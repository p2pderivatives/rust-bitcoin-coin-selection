//! Rust Bitcoin coin selection library.
//!
//! Efficient algorithms for choosing an optimal UTXO set.

// Coding conventions.
#![deny(non_upper_case_globals)]
#![deny(non_camel_case_types)]
#![deny(non_snake_case)]
#![deny(unused_mut)]
#![deny(missing_docs)]
// Experimental features we need.
#![cfg_attr(docsrs, feature(doc_cfg))]

mod branch_and_bound;
mod errors;
mod single_random_draw;

use std::cmp::Ordering;

use bitcoin_units::{Amount, FeeRate, SignedAmount, Weight};
use rand::thread_rng;

pub use crate::branch_and_bound::select_coins_bnb;
use crate::errors::{OverflowError, SelectionError};
pub use crate::single_random_draw::select_coins_srd;
use crate::OverflowError::Addition;
use crate::SelectionError::Overflow;

pub(crate) type Return<'a> = Result<(u32, Vec<&'a WeightedUtxo>), SelectionError>;

// https://github.com/bitcoin/bitcoin/blob/f722a9bd132222d9d5cd503b5af25c905b205cdb/src/wallet/coinselection.h#L20
const CHANGE_LOWER: Amount = Amount::from_sat_u32(50_000);

/// Computes the value of an output accounting for the cost to spend it.
///
/// The effective_value can be calculated as: value - (fee_rate * weight).
///
/// Note: the effective value of a `Transaction` may increase less than the effective value of
/// a `TxOut` when adding another `TxOut` to the transaction. This happens when the new
/// `TxOut` added causes the output length `VarInt` to increase its encoding length.
///
/// # Parameters
///
/// * `fee_rate` - the fee rate of the transaction being created.
/// * `weight` - the utxo spending conditions weight.
/// * `value` - the utxo value to spend.
pub(crate) fn effective_value(
    fee_rate: FeeRate,
    weight: Weight,
    value: Amount,
) -> Option<SignedAmount> {
    let signed_input_fee: SignedAmount = fee_rate.fee_wu(weight)?.to_signed();
    let eff_value = (value.to_signed() - signed_input_fee).unwrap();
    Some(eff_value)
}

/// Represents a Pool of candidate outputs.
#[derive(Debug, Clone, Copy)]
pub struct UtxoPool<'a> {
    /// The candidate outputs to select.
    utxos: &'a [WeightedUtxo],
    /// The sum of effective_values of all candidate outputs.
    available_value: Amount,
}

impl UtxoPool<'_> {
    /// Creates a new `UtxoPool`.
    pub fn new(utxos: &[WeightedUtxo]) -> Result<UtxoPool<'_>, SelectionError> {
        let available_value = utxos
            .iter()
            .map(|u| u.effective_value())
            .try_fold(Amount::ZERO, Amount::checked_add)
            .ok_or(Overflow(Addition))?;

        let _ = utxos
            .iter()
            .map(|u| u.weight())
            .try_fold(Weight::ZERO, Weight::checked_add)
            .ok_or(Overflow(Addition))?;

        let pool = UtxoPool { utxos, available_value };
        Ok(pool)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// Represents the spendable conditions of a `UTXO`.
pub struct WeightedUtxo {
    /// The `Amount` that the output contributes towards the selection target.
    value: Amount,
    /// The estimated `Weight` (satisfaction weight + base weight) of the output.
    weight: Weight,
    /// The positive effective value `(value - fee)`.  This value is stored as a `u64` for
    /// better performance.
    effective_value: u64,
    /// The `SignedAmount` required to spend the output at the given `fee_rate`.
    fee: SignedAmount,
    /// The `SignedAmount` required to spend the output at the given `long_term_fee_rate`.
    long_term_fee: SignedAmount,
    /// A metric for how wasteful it is to spend this `WeightedUtxo` given the current fee
    /// environment.
    waste: i64,
}

impl WeightedUtxo {
    /// Creates a new `WeightedUtxo`.
    pub fn new(
        value: Amount,
        weight: Weight,
        fee_rate: FeeRate,
        long_term_fee_rate: FeeRate,
    ) -> Option<WeightedUtxo> {
        let positive_effective_value = Self::positive_effective_value(fee_rate, weight, value);

        if let Some(effective_value) = positive_effective_value {
            let fee = fee_rate.fee_wu(weight)?.to_signed();
            let long_term_fee: SignedAmount = long_term_fee_rate.fee_wu(weight)?.to_signed();
            let waste = Self::calculate_waste_score(fee, long_term_fee);
            return Some(Self { value, weight, effective_value, fee, long_term_fee, waste });
        }

        None
    }

    /// Calculates if the current fee environment is expensive.
    pub fn is_fee_expensive(&self) -> bool { self.fee > self.long_term_fee }

    /// Returns the associated value.
    pub fn value(&self) -> Amount { self.value }

    /// Returns the associated weight.
    pub fn weight(&self) -> Weight { self.weight }

    /// Returns the calculated effective value.
    pub fn effective_value(&self) -> Amount { Amount::from_sat(self.effective_value).unwrap() }

    fn positive_effective_value(fee_rate: FeeRate, weight: Weight, value: Amount) -> Option<u64> {
        if let Some(eff_value) = effective_value(fee_rate, weight, value) {
            if let Ok(unsigned) = eff_value.to_unsigned() {
                return Some(unsigned.to_sat());
            }
        }

        None
    }

    fn calculate_waste_score(fee: SignedAmount, long_term_fee: SignedAmount) -> i64 {
        fee.to_sat() - long_term_fee.to_sat()
    }
}

impl Ord for WeightedUtxo {
    fn cmp(&self, other: &Self) -> Ordering {
        other.effective_value.cmp(&self.effective_value).then(self.weight.cmp(&other.weight))
    }
}

impl PartialOrd for WeightedUtxo {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

/// Attempt a match with [`select_coins_bnb`] falling back to [`select_coins_srd`].
///
/// If [`select_coins_bnb`] fails to find a changeless solution (basically, an exact match), then
/// run [`select_coins_srd`] and attempt a random selection.  This solution is also employed by
/// the Bitcoin Core wallet written in C++.  Therefore, this implementation attempts to return the
/// same results as one would find if running the Core wallet.
///
/// If the maximum weight is exceeded, then the least valuable inputs are removed from the current
/// selection using weight as a tie breaker.  In so doing, minimize the number of UTXOs included
/// by preferring more valuable UITXOs in the result.
///
/// # Parameters
///
/// * target: Target spend `Amount`.
/// * cost_of_change: The `Amount` needed to produce a change output.
/// * `max_weight` - the maximum selection weight allowed.
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from.
///
/// # Returns
///
/// The best solution found and the number of iterations to find it.  Note that if the iteration
/// count equals `ITERATION_LIMIT`, a better solution may exist than the one found.
///
/// # Errors
///
/// If an arithmetic overflow occurs, the target can't be reached, or an un-expected error occurs.
/// That is, if sufficient funds are supplied, and an overflow does not occur, then a solution
/// should always be found.  Anything else would be an un-expected program error which ought never
/// happen.
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins(
    target: Amount,
    cost_of_change: Amount,
    max_weight: Weight,
    pool: UtxoPool<'_>,
) -> Return<'_> {
    let bnb_result = select_coins_bnb(target, cost_of_change, max_weight, &pool);

    if bnb_result.is_err() {
        select_coins_srd(target, max_weight, &pool, &mut thread_rng())
    } else {
        bnb_result
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use arbitrary::{Arbitrary, Result, Unstructured};
    use arbtest::arbtest;
    use bitcoin_units::{Amount, CheckedSum, Weight};

    use super::*;
    use crate::SelectionError::{InsufficentFunds, Overflow, ProgramError};

    pub fn build_pool() -> Vec<WeightedUtxo> {
        let amts = [27_336, 238, 9_225, 20_540, 35_590, 49_463, 6_331, 35_548, 50_363, 28_009];
        let weight = Weight::ZERO;
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;

        let utxos: Vec<_> = amts
            .iter()
            .filter_map(|a| {
                let amt = Amount::from_sat_u32(*a);
                WeightedUtxo::new(amt, weight, fee_rate, lt_fee_rate)
            })
            .collect();

        utxos
    }

    pub fn assert_ref_eq(inputs: Vec<&WeightedUtxo>, expected: Vec<WeightedUtxo>) {
        let expected_ref: Vec<&WeightedUtxo> = expected.iter().collect();
        assert_eq!(inputs, expected_ref);
    }

    pub fn assert_target_selection(
        utxos: &Vec<&WeightedUtxo>,
        target: Amount,
        upper_bound: Option<Amount>,
    ) {
        let utxos: Vec<WeightedUtxo> = utxos.iter().map(|&u| u.clone()).collect();
        let eff_value_sum = SelectionCandidate::effective_value_sum(&utxos).unwrap();
        assert!(eff_value_sum >= target);

        if let Some(ub) = upper_bound {
            assert!(eff_value_sum <= ub);
        }
    }

    pub(crate) fn parse_fee_rate(f: &str) -> FeeRate {
        let rate_parts: Vec<_> = f.split(" ").collect();
        let rate = rate_parts[0].parse::<u32>().unwrap();

        match rate_parts.len() {
            1 => {
                assert!(rate == 0, "Try adding sat/kwu or sat/vB to fee_rate");
                FeeRate::ZERO
            }

            2 => match rate_parts[1] {
                "sat/kwu" => FeeRate::from_sat_per_kwu(rate),
                "sat/vB" => FeeRate::from_sat_per_vb(rate),
                "0" => FeeRate::ZERO,
                _ => panic!("only support sat/kwu or sat/vB rates"),
            },

            _ => panic!("number, space then rate not parsed.  example: 10 sat/kwu"),
        }
    }

    #[derive(Debug)]
    pub struct SelectionCandidate {
        pub utxos: Vec<WeightedUtxo>,
        pub fee_rate: FeeRate,
        pub long_term_fee_rate: FeeRate,
    }

    impl<'a> Arbitrary<'a> for SelectionCandidate {
        fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
            let init: Vec<(Amount, Weight)> = Vec::arbitrary(u)?;
            let fee_rate = FeeRate::arbitrary(u)?;
            let long_term_fee_rate = FeeRate::arbitrary(u)?;
            let w_utxos: Vec<WeightedUtxo> = init
                .iter()
                .filter_map(|i| WeightedUtxo::new(i.0, i.1, fee_rate, long_term_fee_rate))
                .collect();

            let utxos: Vec<_> = w_utxos
                .clone()
                .into_iter()
                .scan(0, |state, u| {
                    *state += u.effective_value;
                    // only add utxos to the pool that sum to less than Amount::MAX
                    if Amount::from_sat(*state).is_ok() {
                        Some(*state)
                    } else {
                        None
                    }
                })
                .zip(w_utxos.clone())
                .map(|(_, u)| u)
                .scan(Weight::ZERO, |state, u| {
                    // only add utxos to the pool that sum to less than Weight::MAX
                    if let Some(w) = u.weight().checked_add(*state) {
                        *state = w;
                        Some(*state)
                    } else {
                        None
                    }
                })
                .zip(w_utxos.clone())
                .map(|(_, u)| u)
                .collect();

            Ok(SelectionCandidate { utxos, fee_rate, long_term_fee_rate })
        }
    }

    // TODO check about adding this to rust-bitcoins from_str for Weight
    fn parse_weight(weight: &str) -> Weight {
        let size_parts: Vec<_> = weight.split(" ").collect();
        let size_int = size_parts[0].parse::<u64>().unwrap();
        match size_parts[1] {
            "wu" => Weight::from_wu(size_int),
            "vB" => Weight::from_vb(size_int).unwrap(),
            _ => panic!("only support wu or vB sizes"),
        }
    }

    impl SelectionCandidate {
        pub fn new(
            utxos: &[&str],
            fee_rate: FeeRate,
            long_term_fee_rate: FeeRate,
        ) -> SelectionCandidate {
            let utxos: Vec<_> = utxos
                .iter()
                .filter_map(|u| {
                    let val_with_size: Vec<_> = u.split("/").collect();
                    let weight = parse_weight(val_with_size[1]);
                    let val = val_with_size[0];

                    let abs_val = if val.starts_with("e") {
                        let val = val.replace("e(", "").replace(")", "");
                        let eff_value = SignedAmount::from_str(&val).unwrap();
                        compute_absolute_value(eff_value, weight, fee_rate)
                    } else {
                        Amount::from_str(val).unwrap()
                    };

                    WeightedUtxo::new(abs_val, weight, fee_rate, long_term_fee_rate)
                })
                .collect();

            SelectionCandidate { utxos, fee_rate, long_term_fee_rate }
        }

        fn effective_value_sum(utxos: &[WeightedUtxo]) -> Option<Amount> {
            utxos.iter().map(|u| u.effective_value()).checked_sum()
        }

        pub fn weight_total(&self) -> Option<Weight> {
            self.utxos.iter().map(|u| u.weight()).try_fold(Weight::ZERO, Weight::checked_add)
        }
    }

    pub fn compute_absolute_value(
        effective_value: SignedAmount,
        weight: Weight,
        fee_rate: FeeRate,
    ) -> Amount {
        let signed_fee = fee_rate.fee_wu(weight).unwrap().to_signed();
        let signed_absolute_value = (effective_value + signed_fee).unwrap();
        signed_absolute_value.to_unsigned().unwrap()
    }

    #[test]
    fn weighted_utxo_constructor_overflow() {
        let value = Amount::from_sat_u32(100);
        let weight = Weight::MAX;
        let fee_rate = FeeRate::MAX;
        let long_term_fee_rate = FeeRate::MAX;

        let utxo = WeightedUtxo::new(value, weight, fee_rate, long_term_fee_rate);
        assert!(utxo.is_none());
    }

    #[test]
    fn weighted_utxo_constructor_negative_eff_value() {
        let value = Amount::from_sat_u32(1);
        let weight = Weight::from_vb(68).unwrap();
        let fee_rate = FeeRate::from_sat_per_kwu(20);
        let long_term_fee_rate = FeeRate::from_sat_per_kwu(20);

        let utxo = WeightedUtxo::new(value, weight, fee_rate, long_term_fee_rate);
        assert!(utxo.is_none());
    }

    #[test]
    fn select_coins_no_solution() {
        // Test the code branch where both SRD and BnB fail.
        let target = Amount::from_sat_u32(255432);
        let cost_of_change = Amount::ZERO;
        let max_weight = Weight::from_wu(40_000);
        let pool = build_pool(); // eff value sum 262643
        let utxo_pool = crate::UtxoPool::new(&pool).unwrap();

        let result = select_coins(target, cost_of_change, max_weight, utxo_pool);

        match result {
            Err(crate::SelectionError::InsufficentFunds) => {}
            _ => panic!("un-expected result: {:?}", result),
        }
    }

    #[test]
    fn select_coins_srd_solution() {
        let target = (Amount::from_sat_u32(255432) - CHANGE_LOWER).unwrap();
        let cost_of_change = Amount::ZERO;
        let max_weight = Weight::from_wu(40_000);
        let pool = build_pool();
        let utxo_pool = crate::UtxoPool::new(&pool).unwrap();

        let result = select_coins(target, cost_of_change, max_weight, utxo_pool);
        let (_iterations, utxos) = result.unwrap();
        let sum: Amount = utxos.into_iter().map(|u| u.value()).checked_sum().unwrap();
        assert!(sum > target);
    }

    #[test]
    fn select_coins_bnb_solution() {
        let target = Amount::from_sat_u32(255432);
        let max_weight = Weight::from_wu(40_000);
        let pool = build_pool();
        let utxo_pool = crate::UtxoPool::new(&pool).unwrap();

        // set cost_of_change to be the difference
        // between the total pool sum and the target amount
        // plus 1.  This creates an upper bound that the sum
        // of all utxos will fall bellow resulting in a BnB match.
        let cost_of_change = Amount::from_sat_u32(7211);

        let result = select_coins(target, cost_of_change, max_weight, utxo_pool);
        let (iterations, utxos) = result.unwrap();
        let sum: Amount = utxos.into_iter().map(|u| u.value()).checked_sum().unwrap();
        assert!(sum > target);
        assert!(sum <= (target + cost_of_change).unwrap());
        assert_eq!(16, iterations);
    }

    #[test]
    fn utxo_pool_amount_overflow() {
        // the sum of input effective values cannot exceed Amount::MAX.
        let amt_one = Amount::MAX;
        let amt_two = Amount::from_sat_u32(1);

        let input_one =
            WeightedUtxo::new(amt_one, Weight::ZERO, FeeRate::ZERO, FeeRate::ZERO).unwrap();
        let input_two =
            WeightedUtxo::new(amt_two, Weight::ZERO, FeeRate::ZERO, FeeRate::ZERO).unwrap();
        let inputs = vec![input_one, input_two];
        let pool = crate::UtxoPool::new(&inputs);

        match pool {
            Err(Overflow(Addition)) => {}
            _ => panic!("un-expected result"),
        }
    }

    #[test]
    fn utxo_pool_weight_overflow() {
        // the sum of input weights cannot exceed Weight::MAX.
        let amt = Amount::from_sat_u32(1000);

        let weight_one = Weight::MAX;
        let weight_two = Weight::from_wu(1);

        let input_one = WeightedUtxo::new(amt, weight_one, FeeRate::ZERO, FeeRate::ZERO).unwrap();
        let input_two = WeightedUtxo::new(amt, weight_two, FeeRate::ZERO, FeeRate::ZERO).unwrap();
        let inputs = vec![input_one, input_two];
        let pool = crate::UtxoPool::new(&inputs);

        match pool {
            Err(Overflow(Addition)) => {}
            _ => panic!("un-expected result"),
        }
    }

    #[test]
    fn select_coins_proptest() {
        arbtest(|u| {
            let candidate = SelectionCandidate::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let cost_of_change = Amount::arbitrary(u)?;
            let max_weight = Weight::arbitrary(u)?;

            let utxos = candidate.utxos.clone();
            let utxo_pool = crate::UtxoPool::new(&utxos).unwrap();
            let result = select_coins(target, cost_of_change, max_weight, utxo_pool);

            match result {
                Ok((i, utxos)) => {
                    assert!(i > 0);
                    crate::tests::assert_target_selection(&utxos, target, None);
                }
                Err(InsufficentFunds) => {
                    let available_value = utxo_pool.available_value.clone();
                    assert!(available_value < (target + CHANGE_LOWER).unwrap());
                }
                Err(Overflow(_)) => {
                    assert!(target.checked_add(CHANGE_LOWER).is_none());
                }
                Err(ProgramError) => panic!("un-expected program error"),
                _ => {}
            }

            Ok(())
        });
    }
}
