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

use bitcoin_units::{Amount, FeeRate, SignedAmount, Weight};
use rand::thread_rng;

pub use crate::branch_and_bound::select_coins_bnb;
use crate::errors::{OverflowError, SelectionError};
pub use crate::single_random_draw::select_coins_srd;

pub(crate) type Return<'a, Utxo> = Result<(u32, Vec<&'a Utxo>), SelectionError>;

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
/// * `weight` - utxo spending conditions weight.
pub(crate) fn effective_value(
    fee_rate: FeeRate,
    weight: Weight,
    value: Amount,
) -> Option<SignedAmount> {
    let signed_input_fee: SignedAmount = fee_rate.fee_wu(weight)?.to_signed();
    value.to_signed().checked_sub(signed_input_fee)
}

/// Behavior needed for coin-selection.
pub trait WeightedUtxo {
    /// Total UTXO weight.
    fn weight(&self) -> Weight;

    /// The UTXO value.
    fn value(&self) -> Amount;

    /// Computes the effective_value.
    ///
    /// The effective value is calculated as: fee rate * (satisfaction_weight + the base weight).
    fn effective_value(&self, fee_rate: FeeRate) -> Option<SignedAmount> {
        effective_value(fee_rate, self.weight(), self.value())
    }

    /// Computes how wastefull it is to spend this `Utxo`
    ///
    /// The waste is the difference of the fee to spend this `Utxo` now compared with the expected
    /// fee to spend in the future (long_term_fee_rate).
    fn waste(&self, fee_rate: FeeRate, long_term_fee_rate: FeeRate) -> Option<SignedAmount> {
        let fee: SignedAmount = fee_rate.fee_wu(self.weight())?.to_signed();
        let lt_fee: SignedAmount = long_term_fee_rate.fee_wu(self.weight())?.to_signed();
        fee.checked_sub(lt_fee)
    }
}

/// Attempt a match with [`select_coins_bnb`] falling back to [`select_coins_srd`].
///
/// If [`select_coins_bnb`] fails to find a changeless solution (basically, an exact match), then
/// run [`select_coins_srd`] and attempt a random selection.  This solution is also employed by
/// the Bitcoin Core wallet written in C++.  Therefore, this implementation attempts to return the
/// same results as one would find if running the Core wallet.
///
/// # Parameters
///
/// * target: Target spend `Amount`.
/// * cost_of_change: The `Amount` needed to produce a change output.
/// * fee_rate:  Needed to calculate the effective_value of an output.
/// * long_term_fee_rate: Needed to estimate the future effective_value of an output.
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
pub fn select_coins<Utxo: WeightedUtxo>(
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    weighted_utxos: &[Utxo],
) -> Return<'_, Utxo> {
    let bnb_result =
        select_coins_bnb(target, cost_of_change, fee_rate, long_term_fee_rate, weighted_utxos);

    if bnb_result.is_err() {
        select_coins_srd(target, fee_rate, weighted_utxos, &mut thread_rng())
    } else {
        bnb_result
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use arbitrary::Arbitrary;
    use arbtest::arbtest;
    use bitcoin_units::{Amount, CheckedSum, Weight};

    use super::*;
    use crate::SelectionError::{InsufficentFunds, Overflow, ProgramError};

    pub fn build_pool() -> Vec<Utxo> {
        let amts = [27_336, 238, 9_225, 20_540, 35_590, 49_463, 6_331, 35_548, 50_363, 28_009];

        let utxos: Vec<_> = amts
            .iter()
            .map(|a| {
                let amt = Amount::from_sat_u32(*a);
                let weight = Weight::ZERO;
                Utxo::new(amt, weight)
            })
            .collect();

        utxos
    }

    pub fn assert_ref_eq(inputs: Vec<&Utxo>, expected: Vec<Utxo>) {
        let expected_ref: Vec<&Utxo> = expected.iter().collect();
        assert_eq!(inputs, expected_ref);
    }

    pub fn assert_target_selection(
        utxos: &Vec<&Utxo>,
        fee_rate: FeeRate,
        target: Amount,
        upper_bound: Option<Amount>,
    ) {
        let utxos: Vec<Utxo> = utxos.iter().map(|&u| u.clone()).collect();
        let eff_value_sum =
            UtxoPool::effective_value_sum(&utxos, fee_rate).unwrap().to_unsigned().unwrap();
        assert!(eff_value_sum >= target);

        if let Some(ub) = upper_bound {
            assert!(eff_value_sum <= ub);
        }
    }

    // TODO check about adding this to rust-bitcoins from_str for FeeRate
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

    #[derive(Debug, Clone, PartialEq, Ord, Eq, PartialOrd, Arbitrary)]
    pub struct Utxo {
        pub value: Amount,
        pub weight: Weight,
    }

    #[derive(Debug, Arbitrary)]
    pub struct UtxoPool {
        pub utxos: Vec<Utxo>,
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

    impl UtxoPool {
        pub fn new(utxos: &[&str], fee_rate: FeeRate) -> UtxoPool {
            let utxos: Vec<_> = utxos
                .iter()
                .map(|u| {
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

                    Utxo::new(abs_val, weight)
                })
                .collect();

            UtxoPool { utxos }
        }

        fn effective_value_sum(utxos: &[Utxo], fee_rate: FeeRate) -> Option<SignedAmount> {
            utxos
                .iter()
                .map(|u| u.effective_value(fee_rate).unwrap_or(SignedAmount::ZERO))
                .checked_sum()
        }

        pub fn available_value(&self, fee_rate: FeeRate) -> Option<SignedAmount> {
            Self::effective_value_sum(&self.utxos, fee_rate)
        }
    }

    impl WeightedUtxo for Utxo {
        fn weight(&self) -> Weight { self.weight }
        fn value(&self) -> Amount { self.value }
    }

    impl Utxo {
        pub fn new(value: Amount, weight: Weight) -> Utxo { Utxo { value, weight } }
    }

    // TODO add to RB along side effective_value maybe
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
    fn select_coins_no_solution() {
        // Test the code branch where both SRD and BnB fail.
        let target = Amount::from_sat_u32(255432);
        let cost_of_change = Amount::ZERO;
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;
        let pool = build_pool(); // eff value sum 262643

        let result = select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &pool);

        match result {
            Err(crate::SelectionError::InsufficentFunds) => {}
            _ => panic!("un-expected result: {:?}", result),
        }
    }

    #[test]
    fn select_coins_srd_solution() {
        let target = (Amount::from_sat_u32(255432) - CHANGE_LOWER).unwrap();
        let cost_of_change = Amount::ZERO;
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;
        let pool = build_pool();

        let result = select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &pool);
        let (_iterations, utxos) = result.unwrap();
        let sum: Amount = utxos.into_iter().map(|u| u.value()).checked_sum().unwrap();
        assert!(sum > target);
    }

    #[test]
    fn select_coins_bnb_solution() {
        let target = Amount::from_sat_u32(255432);
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;
        let pool = build_pool();

        // set cost_of_change to be the difference
        // between the total pool sum and the target amount
        // plus 1.  This creates an upper bound that the sum
        // of all utxos will fall bellow resulting in a BnB match.
        let cost_of_change = Amount::from_sat_u32(7211);

        let result = select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &pool);
        let (iterations, utxos) = result.unwrap();
        let sum: Amount = utxos.into_iter().map(|u| u.value()).checked_sum().unwrap();
        assert!(sum > target);
        assert!(sum <= (target + cost_of_change).unwrap());
        assert_eq!(16, iterations);
    }

    #[test]
    fn select_coins_proptest() {
        arbtest(|u| {
            let pool = UtxoPool::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let cost_of_change = Amount::arbitrary(u)?;
            let fee_rate = FeeRate::arbitrary(u)?;
            let lt_fee_rate = FeeRate::arbitrary(u)?;

            let utxos = pool.utxos.clone();
            let result = select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &utxos);

            match result {
                Ok((i, utxos)) => {
                    assert!(i > 0);
                    crate::tests::assert_target_selection(&utxos, fee_rate, target, None);
                }
                Err(InsufficentFunds) => {
                    let available_value = pool.available_value(fee_rate).unwrap();
                    assert!(
                        available_value < (target.to_signed() + CHANGE_LOWER.to_signed()).unwrap()
                    );
                }
                Err(Overflow(_)) => {
                    let available_value = pool.available_value(fee_rate);
                    assert!(
                        available_value.is_none() || target.checked_add(CHANGE_LOWER).is_none()
                    );
                }
                Err(ProgramError) => panic!("un-expected program error"),
                _ => {}
            }

            Ok(())
        });
    }
}
