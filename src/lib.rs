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
mod coin_grinder;
mod single_random_draw;

mod weighted_utxo;

pub use crate::weighted_utxo::WeightedUtxo;

/// Possible returned error types if no match is found.
pub mod errors;

use bitcoin_units::{Amount, FeeRate, SignedAmount, Weight};
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
use rand::thread_rng;

pub use crate::branch_and_bound::branch_and_bound;
pub use crate::coin_grinder::coin_grinder;
use crate::errors::{OverflowError, SelectionError};
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub use crate::single_random_draw::single_random_draw;

pub(crate) type Return<'a> = Result<(u32, Vec<&'a WeightedUtxo>), SelectionError>;

pub(crate) type ReturnAlpha<'a, T> = Result<(u32, Vec<&'a T>), SelectionError>;

/// Coin Selection Behavior.
pub trait Spendable {
    /// The estimated UTXO weight.
    fn weight(&self) -> Weight;

    /// The value of the UTXO.
    fn value(&self) -> Amount;
}

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
    let signed_input_fee: SignedAmount = fee_rate.to_fee(weight).to_signed();
    let eff_value = (value.to_signed() - signed_input_fee).unwrap();
    Some(eff_value)
}

/// Attempt a match with [`branch_and_bound`] falling back to [`single_random_draw`].
///
/// If [`branch_and_bound`] fails to find a changeless solution (basically, an exact match), then
/// run [`single_random_draw`] and attempt a random selection.  This solution is also employed by
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
/// A tuple `(u32, Vec<&'a WeightedUtxo>` is returned on success where `u32` is the number of
/// iterations to find the solution and `Vec<&'a WeightedUtxo>` is the best found selection.
/// Note that if the iteration count equals `ITERATION_LIMIT`, a better solution may exist than the
/// one found.
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins<T: Spendable>(
    target: Amount,
    cost_of_change: Amount,
    max_weight: Weight,
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    spendable_coins: &[T],
) -> Result<(u32, Vec<&T>), SelectionError> {
    let bnb_result = branch_and_bound(
        target,
        cost_of_change,
        max_weight,
        fee_rate,
        long_term_fee_rate,
        spendable_coins,
    );

    if bnb_result.is_err() {
        single_random_draw(target, max_weight, fee_rate, &mut thread_rng(), spendable_coins)
    } else {
        bnb_result
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use arbitrary::Arbitrary;
    use arbtest::arbtest;
    use bitcoin_units::{Amount, NumOpResult, Weight};

    use super::*;
    use crate::SelectionError::{InsufficentFunds, Overflow, ProgramError};

    #[derive(Clone, Debug, Eq, PartialEq)]
    pub struct Utxo {
        pub value: Amount,
        pub weight: Weight,
    }

    impl Spendable for Utxo {
        fn weight(&self) -> Weight {
            self.weight
        }
        fn value(&self) -> Amount {
            self.value
        }
    }

    pub fn build_pool() -> Vec<Utxo> {
        let amts = [27_336, 238, 9_225, 20_540, 35_590, 49_463, 6_331, 35_548, 50_363, 28_009];
        let weight = Weight::ZERO;

        let utxos: Vec<_> =
            amts.iter().map(|a| Utxo { value: Amount::from_sat_u32(*a), weight }).collect();

        utxos
    }

    pub fn assert_ref_eq(inputs: Vec<&Utxo>, expected: Vec<Utxo>) {
        let expected_ref: Vec<&Utxo> = expected.iter().collect();
        assert_eq!(inputs, expected_ref);
    }

    pub fn effective_sum(utxos: &[Utxo], fee_rate: FeeRate) -> Option<Amount> {
        utxos
            .iter()
            .filter_map(|u| effective_value(fee_rate, u.weight, u.value))
            .filter_map(|u| u.to_unsigned().ok())
            .try_fold(Amount::ZERO, Amount::checked_add)
    }

    pub fn weight_sum(utxos: &[Utxo]) -> Option<Weight> {
        utxos.iter().map(|u| u.weight()).try_fold(Weight::ZERO, Weight::checked_add)
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

    pub fn utxos_from_str(
        utxos: &[&str],
        fee_rate: FeeRate,
        long_term_fee_rate: FeeRate,
    ) -> Vec<Utxo> {
        utxos
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

                Utxo { value: abs_val, weight }
            })
            .collect()
    }

    pub fn compute_absolute_value(
        effective_value: SignedAmount,
        weight: Weight,
        fee_rate: FeeRate,
    ) -> Amount {
        let signed_fee = fee_rate.to_fee(weight).to_signed();
        let signed_absolute_value = (effective_value + signed_fee).unwrap();
        signed_absolute_value.to_unsigned().unwrap()
    }

    #[test]
    fn select_coins_empty_set() {
        let target = Amount::ZERO;
        let cost_of_change = Amount::ZERO;
        let max_weight = Weight::from_wu(40_000);

        let empty: Vec<Utxo> = vec![];
        let result =
            select_coins(target, cost_of_change, max_weight, FeeRate::ZERO, FeeRate::ZERO, &empty);

        match result {
            Err(crate::SelectionError::SolutionNotFound) => {}
            _ => panic!("un-expected result: {:?}", result),
        }
    }

    #[test]
    fn select_coins_no_solution() {
        // Test the code branch where both SRD and BnB fail.
        let target = Amount::from_sat_u32(262644);
        let cost_of_change = Amount::ZERO;
        let max_weight = Weight::from_wu(40_000);
        let pool = build_pool(); // eff value sum 262643

        let result =
            select_coins(target, cost_of_change, max_weight, FeeRate::ZERO, FeeRate::ZERO, &pool);

        match result {
            Err(crate::SelectionError::InsufficentFunds) => {}
            _ => panic!("un-expected result: {:?}", result),
        }
    }

    #[test]
    fn select_coins_bnb_solution() {
        let target = Amount::from_sat_u32(255432);
        let max_weight = Weight::from_wu(40_000);
        let pool = build_pool();

        // set cost_of_change to be the difference
        // between the total pool sum and the target amount
        // plus 1.  This creates an upper bound that the sum
        // of all utxos will fall bellow resulting in a BnB match.
        let cost_of_change = Amount::from_sat_u32(7211);

        let result =
            select_coins(target, cost_of_change, max_weight, FeeRate::ZERO, FeeRate::ZERO, &pool);
        let (iterations, utxos) = result.unwrap();
        let sum: Amount = utxos
            .into_iter()
            .map(|u| u.value())
            .try_fold(Amount::ZERO, Amount::checked_add)
            .unwrap();
        assert!(sum > target);
        assert!(sum <= (target + cost_of_change).unwrap());
        assert_eq!(16, iterations);
    }

    #[test]
    fn select_coins_srd_solution() {
        let fee_rate = FeeRate::from_sat_per_vb(10);
        let target = Amount::from_sat_u32(50_000);
        let utxo_amt = Amount::from_sat_u32(100_000);
        let weight = Weight::from_wu(230); // TR output size
        let w_utxo = Utxo { value: utxo_amt, weight };

        let utxo_pool = vec![w_utxo];
        let cost_of_change = Amount::from_sat_u32(678);

        let (iterations, utxos) = select_coins(
            target,
            cost_of_change,
            Weight::MAX,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &utxo_pool,
        )
        .unwrap();

        let sum: Amount = utxos
            .into_iter()
            .map(|u| u.value())
            .map(NumOpResult::from)
            .sum::<NumOpResult<Amount>>()
            .unwrap();

        assert!(sum > target);
        assert_eq!(1, iterations);
    }

    #[test]
    fn select_coins_proptest() {
        arbtest(|u| {
            let init: Vec<(Amount, Weight)> = Vec::arbitrary(u)?;
            let fee_rate = FeeRate::arbitrary(u)?;
            let long_term_fee_rate = FeeRate::arbitrary(u)?;
            let utxos: Vec<Utxo> = init.iter().map(|i| Utxo { value: i.0, weight: i.1 }).collect();

            let target = Amount::arbitrary(u)?;
            let cost_of_change = Amount::arbitrary(u)?;
            let max_weight = Weight::arbitrary(u)?;

            let result = select_coins(
                target,
                cost_of_change,
                max_weight,
                fee_rate,
                long_term_fee_rate,
                &utxos,
            );

            match result {
                Ok((i, utxos)) => {
                    let u: Vec<Utxo> = utxos.into_iter().cloned().collect();
                    assert!(i > 0);
                    assert!(effective_sum(&u, fee_rate).unwrap() >= target);
                }
                Err(InsufficentFunds) => {
                    assert!(
                        effective_sum(&utxos, fee_rate).unwrap() < target
                            || effective_sum(&utxos, fee_rate).unwrap() == Amount::ZERO
                    );
                }
                Err(Overflow(_)) => {
                    assert!(
                        effective_sum(&utxos, fee_rate).is_none() || weight_sum(&utxos).is_none()
                    );
                }
                Err(ProgramError) => panic!("un-expected program error"),
                _ => {}
            }

            Ok(())
        });
    }
}
