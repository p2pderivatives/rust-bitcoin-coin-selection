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
mod single_random_draw;

use bitcoin::{Amount, FeeRate, SignedAmount, Weight};
use rand::thread_rng;

pub use crate::branch_and_bound::select_coins_bnb;
pub use crate::single_random_draw::select_coins_srd;

pub(crate) type Return<'a, Utxo> = Option<(u32, Vec<&'a Utxo>)>;

// https://github.com/bitcoin/bitcoin/blob/f722a9bd132222d9d5cd503b5af25c905b205cdb/src/wallet/coinselection.h#L20
const CHANGE_LOWER: Amount = Amount::from_sat(50_000);

// https://github.com/rust-bitcoin/rust-bitcoin/blob/35202ba51bef3236e6ed1007a0d2111265b6498c/bitcoin/src/blockdata/transaction.rs#L357
const SEQUENCE_SIZE: u64 = 4;

// https://github.com/rust-bitcoin/rust-bitcoin/blob/35202ba51bef3236e6ed1007a0d2111265b6498c/bitcoin/src/blockdata/transaction.rs#L92
const OUT_POINT_SIZE: u64 = 32 + 4;

// https://github.com/rust-bitcoin/rust-bitcoin/blob/35202ba51bef3236e6ed1007a0d2111265b6498c/bitcoin/src/blockdata/transaction.rs#L249
const BASE_WEIGHT: Weight = Weight::from_vb_unwrap(OUT_POINT_SIZE + SEQUENCE_SIZE);

/// Behavior needed for coin-selection.
pub trait WeightedUtxo {
    /// The weight of the witness data and `scriptSig` which is used to then calculate the fee on
    /// a per `UTXO` basis.
    ///
    /// see also:
    /// <https://github.com/bitcoindevkit/bdk/blob/feafaaca31a0a40afc03ce98591d151c48c74fa2/crates/bdk/src/types.rs#L181>
    fn satisfaction_weight(&self) -> Weight;

    /// The UTXO value.
    fn value(&self) -> Amount;

    /// Computes the value of an output accounting for the cost of spending it.
    ///
    /// The effective value is the value of an output value minus the amount to spend it.  That is, the
    /// effective_value can be calculated as: value - (fee_rate * weight).
    ///
    /// Note: the effective value of a Transaction may increase less than the effective value of
    /// a `TxOut` (UTXO) when adding another `TxOut` to the transaction.  This happens when the new
    /// `TxOut` added causes the output length `VarInt` to increase its encoding length.
    ///
    /// see also:
    /// <https://github.com/rust-bitcoin/rust-bitcoin/blob/59c806996ce18e88394eb4e2c265986c8d3a6620/bitcoin/src/blockdata/transaction.rs>
    fn effective_value(&self, fee_rate: FeeRate) -> Option<SignedAmount> {
        let signed_input_fee = self.calculate_fee(fee_rate)?.to_signed().ok()?;
        self.value().to_signed().ok()?.checked_sub(signed_input_fee)
    }

    /// Computes the fee to spend this `Utxo`.
    ///
    /// The fee is calculated as: fee rate * (satisfaction_weight + the base weight).
    fn calculate_fee(&self, fee_rate: FeeRate) -> Option<Amount> {
        let weight = self.satisfaction_weight().checked_add(BASE_WEIGHT)?;
        fee_rate.checked_mul_by_weight(weight)
    }

    /// Computes how wastefull it is to spend this `Utxo`
    ///
    /// The waste is the difference of the fee to spend this `Utxo` now compared with the expected
    /// fee to spend in the future (long_term_fee_rate).
    fn waste(&self, fee_rate: FeeRate, long_term_fee_rate: FeeRate) -> Option<SignedAmount> {
        let fee: SignedAmount = self.calculate_fee(fee_rate)?.to_signed().ok()?;
        let lt_fee: SignedAmount = self.calculate_fee(long_term_fee_rate)?.to_signed().ok()?;
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
/// * `Some((u32, Vec<WeightedUtxo>))` where `Vec<WeightedUtxo>` is non-empty and where u32 is the
///   iteration count of the prevailing algorithm.  The search result succeeded and a match found.
/// * `None` if un-expected results OR no match found.  A future implementation can add Error types
///   which will differentiate between an unexpected error and no match found.  Currently, a None
///   type occurs when one or more of the following criteria are met:
///     - Iteration limit hit
///     - Overflow when summing the UTXO space
///     - Not enough potential amount to meet the target, etc
///     - Target Amount is zero (no match possible)
///     - UTXO space was searched successfully however no match was found
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins<Utxo: WeightedUtxo>(
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    weighted_utxos: &[Utxo],
) -> Return<Utxo> {
    let bnb =
        select_coins_bnb(target, cost_of_change, fee_rate, long_term_fee_rate, weighted_utxos);

    if bnb.is_some() {
        bnb
    } else {
        select_coins_srd(target, fee_rate, weighted_utxos, &mut thread_rng())
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use arbitrary::{Arbitrary, Result, Unstructured};
    use arbtest::arbtest;
    use bitcoin::amount::CheckedSum;
    use bitcoin::transaction::effective_value;
    use bitcoin::{Amount, Weight};

    use super::*;

    const MAX_POOL_SIZE: usize = 20;

    pub fn build_pool() -> Vec<Utxo> {
        let amts = [27_336, 238, 9_225, 20_540, 35_590, 49_463, 6_331, 35_548, 50_363, 28_009];

        let utxos: Vec<_> = amts
            .iter()
            .map(|a| {
                let amt = Amount::from_sat(*a);
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

    // TODO check about adding this to rust-bitcoins from_str for FeeRate
    pub(crate) fn parse_fee_rate(f: &str) -> FeeRate {
        let rate_parts: Vec<_> = f.split(" ").collect();
        let rate = rate_parts[0].parse::<u64>().unwrap();

        match rate_parts.len() {
            1 => {
                assert!(rate == 0, "Try adding sat/kwu or sat/vB to fee_rate");
                FeeRate::ZERO
            }

            2 => match rate_parts[1] {
                "sat/kwu" => FeeRate::from_sat_per_kwu(rate),
                "sat/vb" => FeeRate::from_sat_per_vb(rate).unwrap(),
                "0" => FeeRate::ZERO,
                _ => panic!("only support sat/kwu or sat/vB rates"),
            },

            _ => panic!("number, space then rate not parsed.  example: 10 sat/kwu"),
        }
    }

    #[derive(Debug, Clone, PartialEq, Ord, Eq, PartialOrd, Arbitrary)]
    pub struct Utxo {
        pub value: Amount,
        pub satisfaction_weight: Weight,
    }

    #[derive(Debug, PartialEq, Eq)]
    pub struct ParseUtxoError;

    impl<'a> Arbitrary<'a> for UtxoPool {
        fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
            let len = u.arbitrary_len::<u64>()? % MAX_POOL_SIZE;

            let mut pool: Vec<Utxo> = Vec::with_capacity(len);
            for _ in 0..len {
                let utxo = Utxo::arbitrary(u)?;
                pool.push(utxo);
            }

            Ok(UtxoPool { utxos: pool })
        }
    }

    #[derive(Debug)]
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

                    Utxo::new(abs_val, weight - BASE_WEIGHT)
                })
                .collect();

            UtxoPool { utxos }
        }
    }

    impl WeightedUtxo for Utxo {
        fn satisfaction_weight(&self) -> Weight { self.satisfaction_weight }
        fn value(&self) -> Amount { self.value }
    }

    impl Utxo {
        pub fn new(value: Amount, satisfaction_weight: Weight) -> Utxo {
            Utxo { value, satisfaction_weight }
        }
    }

    // TODO add to RB along side effective_value maybe
    pub fn compute_absolute_value(
        effective_value: SignedAmount,
        weight: Weight,
        fee_rate: FeeRate,
    ) -> Amount {
        let signed_fee = fee_rate.fee_wu(weight).unwrap().to_signed().unwrap();
        let signed_absolute_value = effective_value + signed_fee;
        signed_absolute_value.to_unsigned().unwrap()
    }

    pub fn build_possible_solutions_srd<'a>(
        pool: &'a UtxoPool,
        fee_rate: FeeRate,
        target: Amount,
        solutions: &mut Vec<Vec<&'a Utxo>>,
    ) {
        let mut gen = exhaustigen::Gen::new();
        while !gen.done() {
            let subset = gen.gen_subset(&pool.utxos).collect::<Vec<_>>();
            let effective_values_sum = subset
                .iter()
                .filter_map(|u| effective_value(fee_rate, u.satisfaction_weight(), u.value()))
                .checked_sum();

            if let Some(s) = effective_values_sum {
                if let Ok(p) = s.to_unsigned() {
                    if p >= target {
                        solutions.push(subset)
                    }
                }
            }
        }
    }

    pub fn build_possible_solutions_bnb<'a>(
        pool: &'a UtxoPool,
        fee_rate: FeeRate,
        target: Amount,
        cost_of_change: Amount,
        solutions: &mut Vec<Vec<&'a Utxo>>,
    ) {
        let mut gen = exhaustigen::Gen::new();
        while !gen.done() {
            let subset = gen.gen_subset(&pool.utxos).collect::<Vec<_>>();
            let effective_values_sum = subset
                .iter()
                .filter_map(|u| effective_value(fee_rate, u.satisfaction_weight(), u.value()))
                .checked_sum();

            if let Some(eff_sum) = effective_values_sum {
                if eff_sum <= SignedAmount::MAX_MONEY {
                    if let Ok(unsigned_sum) = eff_sum.to_unsigned() {
                        if unsigned_sum >= target {
                            if let Some(upper_bound) = target.checked_add(cost_of_change) {
                                if unsigned_sum <= upper_bound {
                                    solutions.push(subset)
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    pub fn assert_proptest_bnb(
        target: Amount,
        cost_of_change: Amount,
        fee_rate: FeeRate,
        pool: UtxoPool,
        result: Return<Utxo>,
    ) {
        let mut bnb_solutions: Vec<Vec<&Utxo>> = Vec::new();
        build_possible_solutions_bnb(&pool, fee_rate, target, cost_of_change, &mut bnb_solutions);

        if let Some((_i, utxos)) = result {
            let utxo_sum: Amount = utxos
                .into_iter()
                .map(|u| {
                    effective_value(fee_rate, u.satisfaction_weight(), u.value())
                        .unwrap()
                        .to_unsigned()
                        .unwrap()
                })
                .sum();

            assert!(utxo_sum >= target);
            assert!(utxo_sum <= target + cost_of_change);
        } else {
            assert!(
                target > Amount::MAX_MONEY || target == Amount::ZERO || bnb_solutions.is_empty()
            );
        }
    }

    pub fn assert_proptest_srd(
        target: Amount,
        fee_rate: FeeRate,
        pool: UtxoPool,
        result: Return<Utxo>,
    ) {
        let mut srd_solutions: Vec<Vec<&Utxo>> = Vec::new();
        build_possible_solutions_srd(&pool, fee_rate, target, &mut srd_solutions);

        if let Some((_i, utxos)) = result {
            let utxo_sum: Amount = utxos
                .into_iter()
                .map(|u| {
                    effective_value(fee_rate, u.satisfaction_weight(), u.value())
                        .unwrap()
                        .to_unsigned()
                        .unwrap()
                })
                .sum();

            assert!(utxo_sum >= target);
        } else {
            assert!(
                target > Amount::MAX_MONEY || target == Amount::ZERO || srd_solutions.is_empty()
            );
        }
    }

    pub fn assert_proptest(
        target: Amount,
        cost_of_change: Amount,
        fee_rate: FeeRate,
        pool: UtxoPool,
        result: Return<Utxo>,
    ) {
        let mut bnb_solutions: Vec<Vec<&Utxo>> = Vec::new();
        build_possible_solutions_bnb(&pool, fee_rate, target, cost_of_change, &mut bnb_solutions);

        let mut srd_solutions: Vec<Vec<&Utxo>> = Vec::new();
        build_possible_solutions_srd(&pool, fee_rate, target, &mut srd_solutions);

        if let Some((_i, utxos)) = result {
            let utxo_sum: Amount = utxos
                .into_iter()
                .map(|u| {
                    effective_value(fee_rate, u.satisfaction_weight(), u.value())
                        .unwrap()
                        .to_unsigned()
                        .unwrap()
                })
                .sum();

            assert!(utxo_sum >= target);
        } else {
            assert!(
                target > Amount::MAX_MONEY
                    || target == Amount::ZERO
                    || bnb_solutions.is_empty() && srd_solutions.is_empty()
            );
        }
    }

    #[test]
    fn select_coins_no_solution() {
        let target = Amount::from_sat(255432);
        let cost_of_change = Amount::ZERO;
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;
        let pool = build_pool(); // eff value sum 262643

        let result = select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &pool);

        // This yields no solution because:
        //  * BnB fails because the sum overage is greater than cost_of_change
        //  * SRD fails because the sum is greater the utxo sum + CHANGE_LOWER
        assert!(result.is_none());
    }

    #[test]
    fn select_coins_srd_solution() {
        let target = Amount::from_sat(255432) - CHANGE_LOWER;
        let cost_of_change = Amount::ZERO;
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;
        let pool = build_pool();

        let result = select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &pool);
        let (_iterations, utxos) = result.unwrap();
        let sum: Amount = utxos.into_iter().map(|u| u.value()).sum();
        assert!(sum > target);
    }

    #[test]
    fn select_coins_bnb_solution() {
        let target = Amount::from_sat(255432);
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;
        let pool = build_pool();

        // set cost_of_change to be the differene
        // between the total pool sum and the target amount
        // plus 1.  This creates an upper bound that the sum
        // of all utxos will fall bellow resulting in a BnB match.
        let cost_of_change = Amount::from_sat(7211);

        let result = select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &pool);
        let (iterations, utxos) = result.unwrap();
        let sum: Amount = utxos.into_iter().map(|u| u.value()).sum();
        assert!(sum > target);
        assert!(sum <= target + cost_of_change);
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

            assert_proptest(target, cost_of_change, fee_rate, pool, result);

            Ok(())
        });
    }
}
