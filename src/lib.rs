//! Rust Bitcoin coin selection library.
//!
//! This library provides efficient algorithms to compose a set of unspent transaction outputs
//! (UTXOs).

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

/// Select coins first using BnB algorithm similar to what is done in bitcoin
/// core see: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>,
/// and falls back on a random UTXO selection. Returns none if the target cannot
/// be reached with the given utxo pool.
/// Requires compilation with the "rand" feature.
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins<Utxo: WeightedUtxo>(
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    weighted_utxos: &[Utxo],
) -> Option<impl Iterator<Item = &Utxo>> {

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
    use super::*;
    use bitcoin::{Amount, ScriptBuf, TxOut, Weight};
    use bitcoin::amount::CheckedSum;
    use bitcoin::transaction::effective_value;
    use std::iter::zip;

    use arbitrary::{Arbitrary, Result, Unstructured};
    use arbtest::arbtest;

    const PROPTEST_POOL_SIZE: usize = 10;
    const PROPTEST_MAX_SAT_AMOUNT: u64 = u64::MAX;
    const PROPTEST_MIN_SAT_AMOUNT: u64 = 161; //tx_in base_weight + 1

    pub fn build_utxo(amt: Amount, satisfaction_weight: Weight) -> Utxo {
        let output = TxOut { value: amt, script_pubkey: ScriptBuf::new() };
        Utxo { output, satisfaction_weight }
    }

    pub fn build_pool() -> Vec<Utxo> {
        let amts = [
            27336,
            238,
            9225,
            20540,
            35590,
            49463,
            6331,
            35548,
            50363,
            28009,
        ];

        let weights = [
            25350,
            106,
            3311,
            2633,
            21081,
            35260,
            3896,
            6377,
            6851,
            20236
        ];

        let utxos: Vec<_> = zip(amts, weights)
            .map(|(a, w)| {
                let amt = Amount::from_sat(a);
                let weight = Weight::from_wu(w);
                build_utxo(amt, weight)
            }).collect();

        utxos
    }

    #[derive(Debug, Clone, PartialEq, Ord, Eq, PartialOrd, Arbitrary)]
    pub struct Utxo {
        output: TxOut,
        satisfaction_weight: Weight,
    }

    #[derive(Debug, Arbitrary)]
    pub struct UtxoPool {
        pub utxos: Vec<Utxo>,
    }

    impl WeightedUtxo for Utxo {
        fn satisfaction_weight(&self) -> Weight { self.satisfaction_weight }
        fn value(&self) -> Amount { self.output.value }
    }

    #[test]
    fn select_coins_no_solution() {
        let target = Amount::from_sat(255432);
        let cost_of_change = Amount::ZERO;
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;
        let pool = build_pool();

        let result = select_coins(
            target,
            cost_of_change,
            fee_rate,
            lt_fee_rate,
            &pool,
        );

        // This yields no solution because:
        //  * BnB fails because the sum overage is greater than ost_of_change
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

        let result = select_coins(
            target,
            cost_of_change,
            fee_rate,
            lt_fee_rate,
            &pool,
        );

        assert!(result.is_some());
        let result: Amount = result.unwrap().map(|u| u.value()).sum();
        assert!(result > target);
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

        let result = select_coins(
            target,
            cost_of_change,
            fee_rate,
            lt_fee_rate,
            &pool,
        );

        assert!(result.is_some());
        let result: Amount = result.unwrap().map(|u| u.value()).sum();
        assert!(result > target);
        assert!(result <= target + cost_of_change);
    }

    fn build_possible_solutions<'a>(pool: &'a UtxoPool, fee_rate: FeeRate, target: Amount, solutions: &mut Vec<Vec<&'a Utxo>>) {
        let mut gen = exhaustigen::Gen::new();
        while !gen.done() {
            let subset = gen.gen_subset(&pool.utxos).collect::<Vec<_>>();
            let effective_value_sum = subset
                .iter()
                .map(|u| {
                    effective_value(
                        fee_rate,
                        u.satisfaction_weight(),
                        u.value()
                    )})
                .filter(|e| e.is_some())
                .map(|u| u.unwrap())
                .checked_sum();

            if let Some(s) = effective_value_sum {
                if let Ok(p) = s.to_unsigned() {
                    if p >= target {
                        solutions.push(subset)
                    }
                }
            }
        }
    }

    #[test]
    fn select_coins_proptest() {
        arbtest(|u| {
            let pool = UtxoPool::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let cost_of_change = Amount::arbitrary(u)?;
            let fee_rate = FeeRate::arbitrary(u)?;
            let lt_fee_rate = FeeRate::arbitrary(u)?;

            let mut solutions: Vec<Vec<&Utxo>> = Vec::new();
            build_possible_solutions(&pool, fee_rate, target, &mut solutions);

            let result = select_coins(
                target,
                cost_of_change,
                fee_rate,
                lt_fee_rate,
                &pool.utxos,
            );

            println!("target: {:?}", target);
            println!("cost of change {:?}", cost_of_change);
            println!("solutions {:?}", solutions);

            if let Some(r) = result {
                let utxo_sum: Amount = r.map(|u| {
                    effective_value(
                        fee_rate,
                        u.satisfaction_weight(),
                        u.value(),
                    )
                    .unwrap()
                    .to_unsigned()
                    .unwrap()
                }).sum();

                assert!(utxo_sum >= target);
            } else {
                assert!(target > Amount::MAX_MONEY || target == Amount::ZERO || solutions.is_empty());
            }

            Ok(())
        }).seed(0xba3bc81500000032);
    }
}
