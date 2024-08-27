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
