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
#![cfg_attr(bench, feature(test))]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(bench)]
extern crate test;

#[cfg(any(test, feature = "rand"))]
mod single_random_draw;

#[cfg(any(test, feature = "rand"))]
mod errors;

#[cfg(any(test, feature = "rand"))]
use rand::thread_rng;

#[cfg(any(test, feature = "rand"))]
pub use crate::single_random_draw::select_coins_srd;

#[cfg(any(test, feature = "rand"))]
use crate::errors::LibError;

// https://github.com/bitcoin/bitcoin/blob/f722a9bd132222d9d5cd503b5af25c905b205cdb/src/wallet/coinselection.h#L20
#[cfg(any(test, feature = "rand"))]
const CHANGE_LOWER: Amount = Amount::from_sat(50_000);

#[cfg(any(test, feature = "rand"))]
use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::TxOut;

/// Select coins first using BnB algorithm similar to what is done in bitcoin
/// core see: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>,
/// and falls back on a random UTXO selection. Returns none if the target cannot
/// be reached with the given utxo pool.
/// Requires compilation with the "rand" feature.
#[cfg(any(test, feature = "rand"))]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins(
    target: Amount,
    _cost_of_change: u64,
    fee_rate: FeeRate,
    outputs: &mut Vec<TxOut>,
) -> Result<Option<Vec<TxOut>>, LibError> {
    match select_coins_bnb() {
        Some(_res) => Ok(None),
        None => select_coins_srd(target, outputs, fee_rate, &mut thread_rng()),
    }
}

/// Select coins using BnB algorithm similar to what is done in bitcoin
/// core see: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>
/// Returns None if BnB doesn't find a solution.
pub fn select_coins_bnb() -> Option<Vec<TxOut>> {
    None
}

#[cfg(test)]
mod tests {}

#[cfg(bench)]
mod benches {}
