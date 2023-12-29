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

mod branch_and_bound;
mod single_random_draw;

use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::TxOut;
use bitcoin::Weight;

use crate::branch_and_bound::select_coins_bnb;
use crate::single_random_draw::select_coins_srd;
use rand::thread_rng;

/// Trait that a UTXO struct must implement to be used as part of the coin selection
/// algorithm.
pub trait Utxo: Clone {
    /// Return the value of the UTXO.
    fn get_value(&self) -> u64;
}

// https://github.com/bitcoin/bitcoin/blob/f722a9bd132222d9d5cd503b5af25c905b205cdb/src/wallet/coinselection.h#L20
const CHANGE_LOWER: Amount = Amount::from_sat(50_000);

/// This struct contains the weight of all params needed to satisfy the UTXO.
///
/// The idea of using a WeightUtxo type was inspired by the BDK implementation:
/// <https://github.com/bitcoindevkit/bdk/blob/feafaaca31a0a40afc03ce98591d151c48c74fa2/crates/bdk/src/types.rs#L181>
#[derive(Clone, Debug, PartialEq)]
// note, change this to private?  No good reason to be public.
pub struct WeightedUtxo {
    /// The satisfaction_weight is the size of the required params to satisfy the UTXO.
    pub satisfaction_weight: Weight,
    /// The corresponding UTXO.
    pub utxo: TxOut,
}

/// Select coins first using BnB algorithm similar to what is done in bitcoin
/// core see: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>,
/// and falls back on a random UTXO selection. Returns none if the target cannot
/// be reached with the given utxo pool.
/// Requires compilation with the "rand" feature.
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins<T: Utxo>(
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    weighted_utxos: &mut [WeightedUtxo],
) -> Option<Vec<WeightedUtxo>> {
    let coins = select_coins_bnb(target, cost_of_change, fee_rate, weighted_utxos);

    if coins.is_none() {
        select_coins_srd(target, fee_rate, weighted_utxos, &mut thread_rng())
    } else {
        coins
    }
}

#[cfg(bench)]
mod benches {
    use crate::select_coins_bnb;
    use crate::Utxo;
    use test::Bencher;

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct MinimalUtxo {
        value: u64,
    }

    impl Utxo for MinimalUtxo {
        fn get_value(&self) -> u64 {
            self.value
        }
    }

    #[bench]
    /// Creates a UTXO pool of 1,000 coins that do not match and one coin
    /// that will be a match when combined with any of the other 1,000 coins.
    ///
    /// Matching benchmark of Bitcoin core coin-selection benchmark.
    // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/bench/coin_selection.cpp#L44
    fn bench_select_coins_bnb(bh: &mut Bencher) {
        // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/consensus/amount.h#L15
        /// The amount of satoshis in one BTC.
        const COIN: u64 = 100_000_000;

        // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.h#L18
        /// lower bound for randomly-chosen target change amount
        const CHANGE_LOWER: u64 = 50_000;

        let u = MinimalUtxo { value: 1000 * COIN };
        let mut utxo_pool = vec![u; 1000];
        utxo_pool.push(MinimalUtxo { value: 3 * COIN });

        bh.iter(|| {
            let result =
                select_coins_bnb(1003 * COIN, CHANGE_LOWER, &mut utxo_pool.clone()).unwrap();
            assert_eq!(2, result.len());
            assert_eq!(1000 * COIN, result[0].value);
            assert_eq!(3 * COIN, result[1].value);
        });
    }
}
