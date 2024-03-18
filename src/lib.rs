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
use bitcoin::SignedAmount;
use bitcoin::TxOut;
use bitcoin::Weight;

pub use crate::branch_and_bound::select_coins_bnb;
use crate::single_random_draw::select_coins_srd;
use bitcoin::blockdata::transaction::TxIn;
use rand::thread_rng;

/// Trait that a UTXO struct must implement to be used as part of the coin selection
/// algorithm.
pub trait Utxo: Clone {
    /// Return the value of the UTXO.
    fn get_value(&self) -> u64;
}

// https://github.com/bitcoin/bitcoin/blob/f722a9bd132222d9d5cd503b5af25c905b205cdb/src/wallet/coinselection.h#L20
const CHANGE_LOWER: Amount = Amount::from_sat(50_000);

fn calculate_effective_value(
    fee_rate: FeeRate,
    value: Amount,
    satisfaction_weight: Weight,
) -> Option<SignedAmount> {
    let signed_input_fee = calculate_fee(fee_rate, satisfaction_weight)?.to_signed().ok()?;
    value.to_signed().ok()?.checked_sub(signed_input_fee)
}

fn calculate_fee(fee_rate: FeeRate, satisfaction_weight: Weight) -> Option<Amount> {
    let weight = satisfaction_weight.checked_add(TxIn::BASE_WEIGHT)?;
    fee_rate.checked_mul_by_weight(weight)
}

fn calculate_waste(
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    satisfaction_weight: Weight,
) -> Option<SignedAmount> {
    let fee: SignedAmount = calculate_fee(fee_rate, satisfaction_weight)?.to_signed().ok()?;
    let lt_fee: SignedAmount =
        calculate_fee(long_term_fee_rate, satisfaction_weight)?.to_signed().ok()?;
    fee.checked_sub(lt_fee)
}

/// TODO
#[derive(Clone, Debug)]
pub struct Coin {
    /// TODO
    pub utxo: TxOut,
    /// TODO
    pub effective_value: Amount,
    /// TODO
    pub waste: SignedAmount,
    /// TODO
    pub fee_rate: FeeRate,
    /// TODO
    pub long_term_fee_rate: FeeRate,
}

/// TODO
impl Coin {
    /// TODO
    pub fn new(
        utxo: TxOut,
        fee_rate: FeeRate,
        long_term_fee_rate: FeeRate,
        satisfaction_weight: Weight,
    ) -> Option<Self> {
        let effective_value = calculate_effective_value(fee_rate, utxo.value, satisfaction_weight)?
            .to_unsigned()
            .ok()?;
        let waste = calculate_waste(fee_rate, long_term_fee_rate, satisfaction_weight)?;
        Some(Self { utxo, effective_value, waste, fee_rate, long_term_fee_rate })
    }
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
    coins: &[Coin],
) -> Option<impl Iterator<Item = &Coin>> {
    {
        let bnb = select_coins_bnb(target, cost_of_change, coins);

        if bnb.is_some() {
            bnb
        } else {
            select_coins_srd(target, coins, &mut thread_rng())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::ScriptBuf;
    use core::str::FromStr;

    #[test]
    fn coin_constructor_negative_effective_value() {
        let tx_out =
            TxOut { value: Amount::from_str("1 sat").unwrap(), script_pubkey: ScriptBuf::new() };

        let fee_rate: FeeRate = FeeRate::from_sat_per_kwu(10);
        let coin = Coin::new(tx_out, fee_rate, FeeRate::ZERO, Weight::ZERO);
        assert!(coin.is_none());
    }

    #[test]
    fn coin_constructor_typical() {
        let tx_out =
            TxOut { value: Amount::from_str("46 sats").unwrap(), script_pubkey: ScriptBuf::new() };

        let fee_rate: FeeRate = FeeRate::from_sat_per_kwu(10);
        let lt_fee_rate: FeeRate = FeeRate::from_sat_per_kwu(15);
        let satisfaction_weight = Weight::from_wu(204);

        let coin = Coin::new(tx_out.clone(), fee_rate, lt_fee_rate, satisfaction_weight).unwrap();

        // effective_vale = value - fee
        // fee = satisfaction_weight + base_weight * fee_rate
        //
        // effective_value = 46 sats - (204 wu + 160 wu) * 10 sat/kwu = 42 sats
        assert_eq!(coin.effective_value, Amount::from_str("42 sats").unwrap());

        // waste = fee - long term fee
        // waste = (fee_rate * weight) - (lt_fee_fee_rate * weight)
        //       = (10 sat/kwu * (204 wu + 160 wu)) - (15 sat/kwu * (204 wu + 160 wu))
        // waste = -2 sats
        assert_eq!(coin.waste, SignedAmount::from_str("-2 sats").unwrap());

        assert_eq!(coin.utxo, tx_out);
    }

    #[test]
    fn coin_constructor_overflow() {
        let tx_out =
            TxOut { value: Amount::from_str("1 cBTC").unwrap(), script_pubkey: ScriptBuf::new() };

        let coin = Coin::new(tx_out.clone(), FeeRate::MAX, FeeRate::ZERO, Weight::ZERO);
        assert!(coin.is_none());

        let coin = Coin::new(tx_out.clone(), FeeRate::ZERO, FeeRate::ZERO, Weight::MAX);
        assert!(coin.is_none());

        let coin = Coin::new(tx_out, FeeRate::ZERO, FeeRate::MAX, Weight::ZERO);
        assert!(coin.is_none());
    }
}
