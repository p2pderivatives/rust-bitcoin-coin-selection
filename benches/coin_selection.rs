//! Benchmark select_coins() function
//!
//! Generate a pool of 400 UTXOs with varying amounts and types.  This implementation is largely a
//! duplicate of bitcoin-core so as to accurately compare performance between implementations:
//!
//! https://github.com/bitcoin/bitcoin/blob/59224b66aa1db43adc61c15ee41b413951f22f80/src/bench/coin_selection.cpp#L50

use bitcoin_coin_selection::{select_coins, Spendable};
use bitcoin_units::{Amount, FeeRate, SignedAmount, Weight};
use criterion::{criterion_group, criterion_main, Criterion};
use rand::Rng;

const MAX_STANDARD_TX_WEIGHT: Weight = Weight::from_wu(400_000);

#[derive(Clone)]
struct Utxo {
    value: Amount,
    weight: Weight,
}

impl Spendable for Utxo {
    fn total_weight(&self) -> Weight {
        self.weight
    }

    fn value(&self) -> Amount {
        self.value
    }
}

fn effective_sum(utxos: &[&Utxo], fee_rate: FeeRate) -> Amount {
    utxos
        .iter()
        .filter_map(|u| effective_value(fee_rate, u.weight, u.value))
        .filter_map(|u| u.to_unsigned().ok())
        // TODO units 1.0 has .sum() instead of using fold().
        .fold(Amount::ZERO, |acc, x| (acc + x).unwrap())
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

pub fn coin_selection_benchmark(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let mut coins = vec![];
    let mut amount: Amount;
    for _i in 0..400 {
        let p = rng.gen_range(0..=100);
        if p < 50 {
            let range = rng.gen_range(0..=90_000);
            amount = Amount::from_sat_u32(10_000 + range);
        } else if p < 75 {
            let range = rng.gen_range(0..=900_000);
            amount = Amount::from_sat_u32(100_000 + range);
        } else if p < 95 {
            let range = rng.gen_range(0..=9_000_000);
            amount = Amount::from_sat_u32(1_000_000 + range);
        } else {
            let range = rng.gen_range(0..=90_000_000);
            amount = Amount::from_sat_u32(10_000_000 + range);
        }

        let u = Utxo { value: amount, weight: Weight::ZERO };

        coins.push(u);
    }

    let weighted_coins: Vec<_> = coins
        .iter()
        .map(|c| {
            let y = rng.gen_range(0..=100);
            let weight = if y < 35 {
                Weight::from_vb_unchecked(148) // P2PKH
            } else if y < 55 {
                Weight::from_vb_unchecked(91) // P2SH-P2WPKH
            } else if y < 90 {
                Weight::from_vb_unchecked(68) // P2WPKH
            } else {
                Weight::from_vb_unchecked(58) // P2TR
            };

            Utxo { value: c.value, weight }
        })
        .collect();

    let mut targets = vec![];
    for _t in 0..10 {
        let range = rng.gen_range(0..=90_000_000);
        let target = Amount::from_sat_u32(10_000_000 + range);
        targets.push(target);
    }

    c.bench_function("coin_selection", |b| {
        b.iter(|| {
            let change_output_size = Weight::from_vb_unchecked(31);
            let change_spend_size = Weight::from_vb_unchecked(68);
            let fee_rate = FeeRate::from_sat_per_vb(20);
            let lt_fee_rate = FeeRate::from_sat_per_vb(10);
            let discard_fee_rate = FeeRate::from_sat_per_vb(3);

            let change_fee = fee_rate.to_fee(change_output_size);
            let min_viable_change = discard_fee_rate.to_fee(change_spend_size);
            let cost_of_change = (min_viable_change + change_fee).unwrap();
            for target in &targets {
                let (_, inputs) = select_coins(
                    *target,
                    cost_of_change,
                    MAX_STANDARD_TX_WEIGHT,
                    fee_rate,
                    lt_fee_rate,
                    &weighted_coins,
                )
                .unwrap();
                let sum = effective_sum(&inputs, fee_rate);
                assert!(sum >= *target);
            }
        })
    });
}

criterion_group!(benches, coin_selection_benchmark);
criterion_main!(benches);
