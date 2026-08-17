use bitcoin_coin_selection::{branch_and_bound, Spendable};
use bitcoin_units::{Amount, FeeRate, SignedAmount, Weight};
use criterion::{criterion_group, criterion_main, Criterion};
use std::time::Duration;

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

pub fn bnb_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("exhaust");
    group.measurement_time(Duration::from_secs(10));

    // min_viable_change + change_fee for default feerate of 5000 s/kvB.
    let cost_of_change = Amount::from_sat_u32(204 + 155);
    let fee_rate = FeeRate::ZERO;
    let lt_fee_rate = FeeRate::ZERO;
    let weight = Weight::from_wu(230);
    let target = Amount::from_sat_u32(800_000);
    let max_weight = MAX_STANDARD_TX_WEIGHT;

    let mut utxos = vec![];
    for i in 0..19 {
        let u = Utxo { value: Amount::from_sat_u32(100_000 + i), weight };
        utxos.push(u)
    }

    group.bench_function("bnb", |b| {
        b.iter(|| {
            let (iteration_count, inputs) =
                branch_and_bound(target, cost_of_change, max_weight, fee_rate, lt_fee_rate, &utxos)
                    .unwrap();
            assert_eq!(iteration_count, 100_000);
            assert_eq!(inputs.len(), 8);
            let sum = effective_sum(&inputs, fee_rate);
            assert!(sum >= target);
        })
    });
    group.finish();
}

criterion_group!(benches, bnb_benchmark);
criterion_main!(benches);
