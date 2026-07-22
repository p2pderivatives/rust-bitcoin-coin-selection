use bitcoin_coin_selection::{single_random_draw, Spendable};
use bitcoin_units::{Amount, FeeRate, Weight};
use criterion::{criterion_group, criterion_main, Criterion};
use rand::thread_rng;

#[derive(Clone, Debug, Eq, PartialEq)]
struct Utxo {
    value: Amount,
    weight: Weight
}

impl Spendable for Utxo {
    fn weight(&self) -> Weight {
        self.weight
    }
    fn value(&self) -> Amount {
        self.value
    }
}

pub fn srd_benchmark(c: &mut Criterion) {
    let fee_rate = FeeRate::from_sat_per_kwu(10);
    let lt_fee_rate = FeeRate::MAX;

    let utxo = Utxo {
        value: Amount::from_sat_u32(1_00),
        weight: Weight::ZERO
    };
    let utxos = vec![utxo; 1_000];

    let target = Amount::from_sat_u32(100_000);
    let max_weight = Weight::MAX;

    c.bench_function("srd", |b| {
        b.iter(|| {
            let (iteration_count, inputs) =
                single_random_draw(target, max_weight, fee_rate, &mut thread_rng(), &utxos).unwrap();
            assert_eq!(iteration_count, 1_000);
            assert_eq!(inputs.len(), 1_000);
        })
    });
}

criterion_group!(benches, srd_benchmark);
criterion_main!(benches);
