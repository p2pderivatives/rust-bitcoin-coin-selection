use bitcoin_coin_selection::{select_coins_bnb, WeightedUtxo};
use bitcoin_units::{Amount, FeeRate, Weight};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

#[derive(Debug, Clone)]
pub struct Utxo {
    value: Amount,
    weight: Weight,
}

impl WeightedUtxo for Utxo {
    fn weight(&self) -> Weight { self.weight }
    fn value(&self) -> Amount { self.value }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.h#L18
    let cost_of_change = Amount::from_sat_u32(50_000);

    let one = Utxo { value: Amount::from_sat_u32(1_000), weight: Weight::ZERO };

    let two = Utxo { value: Amount::from_sat_u32(3), weight: Weight::ZERO };

    let target = Amount::from_sat_u32(1_003);
    let mut utxo_pool = vec![one; 1000];
    utxo_pool.push(two);

    c.bench_function("bnb 1000", |b| {
        b.iter(|| {
            let (iteration_count, inputs) = select_coins_bnb(
                black_box(target),
                black_box(cost_of_change),
                black_box(FeeRate::ZERO),
                black_box(FeeRate::ZERO),
                black_box(&utxo_pool),
            )
            .unwrap();
            assert_eq!(iteration_count, 100000);

            assert_eq!(2, inputs.len());
            assert_eq!(Amount::from_sat_u32(1_000), inputs[0].value());
            assert_eq!(Amount::from_sat_u32(3), inputs[1].value());
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
