use bitcoin_coin_selection::{select_coins_bnb, WeightedUtxo};
use bitcoin_units::{Amount, FeeRate, Weight};
use criterion::{criterion_group, criterion_main, Criterion};

pub fn bnb_benchmark(c: &mut Criterion) {
    // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.h#L18
    let cost_of_change = Amount::from_sat_u32(50_000);
    let fee_rate = FeeRate::ZERO;
    let lt_fee_rate = FeeRate::ZERO;
    let weight = Weight::ZERO;

    let one =
        WeightedUtxo::new(Amount::from_sat_u32(1_000), weight, fee_rate, lt_fee_rate).unwrap();

    let two = WeightedUtxo::new(Amount::from_sat_u32(3), weight, fee_rate, lt_fee_rate).unwrap();

    let target = Amount::from_sat_u32(1_003);
    let max_weight = Weight::MAX;
    let mut utxos = vec![one; 1000];
    utxos.push(two);

    c.bench_function("bnb", |b| {
        b.iter(|| {
            let (iteration_count, inputs) =
                select_coins_bnb(target, cost_of_change, max_weight, &utxos).unwrap();
            assert_eq!(iteration_count, 100000);

            assert_eq!(2, inputs.len());
            assert_eq!(Amount::from_sat_u32(1_000), inputs[0].value());
            assert_eq!(Amount::from_sat_u32(3), inputs[1].value());
        })
    });
}

criterion_group!(benches, bnb_benchmark);
criterion_main!(benches);
