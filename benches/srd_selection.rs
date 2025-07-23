use bitcoin_coin_selection::{select_coins_srd, WeightedUtxo};
use bitcoin_units::{Amount, FeeRate, Weight};
use criterion::{criterion_group, criterion_main, Criterion};
use rand::thread_rng;

pub fn srd_benchmark(c: &mut Criterion) {
    let utxo = WeightedUtxo::new(Amount::from_sat_u32(100), Weight::ZERO);
    let pool = vec![utxo; 1_000];

    let target = Amount::from_sat_u32(50_000);
    let fee_rate = FeeRate::from_sat_per_kwu(10);

    c.bench_function("srd", |b| {
        b.iter(|| {
            let (iteration_count, inputs) =
                select_coins_srd(target, fee_rate, &pool, &mut thread_rng()).unwrap();
            assert_eq!(iteration_count, 1_000);
            assert_eq!(inputs.len(), 1_000);
        })
    });
}

criterion_group!(benches, srd_benchmark);
criterion_main!(benches);
