use criterion::{black_box, criterion_group, criterion_main, Criterion};

use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::ScriptBuf;
use bitcoin::TxOut;
use bitcoin::Weight;

use bitcoin::transaction::InputWeightPrediction;
use rust_bitcoin_coin_selection::select_coins_bnb;
use rust_bitcoin_coin_selection::WeightedUtxo;

pub fn criterion_benchmark(c: &mut Criterion) {
    let one = WeightedUtxo {
        satisfaction_weight: Weight::ZERO,
        utxo: TxOut { value: Amount::from_sat(1_000), script_pubkey: ScriptBuf::new() },
    };

    let two = WeightedUtxo {
        satisfaction_weight: Weight::ZERO,
        utxo: TxOut { value: Amount::from_sat(3), script_pubkey: ScriptBuf::new() },
    };

    let target = Amount::from_sat(1_003);
    let mut utxo_pool = vec![one; 1000];
    utxo_pool.push(two);

    c.bench_function("bnb 1000", |b| {
        b.iter(|| {
            let result: Vec<_> = select_coins_bnb(
                black_box(target),
                black_box(InputWeightPrediction::P2WPKH_MAX),
                black_box(FeeRate::ZERO),
                black_box(FeeRate::ZERO),
                black_box(&utxo_pool),
            )
            .unwrap()
            .collect();

            assert_eq!(2, result.len());
            assert_eq!(Amount::from_sat(1_000), result[0].utxo.value);
            assert_eq!(Amount::from_sat(3), result[1].utxo.value);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
