use bitcoin::{Amount, FeeRate, ScriptBuf, TxOut, Weight};
use bitcoin_coin_selection::{select_coins_bnb, WeightedUtxo};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

#[derive(Debug, Clone)]
pub struct Utxo {
    output: TxOut,
    weight: Weight,
}

impl WeightedUtxo for Utxo {
    fn weight(&self) -> Weight { self.weight }
    fn value(&self) -> Amount { self.output.value }
}

pub fn criterion_benchmark(c: &mut Criterion) {
    // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.h#L18
    let cost_of_change = Amount::from_sat(50_000);

    let one = Utxo {
        output: TxOut { value: Amount::from_sat(1_000), script_pubkey: ScriptBuf::new() },
        weight: Weight::ZERO,
    };

    let two = Utxo {
        output: TxOut { value: Amount::from_sat(3), script_pubkey: ScriptBuf::new() },
        weight: Weight::ZERO,
    };

    let target = Amount::from_sat(1_003);
    let mut utxo_pool = vec![one; 1000];
    utxo_pool.push(two);

    c.bench_function("bnb 1000", |b| {
        b.iter(|| {
            let result: Vec<_> = select_coins_bnb(
                black_box(target),
                black_box(cost_of_change),
                black_box(FeeRate::ZERO),
                black_box(FeeRate::ZERO),
                black_box(&utxo_pool),
            )
            .unwrap()
            .collect();

            assert_eq!(2, result.len());
            assert_eq!(Amount::from_sat(1_000), result[0].value());
            assert_eq!(Amount::from_sat(3), result[1].value());
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
