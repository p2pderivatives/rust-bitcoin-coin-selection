use criterion::{black_box, criterion_group, criterion_main, Criterion};

use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::ScriptBuf;
use bitcoin::SignedAmount;
use bitcoin::TxOut;
use rust_bitcoin_coin_selection::select_coins_bnb;
use rust_bitcoin_coin_selection::Coin;

pub fn criterion_benchmark(c: &mut Criterion) {
    // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.h#L18
    let cost_of_change = Amount::from_sat(50_000);

    let no_op = TxOut { value: Amount::ZERO, script_pubkey: ScriptBuf::new() };
    let fee_rate = FeeRate::ZERO;
    let long_term_fee_rate = FeeRate::ZERO;
    let waste = SignedAmount::ZERO;

    let one = Coin {
        utxo: no_op.clone(),
        effective_value: Amount::from_sat(1_000),
        waste,
        fee_rate,
        long_term_fee_rate,
    };

    let two = Coin {
        utxo: no_op.clone(),
        effective_value: Amount::from_sat(3),
        waste,
        fee_rate,
        long_term_fee_rate,
    };

    let target = Amount::from_sat(1_003);
    let mut utxo_pool = vec![one; 1000];
    utxo_pool.push(two);

    c.bench_function("bnb 1000", |b| {
        b.iter(|| {
            let result: Vec<_> = select_coins_bnb(
                black_box(target),
                black_box(cost_of_change),
                black_box(&utxo_pool),
            )
            .unwrap()
            .collect();

            assert_eq!(2, result.len());
            assert_eq!(Amount::from_sat(1_000), result[0].effective_value);
            assert_eq!(Amount::from_sat(3), result[1].effective_value);
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
