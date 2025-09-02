#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin_coin_selection::select_coins;
use bitcoin_coin_selection_fuzz::UtxoPool;
use bitcoin_units::{Amount, Weight};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let cost_of_change = Amount::arbitrary(&mut u).unwrap();
    let max_weight = Weight::arbitrary(&mut u).unwrap();
    let pool = UtxoPool::arbitrary(&mut u).unwrap();

    let _ = select_coins(target, cost_of_change, max_weight, &pool.utxos);
});
