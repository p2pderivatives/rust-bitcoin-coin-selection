#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin_coin_selection::select_coins;
use bitcoin_units::{Amount, FeeRate, Weight};
use libfuzzer_sys::fuzz_target;
use bitcoin_coin_selection_fuzz::Pool;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let cost_of_change = Amount::arbitrary(&mut u).unwrap();
    let max_weight = Weight::arbitrary(&mut u).unwrap();
    let fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let lt_fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let pool = Pool::arbitrary(&mut u).unwrap();

    let _ = select_coins(target, cost_of_change, max_weight, fee_rate, lt_fee_rate, &pool.utxos);
});
