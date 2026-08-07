#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin_coin_selection::coin_grinder;
use bitcoin_units::{Amount, FeeRate, Weight};
use libfuzzer_sys::fuzz_target;
use bitcoin_coin_selection_fuzz::Pool;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let change_target = Amount::arbitrary(&mut u).unwrap();
    let max_weight = Weight::arbitrary(&mut u).unwrap();
    let fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let pool = Pool::arbitrary(&mut u).unwrap();

    let _ = coin_grinder(target, change_target, max_weight, fee_rate, &pool.utxos);
});
