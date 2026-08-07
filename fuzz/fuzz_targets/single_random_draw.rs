#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin_coin_selection::single_random_draw;
use bitcoin_units::{Amount, FeeRate, Weight};
use libfuzzer_sys::fuzz_target;
use bitcoin_coin_selection_fuzz::Pool;
use rand::thread_rng;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let max_weight = Weight::arbitrary(&mut u).unwrap();
    let fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let pool = Pool::arbitrary(&mut u).unwrap();

    let _ = single_random_draw(target, max_weight, fee_rate, &mut thread_rng(), &pool.utxos);
});
