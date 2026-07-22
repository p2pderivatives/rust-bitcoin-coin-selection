#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin_coin_selection::branch_and_bound;
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

    let _ = branch_and_bound(target, cost_of_change, max_weight, fee_rate, lt_fee_rate, &pool.utxos);
});
