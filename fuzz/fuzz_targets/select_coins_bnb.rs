#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin_coin_selection::select_coins_bnb;
use bitcoin_coin_selection_fuzz::CandidateOutputs;
use bitcoin_units::{Amount, Weight};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let cost_of_change = Amount::arbitrary(&mut u).unwrap();
    let max_weight = Weight::arbitrary(&mut u).unwrap();
    let candidates = CandidateOutputs::arbitrary(&mut u).unwrap();

    let _ = select_coins_bnb(target, cost_of_change, max_weight, &candidates.utxos);
});
