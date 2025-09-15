#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin_units::{Amount, Weight};
use libfuzzer_sys::fuzz_target;
use bitcoin_coin_selection_fuzz::CandidateOutputs;

use bitcoin_coin_selection::coin_grinder;

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let change_target = Amount::arbitrary(&mut u).unwrap();
    let max_selection_weight = Weight::arbitrary(&mut u).unwrap();
    let candidates = CandidateOutputs::arbitrary(&mut u).unwrap();

    let _ = coin_grinder(target, change_target, max_selection_weight, &candidates.utxos);
});
