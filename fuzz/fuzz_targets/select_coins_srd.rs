#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin::{TxOut, FeeRate, Amount, Weight};
use bitcoin_coin_selection::{single_random_draw_with_rng, WeightedUtxo};
use libfuzzer_sys::fuzz_target;
use rand::thread_rng;

#[derive(Arbitrary, Debug)]
pub struct Utxo {
    output: TxOut,
    weight: Weight
}

impl WeightedUtxo for Utxo {
    fn weight(&self) -> Weight {
        self.weight
    }

    fn value(&self) -> Amount {
        self.output.value
    }
}

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let wu = Vec::<Utxo>::arbitrary(&mut u).unwrap();

    single_random_draw_with_rng(target, fee_rate, &wu, &mut thread_rng());
});
