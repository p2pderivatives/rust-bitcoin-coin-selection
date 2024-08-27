#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin::{TxOut, FeeRate, Amount, Weight};
use bitcoin_coin_selection::{select_coins_srd, WeightedUtxo};
use libfuzzer_sys::fuzz_target;
use rand::thread_rng;

#[derive(Arbitrary, Debug)]
pub struct Utxo {
    output: TxOut,
    satisfaction_weight: Weight
}

impl WeightedUtxo for Utxo {
    fn satisfaction_weight(&self) -> Weight {
        self.satisfaction_weight
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

    select_coins_srd(target, fee_rate, &wu, &mut thread_rng());
});
