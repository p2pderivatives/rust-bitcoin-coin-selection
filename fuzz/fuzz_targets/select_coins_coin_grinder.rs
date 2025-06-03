#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin::{TxOut, FeeRate, Amount, Weight};
use bitcoin_coin_selection::WeightedUtxo;
use libfuzzer_sys::fuzz_target;

use bitcoin_coin_selection::coin_grinder;

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
    let change_target = Amount::arbitrary(&mut u).unwrap();
    let max_selection_weight = Weight::arbitrary(&mut u).unwrap();
    let fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let wu = Vec::<Utxo>::arbitrary(&mut u).unwrap();

    coin_grinder(target, change_target, max_selection_weight, fee_rate, &wu);
});
