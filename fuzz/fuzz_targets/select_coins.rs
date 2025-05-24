#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin::{TxOut, FeeRate, Amount};
use bitcoin_coin_selection::{select_coins, WeightedUtxo};
use libfuzzer_sys::fuzz_target;

use bitcoin::transaction::InputWeightPrediction;

#[derive(Arbitrary, Debug)]
pub struct Utxo {
    output: TxOut,
    predict_weight: InputWeightPrediction,
}

impl WeightedUtxo for Utxo {
    fn predict_weight(&self) -> InputWeightPrediction {
        self.predict_weight
    }

    fn value(&self) -> Amount {
        self.output.value
    }
}

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let cost_of_change = Amount::arbitrary(&mut u).unwrap();
    let fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let lt_fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let wu = Vec::<Utxo>::arbitrary(&mut u).unwrap();

    select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &wu);
});
