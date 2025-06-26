#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use bitcoin_units::{FeeRate, Amount, Weight};
use bitcoin_coin_selection::{select_coins, WeightedUtxo};
use libfuzzer_sys::fuzz_target;

#[derive(Arbitrary, Debug)]
pub struct Utxo {
    value: Amount,
    weight: Weight,
}

impl WeightedUtxo for Utxo {
    fn weight(&self) -> Weight {
        self.weight
    }

    fn value(&self) -> Amount {
        self.value
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
