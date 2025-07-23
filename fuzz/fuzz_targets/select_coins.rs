#![no_main]

use arbitrary::{Arbitrary, Unstructured, Result};
use bitcoin_units::{FeeRate, Amount, Weight};
use bitcoin_coin_selection::{select_coins, WeightedUtxo};
use libfuzzer_sys::fuzz_target;

#[derive(Debug)]
pub struct UtxoPool {
    pub utxos: Vec<WeightedUtxo>,
}

impl<'a> Arbitrary<'a> for UtxoPool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let init: Vec<(Amount, Weight)> = Vec::arbitrary(u)?;
        let pool: Vec<WeightedUtxo> =
            init.iter().map(|i| WeightedUtxo::new(i.0, i.1)).collect();

        Ok(UtxoPool { utxos: pool })
    }
}

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let cost_of_change = Amount::arbitrary(&mut u).unwrap();
    let fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let lt_fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let pool = UtxoPool::arbitrary(&mut u).unwrap();

    let _ = select_coins(target, cost_of_change, fee_rate, lt_fee_rate, &pool.utxos);
});
