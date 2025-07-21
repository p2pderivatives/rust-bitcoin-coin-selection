#![no_main]

use arbitrary::{Arbitrary, Unstructured, Result};
use bitcoin_units::{FeeRate, Amount, Weight};
use bitcoin_coin_selection::{select_coins_srd, WeightedUtxo};
use libfuzzer_sys::fuzz_target;
use rand::thread_rng;

#[derive(Debug)]
pub struct UtxoPool {
    pub utxos: Vec<WeightedUtxo>,
}

impl<'a> Arbitrary<'a> for UtxoPool {
    fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
        let init: Vec<(Amount, Weight)> = Vec::arbitrary(u)?;
        let fee_rate = FeeRate::arbitrary(u).unwrap();
        let lt_fee_rate = FeeRate::arbitrary(u).unwrap();
        let pool: Vec<WeightedUtxo> =
            init.iter().filter_map(|i| WeightedUtxo::new(i.0, i.1, fee_rate, lt_fee_rate)).collect();

        Ok(UtxoPool { utxos: pool })
    }
}

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let max_weight = Weight::arbitrary(&mut u).unwrap();
    let pool = UtxoPool::arbitrary(&mut u).unwrap();

    let _ = select_coins_srd(target, max_weight, &pool.utxos, &mut thread_rng());
});
