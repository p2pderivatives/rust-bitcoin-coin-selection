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
        let pool: Vec<WeightedUtxo> =
            init.iter().map(|i| WeightedUtxo::new(i.0, i.1)).collect();

        Ok(UtxoPool { utxos: pool })
    }
}

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(&data);

    let target = Amount::arbitrary(&mut u).unwrap();
    let fee_rate = FeeRate::arbitrary(&mut u).unwrap();
    let pool = UtxoPool::arbitrary(&mut u).unwrap();

    let _ = select_coins_srd(target, fee_rate, &pool.utxos, &mut thread_rng());
});
