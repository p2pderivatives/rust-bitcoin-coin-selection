#![no_main]

use arbitrary::Arbitrary;
use bitcoin::{Amount, FeeRate};
use bitcoin_coin_selection::{select_coins_srd, WeightedUtxo};
use libfuzzer_sys::fuzz_target;
use rand::thread_rng;

#[derive(Arbitrary, Debug)]
pub struct Params {
    target: Amount,
    fee_rate: FeeRate,
    weighted_utxos: Vec<WeightedUtxo>,
}

fuzz_target!(|params: Params| {
    let Params { target: t, fee_rate: f, weighted_utxos: wu } = params;
    select_coins_srd(t, f, &wu, &mut thread_rng());
});
