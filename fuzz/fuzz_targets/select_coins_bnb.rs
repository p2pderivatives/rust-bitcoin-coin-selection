#![no_main]

use arbitrary::Arbitrary;
use bitcoin::{Amount, FeeRate};
use bitcoin_coin_selection::{select_coins_bnb, WeightedUtxo};
use libfuzzer_sys::fuzz_target;

#[derive(Arbitrary, Debug)]
pub struct Params {
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    weighted_utxos: Vec<WeightedUtxo>,
}

fuzz_target!(|params: Params| {
    let Params { target: t, cost_of_change: c, fee_rate: f, long_term_fee_rate: lt_f, weighted_utxos: wu } = params;
    select_coins_bnb(t, c, f, lt_f, &wu);
});
