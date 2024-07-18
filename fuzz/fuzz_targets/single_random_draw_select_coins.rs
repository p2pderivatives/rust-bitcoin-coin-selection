use bitcoin_coin_selection::WeightedUtxo;

use bitcoin_coin_selection::select_coins_srd;
use honggfuzz::fuzz;
use arbitrary::Arbitrary;

use rand::thread_rng;

use bitcoin::TxOut;
use bitcoin::FeeRate;
use bitcoin::Amount;
use bitcoin::Weight;

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

#[derive(Arbitrary, Debug)]
pub struct Params {
    target: Amount,
    fee_rate: FeeRate,
    weighted_utxos: Vec<Utxo>,
}

fn main() {
    loop {
        fuzz!(|params: Params| {
            let Params { target: t, fee_rate: f, weighted_utxos: wu } = params;
            select_coins_srd(t, f, &wu, &mut thread_rng());
        });
    }
}
