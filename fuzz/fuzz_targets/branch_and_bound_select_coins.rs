use bitcoin_coin_selection::WeightedUtxo;

use arbitrary::Arbitrary;
use bitcoin_coin_selection::select_coins_bnb;
use honggfuzz::fuzz;

use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::TxOut;
use bitcoin::Weight;

#[derive(Arbitrary, Debug)]
pub struct Utxo {
    output: TxOut,
    satisfaction_weight: Weight,
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
    cost_of_change: Amount,
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    weighted_utxos: Vec<Utxo>,
}

fn main() {
    loop {
        fuzz!(|params: Params| {
            let Params {
                target: t,
                cost_of_change: c,
                fee_rate: f,
                long_term_fee_rate: ltf,
                weighted_utxos: wu,
            } = params;
            select_coins_bnb(t, c, f, ltf, &wu);
        });
    }
}
