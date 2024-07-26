use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::ScriptBuf;
use bitcoin::TxOut;
use bitcoin::Weight;
use proptest::prelude::*;

use bitcoin_coin_selection::select_coins_bnb;
use bitcoin_coin_selection::WeightedUtxo;

#[derive(Clone, Debug)]
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

fn build_pool(vec: &mut Vec<(u8, bool)>) -> Vec<Utxo> {
    vec.into_iter()
        .map(|(u, _b)| u64::from(*u))
        .map(|a| {
            let output = TxOut {
                value: Amount::from_sat(a),
                script_pubkey: ScriptBuf::new()
            };

            let satisfaction_weight = Weight::ZERO;

            Utxo {
                output,
                satisfaction_weight
            }
        })
    .collect()
}

fn create_target_amt_from(pool: &Vec<(u8, bool)>) -> Amount {
    pool.iter().fold(Amount::ZERO, |acc, (u, b)|
        {
            if *b {
                acc + Amount::from_sat(u64::from(*u))
            } else {
                acc
            }
        }
    )
}

proptest! {
    #[test]
    // Vec<u8> is used here so that when the sum is done
    // later, that it does not overflow.
    fn test_bnb_arbitrary_pool(ref mut vec in any::<Vec<(u8, bool)>>()) {
        vec.truncate(10);
        let pool: Vec<_> = build_pool(vec);
        let target = create_target_amt_from(&vec);

        let selection: Vec<Amount> =
            select_coins_bnb(
                target,
                Amount::ZERO,
                FeeRate::ZERO,
                FeeRate::ZERO,
                &pool)
            .unwrap()
            .map(|i| i.value()).collect();

        let sum: Amount = selection.into_iter().sum();
        assert_eq!(target, sum);
    }
}

fn main() {
    test_bnb_arbitrary_pool();
}
