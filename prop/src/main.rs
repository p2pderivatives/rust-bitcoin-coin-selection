use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::ScriptBuf;
use bitcoin::TxOut;
use bitcoin::Weight;
use proptest::prelude::*;

use bitcoin_coin_selection::select_coins_bnb;
use bitcoin_coin_selection::WeightedUtxo;

use std::str::FromStr;

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

fn build_linear_pool() -> Vec<Utxo> {
    (1..10)
        .map(|i| format!("{} cBTC", i))
        .map(|s| Amount::from_str(&s).unwrap())
        .map(|a| {
            let output = TxOut {
                value: a,
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

    #[test]
    fn test_bnb_arbitrary_target(t in any::<u64>()) {
        let target_str = format!("{} cBTC", t % 10);
        let target = Amount::from_str(&target_str).unwrap();
        let pool = build_linear_pool();

        let selection_sum: Amount =
            select_coins_bnb(
                target,
                Amount::ZERO,
                FeeRate::ZERO,
                FeeRate::ZERO,
                &pool)
            .unwrap()
            .map(|i| i.value()).sum();

        assert_eq!(selection_sum, target);
    }
}

fn main() {
    test_bnb_arbitrary_pool();
    test_bnb_arbitrary_target();
}
