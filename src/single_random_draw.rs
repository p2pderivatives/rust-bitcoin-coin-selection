//! This library provides efficient algorithms to compose a set of unspent transaction outputs
//! (UTXOs).

#[cfg(any(test, feature = "rand"))]
use crate::errors::LibError;

use bitcoin::Amount;
use bitcoin::blockdata::transaction;
use bitcoin::FeeRate;
use bitcoin::TxOut;
use bitcoin::Weight;
use crate::CHANGE_LOWER;
use rand::seq::SliceRandom;

/// Randomly select coins for the given target by shuffling the utxo pool and
/// taking UTXOs until the given target is reached.
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins_srd<R: rand::Rng + ?Sized>(
    target: Amount,
    outputs: &mut Vec<TxOut>,
    fee_rate: FeeRate,
    rng: &mut R)
-> Result<Option<Vec<TxOut>>, LibError> {
    outputs.shuffle(rng);

    let mut selected_effective_value: Amount = Amount::ZERO;
    let mut i = 0;
    let mut result = Vec::new();

    // The required size of a change output must be at least
    // larger than the target by CHANGE_LOWER.  Therefore,
    // CHANGE_LOWER + target becomes the new lower bound for the
    // selection.
    while selected_effective_value < target + CHANGE_LOWER && i < outputs.len() {
        let output: &TxOut = &outputs[i];
        let value: Amount = output.value;

        let outputs = outputs.iter().map(|txout| txout.script_pubkey.len());

        let weight: Weight = transaction::predict_weight(
            None::<Vec<transaction::InputWeightPrediction>>,
            Some(outputs),
        );

        let fee: Option<Amount> = fee_rate.checked_mul_by_weight(weight);

        match fee {
            Some(f) => {
                let effective_value = value - f;
                selected_effective_value += effective_value;
            },
            None => return Err(LibError::Multiplication(weight, fee_rate))
        }

        result.push(output.clone());
        i += 1;
    }

    if selected_effective_value >= target + CHANGE_LOWER {
        Ok(Some(result))
    } else {
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::single_random_draw::select_coins_srd;
    use crate::CHANGE_LOWER;
    use bitcoin::Amount;
    use bitcoin::ScriptBuf;
    use core::str::FromStr;
    use rand::rngs::mock::StepRng;

    const FEE_RATE: FeeRate = FeeRate::from_sat_per_kwu(10);

    fn create_outputs() -> Vec<TxOut> {
        vec![
            TxOut { value: Amount::from_str("1 cBTC").unwrap(), script_pubkey: ScriptBuf::new() },
            TxOut { value: Amount::from_str("2 cBTC").unwrap(), script_pubkey: ScriptBuf::new() },
        ]
    }

    fn get_rng() -> StepRng {
        // [1, 2]
        // let mut vec: Vec<u32> = (1..3).collect();
        // let mut rng = StepRng::new(0, 0);
        //
        // [2, 1]
        // vec.shuffle(&mut rng);

        // shuffle() will always result in the order described above when a constant
        // is used as the rng.  The first is removed from the beginning and added to
        // the end while the remaining elements keep their order.
        StepRng::new(0, 0)
    }

    #[test]
    fn select_coins_srd_with_solution() {
        let target: Amount = Amount::from_str("1.5 cBTC").unwrap();
        let mut outputs: Vec<TxOut> = create_outputs();

        let utxo_match: Vec<TxOut> =
            select_coins_srd(target, &mut outputs, FEE_RATE, &mut get_rng())
                .expect("unexpected error")
                .expect("expected match");

        assert_eq!(utxo_match.len(), 1);
        assert_eq!(utxo_match[0], outputs[0]);
    }

    #[test]
    fn select_coins_srd_no_solution() {
        let target: Amount = Amount::from_str("4 cBTC").unwrap();
        let mut outputs: Vec<TxOut> = create_outputs();

        let utxo_match: Option<Vec<TxOut>> =
            select_coins_srd(target, &mut outputs, FEE_RATE, &mut get_rng()).expect("unexpected error");
        assert!(utxo_match.is_none());
    }

    #[test]
    fn select_coins_all_solution() {
        let target: Amount = Amount::from_str("3 cBTC").unwrap() - CHANGE_LOWER;
        let mut outputs: Vec<TxOut> = create_outputs();

        let utxo_match: Vec<TxOut> =
            select_coins_srd(target, &mut outputs, FeeRate::ZERO, &mut get_rng())
                .expect("unexpected error")
                .expect("expected match");
        assert_eq!(utxo_match.len(), 2);
    }

    #[test]
    fn select_coins_srd_effective_value_too_small() {
        let target: Amount = Amount::from_str("3 cBTC").unwrap() - CHANGE_LOWER;
        let mut outputs: Vec<TxOut> = create_outputs();

        // This test will fail if SRD is using value instead of effective_value
        let utxo_match: Option<Vec<TxOut>> =
            select_coins_srd(target, &mut outputs, FEE_RATE, &mut get_rng()).expect("unexpected error");

        assert!(utxo_match.is_none());
    }

    #[test]
    fn select_coins_srd_fee_rate_error() {
        let target: Amount = Amount::from_str("2 cBTC").unwrap();
        let mut outputs: Vec<TxOut> = create_outputs();

        let error = select_coins_srd(target, &mut outputs, FeeRate::MAX, &mut get_rng())
            .expect_err("expected multiplication overflow");
        assert_eq!(error.to_string(), "112 * 18446744073709551615 exceeds u64 Max");
    }

    #[test]
    fn select_coins_srd_change_output_too_small() {
        let target: Amount = Amount::from_str("3 cBTC").unwrap();
        let mut outputs: Vec<TxOut> = create_outputs();

        let utxo_match: Option<Vec<TxOut>> =
            select_coins_srd(target, &mut outputs, FeeRate::ZERO, &mut get_rng()).expect("unexpected error");
        assert!(utxo_match.is_none());
    }
}
