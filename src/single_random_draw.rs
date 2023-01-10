//! This library provides efficient algorithms to compose a set of unspent transaction outputs
//! (UTXOs).

use crate::errors::Error;
use crate::WeightedUtxo;
use crate::CHANGE_LOWER;
use crate::TXIN_BASE_WEIGHT;
use bitcoin::Amount;
use bitcoin::FeeRate;
use rand::seq::SliceRandom;

/// Calculates the effective_value of an input.
///
/// Returns `Ok(None)` if the effective_value is negative.  If the effective_value is positive, return `Ok(Some(Amount))`.
///
/// ## Errors
///
/// Returns `Err(Error::Multiplication)` if `FeeRate` * `Weight` overflows.
///
fn get_effective_value(
    weighted_utxo: &WeightedUtxo,
    fee_rate: FeeRate,
) -> Result<Option<Amount>, Error> {
    let satisfaction_weight = weighted_utxo.satisfaction_weight;

    let checked_weight = satisfaction_weight.checked_add(TXIN_BASE_WEIGHT);

    let weight = match checked_weight {
        Some(w) => w,
        None => return Err(Error::AdditionOverflow(satisfaction_weight, TXIN_BASE_WEIGHT)),
    };

    let input_fee: Option<Amount> = fee_rate.checked_mul_by_weight(weight);

    match input_fee {
        Some(f) => Ok(weighted_utxo.utxo.value.checked_sub(f)),
        None => Err(Error::MultiplicationOverflow(satisfaction_weight, fee_rate)),
    }
}

/// Randomly select coins for the given target by shuffling the UTXO pool and
/// taking UTXOs until the given target is reached.
///
/// The fee_rate can have an impact on the selection process since the fee
/// must be paid for in addition to the target.  However, the total fee
/// is dependant on the number of UTXOs consumed and the new inputs created.
/// The selection strategy therefore calculates the fees of what is known
/// ahead of time (the number of UTXOs create and the transaction header),
/// and then then for each new input, the effective_value is tracked which
/// deducts the fee for each individual input at selection time.  For more
/// discussion see the following:
///
/// https://bitcoin.stackexchange.com/questions/103654/calculating-fee-based-on-fee-rate-for-bitcoin-transaction/114847#114847
///
/// ## Parameters
/// ///
/// /// * `target` - target value to send to recipient.  Include the fee to pay for the known parts of the transaction excluding the fee for the inputs.
/// /// * `fee_rate` - ratio of transaction amount per size.
/// /// * `weighted_utxos` - Weighted UTXOs from which to sum the target amount.
/// /// * `rng` - used primarily by tests to make the selection deterministic.
pub fn select_coins_srd<R: rand::Rng + ?Sized>(
    target: Amount,
    fee_rate: FeeRate,
    weighted_utxos: &mut [WeightedUtxo],
    rng: &mut R,
) -> Result<Vec<WeightedUtxo>, Error> {
    let mut result: Vec<WeightedUtxo> = Vec::new();

    weighted_utxos.shuffle(rng);

    let threshold = target + CHANGE_LOWER;
    let mut value = Amount::ZERO;

    for w_utxo in weighted_utxos {
        // note: I'd prefer to use filter() and filter all inputs that have a negative
        //       effective_value, however, an error message is returned if a multiplication
        //       overflow occurs while the caclulating effective_value.
        let effective_value: Option<Amount> = get_effective_value(w_utxo, fee_rate)?;

        // skip if effective_value is negative.
        match effective_value {
            Some(e) => value += e,
            None => continue,
        }

        result.push(w_utxo.clone());

        if value >= threshold {
            return Ok(result);
        }
    }

    Ok(Vec::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::single_random_draw::select_coins_srd;
    use crate::WeightedUtxo;
    use crate::CHANGE_LOWER;
    use bitcoin::Amount;
    use bitcoin::ScriptBuf;
    use bitcoin::TxOut;
    use bitcoin::Weight;
    use core::str::FromStr;
    use rand::rngs::mock::StepRng;

    const FEE_RATE: FeeRate = FeeRate::from_sat_per_kwu(10);
    const SATISFACTION_SIZE: Weight = Weight::from_wu(204);

    fn create_weighted_utxos() -> Vec<WeightedUtxo> {
        let utxo_one = WeightedUtxo {
            satisfaction_weight: SATISFACTION_SIZE,
            utxo: TxOut {
                value: Amount::from_str("1 cBTC").unwrap(),
                script_pubkey: ScriptBuf::new(),
            },
        };

        let utxo_two = WeightedUtxo {
            satisfaction_weight: SATISFACTION_SIZE,
            utxo: TxOut {
                value: Amount::from_str("2 cBTC").unwrap(),
                script_pubkey: ScriptBuf::new(),
            },
        };

        vec![utxo_one, utxo_two]
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
        let mut weighted_utxos: Vec<WeightedUtxo> = create_weighted_utxos();

        let result = select_coins_srd(target, FEE_RATE, &mut weighted_utxos, &mut get_rng())
            .expect("unexpected error");

        assert_eq!(vec![weighted_utxos[0].clone()], result);
    }

    #[test]
    fn select_coins_srd_no_solution() {
        let target: Amount = Amount::from_str("4 cBTC").unwrap();
        let mut weighted_utxos: Vec<WeightedUtxo> = create_weighted_utxos();

        let result = select_coins_srd(target, FEE_RATE, &mut weighted_utxos, &mut get_rng())
            .expect("unexpected error");

        assert!(result.is_empty());
    }

    #[test]
    fn select_coins_srd_all_solution() {
        let target: Amount = Amount::from_str("2.5 cBTC").unwrap();
        let mut weighted_utxos: Vec<WeightedUtxo> = create_weighted_utxos();

        let result = select_coins_srd(target, FeeRate::ZERO, &mut weighted_utxos, &mut get_rng())
            .expect("unexpected error");

        assert_eq!(weighted_utxos.clone(), result);
    }

    #[test]
    fn select_coins_skip_negative_effective_value() {
        let target: Amount = Amount::from_str("1 cBTC").unwrap() - CHANGE_LOWER;

        let mut weighted_utxos: Vec<WeightedUtxo> = vec![WeightedUtxo {
            satisfaction_weight: Weight::ZERO,
            utxo: TxOut {
                value: Amount::from_str("1 sat").unwrap(),
                script_pubkey: ScriptBuf::new(),
            },
        }];

        let result = select_coins_srd(target, FEE_RATE, &mut weighted_utxos, &mut get_rng())
            .expect("unexpected error");

        assert!(result.is_empty());
    }

    #[test]
    fn select_coins_srd_fee_rate_error() {
        let target: Amount = Amount::from_str("2 cBTC").unwrap();
        let mut weighted_utxos: Vec<WeightedUtxo> = create_weighted_utxos();

        let result: Error =
            select_coins_srd(target, FeeRate::MAX, &mut weighted_utxos, &mut get_rng())
                .expect_err("expected error");

        assert_eq!(result.to_string(), "204 * 18446744073709551615 exceeds u64 Max");
    }

    #[test]
    fn select_coins_srd_change_output_too_small() {
        let target: Amount = Amount::from_str("3 cBTC").unwrap();
        let mut weighted_utxos: Vec<WeightedUtxo> = create_weighted_utxos();

        let result = select_coins_srd(target, FEE_RATE, &mut weighted_utxos, &mut get_rng())
            .expect("unexpected error");

        assert!(result.is_empty());
    }

    #[test]
    fn select_coins_srd_with_high_fee() {
        let target: Amount = Amount::from_str("1.905 cBTC").unwrap();
        // The high fee_rate will cause both utxos to be consumed
        // instead of just one.
        let fee_rate: FeeRate = FeeRate::from_sat_per_kwu(250);
        let mut weighted_utxos: Vec<WeightedUtxo> = create_weighted_utxos();

        let result = select_coins_srd(target, fee_rate, &mut weighted_utxos, &mut get_rng())
            .expect("unexpected error");

        assert_eq!(weighted_utxos.clone(), result);
    }

    #[test]
    fn select_coins_srd_addition_overflow() {
        let target: Amount = Amount::from_str("2 cBTC").unwrap();

        let mut weighted_utxos: Vec<WeightedUtxo> = vec![WeightedUtxo {
            satisfaction_weight: Weight::MAX,
            utxo: TxOut {
                value: Amount::from_str("1 cBTC").unwrap(),
                script_pubkey: ScriptBuf::new(),
            },
        }];

        let result: Error = select_coins_srd(target, FEE_RATE, &mut weighted_utxos, &mut get_rng())
            .expect_err("expected error");

        assert_eq!(result.to_string(), "18446744073709551615 + 40 exceeds u64 Max");
    }
}
