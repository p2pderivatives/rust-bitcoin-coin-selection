//! This library provides efficient algorithms to compose a set of unspent transaction outputs
//! (UTXOs).

use bitcoin::blockdata::transaction::effective_value;
use bitcoin::{Amount, FeeRate};
use rand::seq::SliceRandom;

use crate::{WeightedUtxo, CHANGE_LOWER};

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
/// <https://bitcoin.stackexchange.com/questions/103654/calculating-fee-based-on-fee-rate-for-bitcoin-transaction/114847#114847>
///
/// ## Parameters
/// ///
/// /// * `target` - target value to send to recipient.  Include the fee to pay for the known parts of the transaction excluding the fee for the inputs.
/// /// * `fee_rate` - ratio of transaction amount per size.
/// /// * `weighted_utxos` - Weighted UTXOs from which to sum the target amount.
/// /// * `rng` - used primarily by tests to make the selection deterministic.
pub fn select_coins_srd<'a, R: rand::Rng + ?Sized, Utxo: WeightedUtxo>(
    target: Amount,
    fee_rate: FeeRate,
    weighted_utxos: &'a [Utxo],
    rng: &mut R,
) -> Option<std::vec::IntoIter<&'a Utxo>> {
    if target > Amount::MAX_MONEY {
        return None;
    }

    let mut result: Vec<_> = weighted_utxos.iter().collect();
    let mut origin = result.to_owned();
    origin.shuffle(rng);

    result.clear();

    let threshold = target + CHANGE_LOWER;
    let mut value = Amount::ZERO;

    for w_utxo in origin {
        let utxo_value = w_utxo.value();
        let effective_value = effective_value(fee_rate, w_utxo.satisfaction_weight(), utxo_value)?;

        value += match effective_value.to_unsigned() {
            Ok(amt) => amt,
            Err(_) => continue,
        };

        result.push(w_utxo);

        if value >= threshold {
            return Some(result.into_iter());
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use bitcoin::{Amount, ScriptBuf, TxOut, Weight};
    use rand::rngs::mock::StepRng;

    use super::*;
    use crate::single_random_draw::select_coins_srd;
    use crate::{WeightedUtxo, CHANGE_LOWER};

    const FEE_RATE: FeeRate = FeeRate::from_sat_per_kwu(10);
    const SATISFACTION_WEIGHT: Weight = Weight::from_wu(204);

    #[derive(Debug)]
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

    fn build_utxo(amt: Amount, satisfaction_weight: Weight) -> Utxo {
        let output = TxOut { value: amt, script_pubkey: ScriptBuf::new() };
        Utxo { output, satisfaction_weight }
    }

    fn build_pool() -> Vec<Utxo> {
        let amts = vec![Amount::from_str("1 cBTC").unwrap(), Amount::from_str("2 cBTC").unwrap()];

        let mut pool = vec![];

        for a in amts {
            let utxo = build_utxo(a, SATISFACTION_WEIGHT);
            pool.push(utxo);
        }

        pool
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
        let pool = build_pool();

        let result: Vec<&Utxo> = select_coins_srd(target, FEE_RATE, &pool, &mut get_rng())
            .expect("unexpected error")
            .collect();

        let expected_result = Amount::from_str("2 cBTC").unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(expected_result, result[0].output.value);
    }

    #[test]
    fn select_coins_srd_no_solution() {
        let target: Amount = Amount::from_str("4 cBTC").unwrap();
        let pool = build_pool();

        let result = select_coins_srd(target, FEE_RATE, &pool, &mut get_rng());
        assert!(result.is_none())
    }

    #[test]
    fn select_coins_srd_all_solution() {
        let target: Amount = Amount::from_str("2.5 cBTC").unwrap();
        let pool = build_pool();

        let result: Vec<&Utxo> = select_coins_srd(target, FeeRate::ZERO, &pool, &mut get_rng())
            .expect("unexpected error")
            .collect();

        let expected_second_element = Amount::from_str("1 cBTC").unwrap();
        let expected_first_element = Amount::from_str("2 cBTC").unwrap();

        assert_eq!(result.len(), 2);
        assert_eq!(result[0].output.value, expected_first_element);
        assert_eq!(result[1].output.value, expected_second_element);
    }

    #[test]
    fn select_coins_skip_negative_effective_value() {
        let target: Amount = Amount::from_str("2 cBTC").unwrap() - CHANGE_LOWER;
        let mut pool = build_pool();

        let negative_eff_value = Amount::from_str("1 sat").unwrap();
        let utxo = build_utxo(negative_eff_value, SATISFACTION_WEIGHT);
        pool.push(utxo);

        let result: Vec<_> = select_coins_srd(target, FEE_RATE, &pool, &mut get_rng())
            .expect("unexpected error")
            .collect();

        let expected_second_element = Amount::from_str("1 cBTC").unwrap();
        let expected_first_element = Amount::from_str("2 cBTC").unwrap();

        assert_eq!(result.len(), 2);
        assert_eq!(result[0].output.value, expected_first_element);
        assert_eq!(result[1].output.value, expected_second_element);
    }

    #[test]
    fn select_coins_srd_fee_rate_error() {
        let target: Amount = Amount::from_str("2 cBTC").unwrap();
        let pool = build_pool();

        let result = select_coins_srd(target, FeeRate::MAX, &pool, &mut get_rng());
        assert!(result.is_none());
    }

    #[test]
    fn select_coins_srd_change_output_too_small() {
        let target: Amount = Amount::from_str("3 cBTC").unwrap();
        let pool = build_pool();

        let result = select_coins_srd(target, FEE_RATE, &pool, &mut get_rng());
        assert!(result.is_none());
    }

    #[test]
    fn select_coins_srd_with_high_fee() {
        // the first UTXO is 2 cBTC.  If the fee is greater than 10 sats,
        // then more than the single 2 cBTC output will need to be selected
        // if the target is 1.99999 cBTC.  That is, 2 cBTC - 1.9999 cBTC = 10 sats.
        let target: Amount = Amount::from_str("1.99999 cBTC").unwrap();

        // fee = 15 sats, since
        // 40 sat/kwu * (204 + BASE_WEIGHT) = 15 sats
        let fee_rate: FeeRate = FeeRate::from_sat_per_kwu(40);
        let pool = build_pool();

        let result: Vec<_> = select_coins_srd(target, fee_rate, &pool, &mut get_rng())
            .expect("unexpected error")
            .collect();
        let expected_second_element = Amount::from_str("1 cBTC").unwrap();
        let expected_first_element = Amount::from_str("2 cBTC").unwrap();

        assert_eq!(result.len(), 2);
        assert_eq!(result[0].output.value, expected_first_element);
        assert_eq!(result[1].output.value, expected_second_element);
    }

    #[test]
    fn select_coins_srd_addition_overflow() {
        let target: Amount = Amount::from_str("2 cBTC").unwrap();
        let amt = Amount::from_str("1 cBTC").unwrap();
        let utxo = build_utxo(amt, Weight::MAX);
        let pool = vec![utxo];

        let result = select_coins_srd(target, FEE_RATE, &pool, &mut get_rng());
        assert!(result.is_none());
    }

    #[test]
    fn select_coins_srd_threshold_overflow() {
        let target: Amount = Amount::MAX;
        let amt = Amount::from_str("1 cBTC").unwrap();
        let utxo = build_utxo(amt, Weight::MAX);
        let pool = vec![utxo];

        let result = select_coins_srd(target, FEE_RATE, &pool, &mut get_rng());
        assert!(result.is_none());
    }
}
