// SPDX-License-Identifier: CC0-1.0
//
//! Single Random Draw Algorithem.
//!
//! This module introduces the Single Random Draw Coin-Selection Algorithm.

use bitcoin_units::{Amount, CheckedSum, FeeRate, SignedAmount};
use rand::seq::SliceRandom;

use crate::{Return, WeightedUtxo, CHANGE_LOWER};

/// Randomize the input set and select coins until the target is reached.
///
/// # Parameters
///
/// * `target` - target value to send to recipient.  Include the fee to pay for
///   the known parts of the transaction excluding the fee for the inputs.
/// * `fee_rate` - ratio of transaction amount per size.
/// * `weighted_utxos` - Weighted UTXOs from which to sum the target amount.
/// * `rng` - used primarily by tests to make the selection deterministic.
///
/// # Returns
///
/// * `Some((u32, Vec<WeightedUtxo>))` where `Vec<WeightedUtxo>` is empty on no matches found.
///   An empty vec signifies that all possibilities where explored successfully and no match
///   could be found with the given parameters.  The first element of the tuple is a u32 which
///   represents the number of iterations needed to find a solution.
/// * `None` un-expected results OR no match found.  A future implementation may add Error types
///   which will differentiate between an unexpected error and no match found.  Currently, a None
///   type occurs when one or more of the following criteria are met:
///     - Overflow when summing available UTXOs
///     - Not enough potential amount to meet the target
///     - Target Amount is zero (no match possible)
///     - Search was successful yet no match found
pub fn select_coins_srd<'a, R: rand::Rng + ?Sized, Utxo: WeightedUtxo>(
    target: Amount,
    fee_rate: FeeRate,
    weighted_utxos: &'a [Utxo],
    rng: &mut R,
) -> Return<'a, Utxo> {
    let mut result: Vec<_> = weighted_utxos.iter().collect();
    let available_value = weighted_utxos
        .iter()
        .map(|u| u.effective_value(fee_rate).unwrap_or(SignedAmount::ZERO))
        .checked_sum()?;

    let threshold = target.checked_add(CHANGE_LOWER)?;
    if available_value < threshold.to_signed() {
        return None;
    }

    let mut origin = result.to_owned();
    origin.shuffle(rng);

    result.clear();

    let mut value = Amount::ZERO;

    let mut iteration = 0;
    for w_utxo in origin {
        iteration += 1;
        let effective_value = w_utxo.effective_value(fee_rate);

        if let Some(e) = effective_value {
            if let Ok(v) = e.to_unsigned() {
                value = (value + v).unwrap();

                result.push(w_utxo);

                if value >= threshold {
                    return Some((iteration, result));
                }
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use arbitrary::Arbitrary;
    use arbtest::arbtest;
    use bitcoin_units::Amount;
    use rand::rngs::mock::StepRng;

    use super::*;
    use crate::single_random_draw::select_coins_srd;
    use crate::tests::{assert_ref_eq, parse_fee_rate, UtxoPool};

    #[derive(Debug)]
    pub struct TestSRD<'a> {
        target: &'a str,
        fee_rate: &'a str,
        weighted_utxos: &'a [&'a str],
        expected_utxos: &'a [&'a str],
        expected_iterations: u32,
    }

    impl TestSRD<'_> {
        fn assert(&self) {
            let target = Amount::from_str(self.target).unwrap();
            let fee_rate = parse_fee_rate(self.fee_rate);

            let pool: UtxoPool = UtxoPool::new(self.weighted_utxos, fee_rate);

            let result = select_coins_srd(target, fee_rate, &pool.utxos, &mut get_rng());

            if let Some((iterations, inputs)) = result {
                assert_eq!(iterations, self.expected_iterations);

                let expected_selection = self.expected_utxos;
                let expected: UtxoPool = UtxoPool::new(expected_selection, fee_rate);

                assert_ref_eq(inputs, expected.utxos);
            } else {
                assert!(self.expected_utxos.is_empty());
                // Remove this check once iteration count is returned by error
                assert_eq!(self.expected_iterations, 0);
            }
        }
    }

    fn assert_coin_select(target_str: &str, expected_iterations: u32, expected_utxos: &[&str]) {
        TestSRD {
            target: target_str,
            fee_rate: "10 sat/kwu",
            weighted_utxos: &["1 cBTC/204 wu", "2 cBTC/204 wu"],
            expected_utxos,
            expected_iterations,
        }
        .assert();
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
    fn select_coins_srd_with_solution() { assert_coin_select("1.5 cBTC", 1, &["2 cBTC/204 wu"]); }

    #[test]
    fn select_coins_srd_all_solution() {
        assert_coin_select("2.5 cBTC", 2, &["2 cBTC/204 wu", "1 cBTC/204 wu"]);
    }

    #[test]
    #[should_panic]
    // the target is greater than the sum of available UTXOs.
    // therefore asserting that a selection exists should panic.
    fn select_coins_srd_eleven_invalid_target_should_panic() {
        assert_coin_select("11 cBTC", 8, &["1 cBTC"]);
    }

    #[test]
    #[should_panic]
    fn select_coins_srd_params_invalid_target_should_panic() {
        // the target is greater than the sum of available UTXOs.
        // therefore asserting that a selection exists should panic.
        TestSRD {
            target: "11 cBTC",
            fee_rate: "0",
            weighted_utxos: &["1.5 cBTC"],
            expected_utxos: &["1.5 cBTC"],
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_no_solution() {
        TestSRD {
            target: "4 cBTC",
            fee_rate: "0",
            weighted_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB"],
            expected_utxos: &[],
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_skip_negative_effective_value() {
        // A value of 2 cBTC is needed after CHANGE_LOWER is subtracted.
        // After randomization, the effective values are: [1,9 cBTC, -2 sats, 0.1 cBTC]
        // The middle utxo is skipped since it's effective value is negative.
        TestSRD {
            target: "1.95 cBTC", // 2 cBTC - CHANGE_LOWER
            fee_rate: "10 sat/kwu",
            weighted_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB", "e(-1 sat)/68 vB"],
            expected_utxos: &["2 cBTC/68 vB", "1 cBTC/68 vB"],
            expected_iterations: 3,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_change_output_too_small() {
        // The resulting change must be greater than CHANGE_LOWER
        // therefore, an exact match will fail.
        TestSRD {
            target: "3 cBTC",
            fee_rate: "10 sat/kwu",
            weighted_utxos: &["e(1 cBTC)/68 vB", "e(2 cBTC)/68 vB"],
            expected_utxos: &[],
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_with_high_fee() {
        // Although the first selected UTXO valued at 2050000 meets the
        // target and meets the threshold of target + CHANGE, the value
        // is not enough since when the effective value is calculated,
        // it falls bellow the threshold.  Therefore multiple UTXOs are
        // selected.
        TestSRD {
            target: "2 cBTC",
            fee_rate: "10 sat/kwu",
            weighted_utxos: &["1 cBTC/68 vB", "2050000 sats/68 vB"],
            expected_utxos: &["2050000 sats/68 vB", "1 cBTC/68 vB"],
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_threshold_overflow() {
        TestSRD {
            target: "2100000000000000 sat", // Amount::MAX
            fee_rate: "10 sat/kwu",
            weighted_utxos: &["1 cBTC/68 vB"],
            expected_utxos: &[],
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_utxo_pool_sum_overflow() {
        TestSRD {
            target: "1 cBTC",
            fee_rate: "0",
            weighted_utxos: &["2100000000000000 sats/68 vB", "1 sats/68 vB"], // [Amount::MAX, ,,]
            expected_utxos: &[],
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_proptest() {
        arbtest(|u| {
            let pool = UtxoPool::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let fee_rate = FeeRate::arbitrary(u)?;

            let result: Option<_> = select_coins_srd(target, fee_rate, &pool.utxos, &mut get_rng());

            if let Some((i, utxos)) = result {
                assert!(i > 0);
                crate::tests::assert_target_selection(&utxos, fee_rate, target, None);
            } else {
                let available_value = pool.available_value(fee_rate);
                assert!(available_value.is_none() || available_value.unwrap() < target.to_signed());
            }

            Ok(())
        });
    }
}
