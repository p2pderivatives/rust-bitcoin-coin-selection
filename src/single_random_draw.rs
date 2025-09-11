// SPDX-License-Identifier: CC0-1.0
//
//! Single Random Draw Algorithem.
//!
//! This module introduces the Single Random Draw Coin-Selection Algorithm.

use std::collections::BinaryHeap;

use bitcoin_units::{Amount, CheckedSum, Weight};
use rand::seq::SliceRandom;

use crate::OverflowError::Addition;
use crate::SelectionError::{InsufficentFunds, MaxWeightExceeded, Overflow, ProgramError};
use crate::{Return, WeightedUtxo, CHANGE_LOWER};

/// Randomize the input set and select coins until the target is reached.  If the maximum
/// weight is exceeded, then the least valuable inputs are removed from the selection using weight
/// as a tie breaker.  In so doing, minimize the number of `UTXOs` included in the result by
/// preferring UTXOs with higher value.
///
/// # Parameters
///
/// * `target` - target value to send to recipient.  Include the fee to pay for
///   the known parts of the transaction excluding the fee for the inputs.
/// * `max_weight` - the maximum selection `Weight` allowed.
/// * `weighted_utxos` - Weighted UTXOs from which to sum the target amount.
/// * `rng` - used primarily by tests to make the selection deterministic.
///
/// # Errors
///
/// If an arithmetic overflow occurs, the target can't be reached, or an un-expected error occurs.
/// Note that if sufficient funds are supplied, and an overflow does not occur, then a solution
/// should always be found.  Anything else would be an un-expected program error.
pub fn select_coins_srd<'a, R: rand::Rng + ?Sized>(
    target: Amount,
    max_weight: Weight,
    weighted_utxos: &'a [WeightedUtxo],
    rng: &mut R,
) -> Return<'a> {
    let _ = weighted_utxos
        .iter()
        .map(|u| u.weight())
        .try_fold(Weight::ZERO, Weight::checked_add)
        .ok_or(Overflow(Addition))?;

    let available_value = weighted_utxos
        .iter()
        .map(|u| u.effective_value())
        .checked_sum()
        .ok_or(Overflow(Addition))?;

    let threshold = target.checked_add(CHANGE_LOWER).ok_or(Overflow(Addition))?;
    if available_value < threshold {
        return Err(InsufficentFunds);
    }

    let mut origin: Vec<_> = weighted_utxos.iter().collect();
    origin.shuffle(rng);
    let mut heap: BinaryHeap<&WeightedUtxo> = BinaryHeap::new();

    let mut value = Amount::ZERO;

    let mut iteration = 0;
    let mut max_tx_weight_exceeded = false;
    let mut weight_total = Weight::ZERO;
    for w_utxo in origin {
        iteration += 1;
        let effective_value = w_utxo.effective_value();
        heap.push(w_utxo);

        value = (value + effective_value).unwrap();

        let utxo_weight = w_utxo.weight();
        weight_total += utxo_weight;

        while weight_total > max_weight {
            max_tx_weight_exceeded = true;

            if let Some(utxo) = heap.pop() {
                let effective_value = utxo.effective_value();
                value = (value - effective_value).unwrap();
                weight_total -= utxo.weight();
            };
        }

        if value >= threshold {
            let result: Vec<_> = heap.into_sorted_vec();
            return Ok((iteration, result));
        }
    }

    if max_tx_weight_exceeded {
        Err(MaxWeightExceeded)
    } else {
        // This should never be reached.
        // Either there is not enough funds, or an overflow occurred.
        // If neither of those two things occurred, then a solution should be found.
        Err(ProgramError)
    }
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
    use crate::tests::{assert_ref_eq, parse_fee_rate, Selection};

    #[derive(Debug)]
    pub struct TestSRD<'a> {
        target: &'a str,
        fee_rate: &'a str,
        max_weight: &'a str,
        weighted_utxos: &'a [&'a str],
        expected_utxos: &'a [&'a str],
        expected_error: Option<crate::SelectionError>,
        expected_iterations: u32,
    }

    impl TestSRD<'_> {
        fn assert(&self) {
            let target = Amount::from_str(self.target).unwrap();
            let fee_rate = parse_fee_rate(self.fee_rate);
            let lt_fee_rate = fee_rate;
            let max_weight: Vec<_> = self.max_weight.split(" ").collect();
            let max_weight = Weight::from_str(max_weight[0]).unwrap();

            let candidate_selection = Selection::new(self.weighted_utxos, fee_rate, lt_fee_rate);

            let result =
                select_coins_srd(target, max_weight, &candidate_selection.utxos, &mut get_rng());

            match result {
                Ok((iterations, inputs)) => {
                    assert_eq!(iterations, self.expected_iterations);
                    let expected_selection =
                        Selection::new(self.expected_utxos, fee_rate, lt_fee_rate);
                    assert_ref_eq(inputs, expected_selection.utxos);
                }
                Err(e) => {
                    let expected_error = self.expected_error.clone().unwrap();
                    assert!(self.expected_utxos.is_empty());
                    assert_eq!(e, expected_error);
                }
            }
        }
    }

    fn assert_coin_select(target_str: &str, expected_iterations: u32, expected_utxos: &[&str]) {
        TestSRD {
            target: target_str,
            fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/204 wu", "2 cBTC/204 wu"],
            expected_utxos,
            expected_error: None,
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
    fn select_coins_srd_with_solution() {
        assert_coin_select("1.5 cBTC", 1, &["2 cBTC/204 wu"]);
    }

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
            max_weight: "40000 wu",
            weighted_utxos: &["1.5 cBTC"],
            expected_utxos: &["1.5 cBTC"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_no_solution() {
        TestSRD {
            target: "4 cBTC",
            fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB"],
            expected_utxos: &[],
            expected_error: Some(InsufficentFunds),
            expected_iterations: 0,
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
            max_weight: "40000 wu",
            weighted_utxos: &["e(1 cBTC)/68 vB", "e(2 cBTC)/68 vB"],
            expected_utxos: &[],
            expected_error: Some(InsufficentFunds),
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
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/68 vB", "2050000 sats/68 vB"],
            expected_utxos: &["2050000 sats/68 vB", "1 cBTC/68 vB"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_threshold_overflow() {
        TestSRD {
            target: "2100000000000000 sat", // Amount::MAX
            fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/68 vB"],
            expected_utxos: &[],
            expected_error: Some(Overflow(Addition)),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_utxo_pool_sum_overflow() {
        TestSRD {
            target: "1 cBTC",
            fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["2100000000000000 sats/68 vB", "1 sats/68 vB"], // [Amount::MAX, ,,]
            expected_utxos: &[],
            expected_error: Some(Overflow(Addition)),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_utxo_pool_weight_overflow() {
        TestSRD {
            target: "1 cBTC",
            fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["1 sats/18446744073709551615 wu", "1 sats/1 wu"], // [Amount::MAX, ,,]
            expected_utxos: &[],
            expected_error: Some(Overflow(Addition)),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_max_weight_error() {
        // No solution is less than `max_weight`.
        TestSRD {
            target: "16 cBTC",
            fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["e(3 cBTC)/68 vB", "e(5 cBTC)/10000 vB", "e(9 cBTC)/68 vB"],
            expected_utxos: &[],
            expected_error: Some(MaxWeightExceeded),
            expected_iterations: 5,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_max_weight_eff_value() {
        TestSRD {
            target: "10000 sats", //threshold = 60k sats
            fee_rate: "10 sat/kwu",
            max_weight: "1000 wu",
            // after rand: [30k sats/500 wu, 29,999 sats/700 wu, 30k sats/500 wu]
            weighted_utxos: &[
                "e(30000 sats)/500 wu",
                "e(30000 sats)/500 wu",
                "e(29999 sats)/700 wu",
            ],
            expected_utxos: &["e(30000 sats)/500 wu", "e(30000 sats)/500 wu"],
            expected_error: None,
            expected_iterations: 3,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_max_weight_eff_value_tie() {
        TestSRD {
            target: "10000 sats", // threshold = 60k sats
            fee_rate: "10 sat/kwu",
            max_weight: "1000 wu",
            // after rand: [30k sats/500 wu, 30k sats/700 wu, 30k sats/500 wu]
            weighted_utxos: &[
                "e(30000 sats)/500 wu",
                "e(30000 sats)/500 wu",
                "e(30000 sats)/700 wu",
            ],
            expected_utxos: &["e(30000 sats)/500 wu", "e(30000 sats)/500 wu"],
            expected_error: None,
            expected_iterations: 3,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_proptest() {
        arbtest(|u| {
            let candidate = Selection::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let max_weight = Weight::arbitrary(u)?;

            let utxos = candidate.utxos.clone();
            let result: Result<_, _> = select_coins_srd(target, max_weight, &utxos, &mut get_rng());

            match result {
                Ok((i, utxos)) => {
                    assert!(i > 0);
                    crate::tests::assert_target_selection(&utxos, target, None);
                }
                Err(InsufficentFunds) => {
                    let available_value = candidate.available_value().unwrap();
                    assert!(available_value < (target + CHANGE_LOWER).unwrap());
                }
                Err(crate::SelectionError::IterationLimitReached) => panic!("un-expected result"),
                Err(MaxWeightExceeded) => {
                    let weight_total = candidate.weight_total().unwrap();
                    assert!(weight_total > max_weight);
                }
                Err(Overflow(_)) => {
                    let available_value = candidate.available_value();
                    let weight_total = candidate.weight_total();
                    assert!(
                        available_value.is_none()
                            || weight_total.is_none()
                            || target.checked_add(CHANGE_LOWER).is_none()
                    );
                }
                Err(ProgramError) => panic!("un-expected program error"),
                Err(crate::SelectionError::SolutionNotFound) => panic!("un-expected result"),
            }

            Ok(())
        });
    }
}
