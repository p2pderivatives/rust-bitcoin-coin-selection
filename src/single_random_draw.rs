// SPDX-License-Identifier: CC0-1.0
//
//! Single Random Draw Algorithem.
//!
//! This module introduces the Single Random Draw Coin-Selection Algorithm.

use std::collections::BinaryHeap;

use bitcoin_units::{Amount, FeeRate, Weight};
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
use rand::seq::SliceRandom;

use crate::weighted_utxo::WeightedUtxo;
use crate::OverflowError::Addition;
use crate::SelectionError::{InsufficentFunds, Overflow};
use crate::{Return, SelectionError, Spendable};

/// Select coins by Single Random Draw (SRD).
///
/// SRD selects eligible Outputs from a shuffled ordering until the effective value of the input
/// set suffices to create the recipient outputs and a change output with an amount of at least
/// `CHANGE_LOWER`. While the maximum selection weight is exceeded during selection, the Output with
/// the lowest effective value is dropped from the selection before additional Output are selected.
/// Due to this greedy approach, SRD can fail to discover possible solutions in pathological cases.
///
/// # Parameters
///
/// * `target` - target value to send to recipient.  Include the fee to pay for
///   the known parts of the transaction excluding the fee for the inputs.
/// * `max_weight` - the maximum selection `Weight` allowed.
/// * `rng` - used primarily by tests to make the selection deterministic.
/// * `spendable_coins` - the spendable coins from which to sum the `target` amount to.
///
/// # Returns
///
/// A Result type where the success case is `(u32, Vec<&'a T>`, otherwise, an error case of `SelectionError`.
/// `u32` is the number iterations to find the solution and `Vec<&'a T>` is the randomly found selection.
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn single_random_draw<'a, R: rand::Rng + ?Sized, T: Spendable>(
    target: Amount,
    max_weight: Weight,
    fee_rate: FeeRate,
    rng: &mut R,
    spendable_coins: &'a [T],
) -> Return<'a, T> {
    let mut weighted_utxos: Vec<_> =
        WeightedUtxo::from_spendables(spendable_coins, fee_rate, FeeRate::ZERO);

    let (available_value, _) = weighted_utxos
        .iter()
        .map(|u| (u.effective_value, u.weight))
        .try_fold((0u64, Weight::ZERO), |acc, u| {
            let amount = acc.0.checked_add(u.0);
            let weight = acc.1.checked_add(u.1);

            if let Some(a) = amount {
                if let Some(w) = weight {
                    if a <= Amount::MAX.to_sat() {
                        return Some((a, w));
                    }
                }
            }
            None
        })
        .ok_or(Overflow(Addition))?;

    if available_value < target.to_sat() {
        return Err(InsufficentFunds);
    }

    weighted_utxos.shuffle(rng);
    let (iters, selected, weight_exceeded) =
        srd_select(target.to_sat(), max_weight, &weighted_utxos);
    let result = selected.into_iter().map(|i| &spendable_coins[i]).collect();
    SelectionError::srd_handler(result, iters, weight_exceeded)
}

#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
fn srd_select(
    target: u64,
    max_weight: Weight,
    weighted_utxos: &[WeightedUtxo],
) -> (u32, Vec<usize>, bool) {
    let mut heap: BinaryHeap<_> = BinaryHeap::new();
    let mut value = 0;
    let mut iteration = 0;
    let mut weight_exceeded = false;
    let mut weight_total = Weight::ZERO;

    let mut result = vec![];
    for w_utxo in weighted_utxos {
        iteration += 1;
        let effective_value = w_utxo.effective_value;
        heap.push(w_utxo);

        value += effective_value;

        let utxo_weight = w_utxo.weight;
        weight_total += utxo_weight;

        while weight_total > max_weight {
            weight_exceeded = true;

            if let Some(utxo) = heap.pop() {
                let effective_value = utxo.effective_value;
                value -= effective_value;
                weight_total -= utxo.weight;
            };
        }

        if value >= target {
            result = heap.iter().map(|u| u.spendable_index).collect();
            return (iteration, result, weight_exceeded);
        }
    }

    (iteration, result, weight_exceeded)
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use arbitrary::Arbitrary;
    use arbtest::arbtest;
    use bitcoin_units::Amount;
    use rand::rngs::mock::StepRng;

    use super::*;
    use crate::single_random_draw::single_random_draw;
    use crate::tests::{
        assert_ref_eq, effective_sum, parse_fee_rate, utxos_from_str, weight_sum, Pool,
    };
    use crate::SelectionError::{MaxWeightExceeded, ProgramError, SolutionNotFound};

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
            let max_weight: Vec<_> = self.max_weight.split(" ").collect();
            let max_weight = Weight::from_str(max_weight[0]).unwrap();

            let utxos = utxos_from_str(self.weighted_utxos, fee_rate);

            let result = single_random_draw(target, max_weight, fee_rate, &mut get_rng(), &utxos);

            match result {
                Ok((iterations, inputs)) => {
                    assert_eq!(iterations, self.expected_iterations);
                    let utxos = utxos_from_str(self.expected_utxos, fee_rate);
                    assert_ref_eq(inputs, utxos);
                }
                Err(e) => {
                    let expected_error = self.expected_error.clone();
                    if let Some(err) = expected_error {
                        assert_eq!(e, err);
                    } else {
                        println!("got: {:?} expected {:?}", e, expected_error);
                    }
                    assert!(self.expected_utxos.is_empty());
                    assert!(self.expected_iterations == 0);
                }
            }
        }
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
        TestSRD {
            target: "1.5 cBTC",
            fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/204 wu", "2 cBTC/204 wu"],
            expected_utxos: &["2 cBTC/204 wu"],
            expected_error: None,
            expected_iterations: 1,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_all_solution() {
        TestSRD {
            target: "2.5 cBTC",
            fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/204 wu", "2 cBTC/204 wu"],
            expected_utxos: &["1 cBTC/204 wu", "2 cBTC/204 wu"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
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
    fn select_coins_srd_with_high_fee() {
        // Both UTXOs are selected since neither has enough effective_value individually
        TestSRD {
            target: "2 cBTC",
            fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB"],
            expected_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_utxo_pool_sum_overflow() {
        TestSRD {
            target: "1 cBTC",
            fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["21000000 BTC/68 vB", "1 sats/68 vB"], // [Amount::MAX, ,,]
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
            weighted_utxos: &["1 sats/18446744073709551615 wu", "1 sats/164 wu"], // [Weight::MAX, Weight::MIN]
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
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_max_weight_eff_value() {
        TestSRD {
            target: "60000 sats",
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
            target: "60000 sats",
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
    fn select_coins_srd_exceed_max_weight_with_solution() {
        TestSRD {
            target: "7 sats",
            fee_rate: "10 sat/kwu",
            max_weight: "460 wu",
            // after rand: [2, 3, 5]
            weighted_utxos: &["e(5 sats)/230 wu", "e(2 sats)/230 wu", "e(3 sats)/230 wu"],
            expected_utxos: &["e(3 sats)/230 wu", "e(5 sats)/230 wu"],
            expected_error: None,
            expected_iterations: 3,
        }
        .assert();
    }

    #[test]
    fn select_coins_srd_proptest() {
        arbtest(|u| {
            let pool = Pool::arbitrary(u)?;

            let target = Amount::arbitrary(u)?;
            let max_weight = Weight::arbitrary(u)?;
            let fee_rate = FeeRate::arbitrary(u)?;

            let result: Result<_, _> =
                single_random_draw(target, max_weight, fee_rate, &mut get_rng(), &pool.utxos);

            match result {
                Ok((i, utxos)) => {
                    assert!(i > 0);
                    let utxos: Vec<_> = utxos.iter().map(|&u| u.clone()).collect();
                    let eff_value_sum = effective_sum(&utxos, fee_rate).unwrap();
                    assert!(eff_value_sum >= target);
                }
                Err(InsufficentFunds) => {
                    assert!(
                        effective_sum(&pool.utxos, fee_rate).unwrap() < target
                            || effective_sum(&pool.utxos, fee_rate).unwrap() == Amount::ZERO
                    );
                }
                Err(crate::SelectionError::IterationLimitReached) => panic!("un-expected result"),
                Err(MaxWeightExceeded) => {
                    assert!(weight_sum(&pool.utxos).unwrap() > max_weight);
                }
                Err(Overflow(_)) => {
                    assert!(
                        effective_sum(&pool.utxos, fee_rate).is_none()
                            || weight_sum(&pool.utxos).is_none()
                    );
                }
                Err(SolutionNotFound) => assert!(target == Amount::ZERO),
                Err(ProgramError) => panic!("un-expected program error"),
            }

            Ok(())
        });
    }
}
