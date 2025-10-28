// SPDX-License-Identifier: CC0-1.0
//
//! Bitcoin Branch and Bound Coin Selection.
//!
//! This module introduces the Branch and Bound Coin-Selection Algorithm.

use bitcoin_units::{Amount, Weight};

use crate::OverflowError::Addition;
use crate::SelectionError::{
    InsufficentFunds, IterationLimitReached, MaxWeightExceeded, Overflow, SolutionNotFound,
};
use crate::{Return, WeightedUtxo};

// Total_Tries in Core:
// https://github.com/bitcoin/bitcoin/blob/1d9da8da309d1dbf9aef15eb8dc43b4a2dc3d309/src/wallet/coinselection.cpp#L74
pub const ITERATION_LIMIT: u32 = 100_000;

// The sum of UTXO amounts after this UTXO index, e.g. lookahead[5] = Σ(UTXO[6+].amount)
fn build_lookahead(lookahead: Vec<&WeightedUtxo>, available_value: Amount) -> Vec<Amount> {
    lookahead
        .iter()
        .map(|u| u.effective_value())
        .scan(available_value, |state, u| {
            *state = (*state - u).unwrap();
            Some(*state)
        })
        .collect()
}

/// Deterministic depth first branch and bound search for a changeless solution.
///
/// A changeless solution is one that exceeds the target amount and is less than target amount plus
/// cost of creating change.  In other words, a changeless solution is a solution where it is less expensive
/// to discard the excess amount (amount over the target) than it is to create a new output
/// containing the change.
///
/// # Parameters
///
/// * target: Target spend `Amount`
/// * cost_of_change: The `Amount` needed to produce a change output
/// * max_weight: the maximum selection `Weight` allowed.
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from
///
/// # Returns
///
/// A tuple `(u32, Vec<&'a WeightedUtxo>` is returned on success where `u32` is the number of
/// iterations to find the solution and `Vec<&'a WeightedUtxo>` is the best found selection.
/// Note that if the iteration count equals `ITERATION_LIMIT`, a better solution may exist than the
/// one found.
// This search explores a binary tree.  The left branch of each node is the inclusion branch and
// the right branch is the exclusion branch.
//      o
//     / \
//    I   E
//
// If the UTXO set consist of a list: [4,3,2,1], and the target is 5, the selection process works
// as follows:
//
// Add 4 to the inclusion branch.  The current total is 4 which is less than our target of 5,
// therefore the search routine continues.  The next UTXO 3 is added to the inclusion branch.
//      o
//     /
//    4
//   /
//  3
//
// At this point, the total sums to 7 (4 + 3) exceeding the target of 5.  7 may be recorded as a
// solution with an excess of 2 (7 - 5). 3 is removed from the left branch and it becomes
// the right branch since 3 is now excluded.
//      o
//     /
//    4
//     \
//      3
//
// We next try add 2 to the inclusion branch.
//      o
//     /
//    4
//     \
//      3
//     /
//    2
//
// The sum of the left inclusion branch is now 6 (4 + 2).  Once again, we find the total
// exceeds 5, so we record 6 as a solution with an excess of 1, our best solution so far.
// Once again, we add 2 to the exclusion branch.
//      o
//     /
//    4
//     \
//      3
//       \
//        2
//
// Finally, we add 1 to the inclusion branch.  This ends our depth first search by matching two
// conditions, it is both the leaf node (no more available value) and matches our search criteria of
// 5 with the smallest possible excess (0).  Both 4 and 1 are on the left inclusion branch.
//
//      o
//     / \
//    4
//     \
//      3
//       \
//        2
//       /
//      1
//
// The search continues because it is possible to do better than 0 (more on that later).
// We next try excluding 4 by adding 4 to the exclusion branch, then we begin a new search
// tree by adding 3 to the inclusion branch.
//      o
//       \
//        4
//       /
//      3
//
// 3 is less than our target, so we next add 2 to our inclusion branch.
//      o
//       \
//        4
//       /
//      3
//     /
//    2
//
// We now stop our search again noticing that 3 and 2 equals our target as 5, and since this
// solution was found last, [3, 2] overwrites the previously found solution [4, 1].  We haven't
// tried combinations including 1 at this point, however adding 1 to [3, 2, 1] would be a worse
// solution since it overshoots the target of 5, so the combination is dismissed.  Furthermore,
// removing 2 would not leave enough available value [3, 1] to make it to our target, therefore
// the search routine has exhausted all possibilities using 3 as the root. We next backtrack and
// exclude our root node of this tree 3.  Since our new sub tree starting at 2 doesn't have enough
// value left to meet the target, we conclude our search at [3, 2].
//
// * Addendum on Waste Calculation Optimization *
// Waste, like accumulated value, is a bound used to track when a search path is no longer
// advantageous.  The waste total is accumulated and stored in a variable called current_waste.
// Besides the difference between amount and target, current_waste stores the difference between
// utxo fee and utxo_long_term_fee.
//
// If the iteration adds a new node to the inclusion branch, besides incrementing the accumulated
// value for the node, the waste is also added to the current_waste.  Note that unlike value,
// waste can actually be negative.  This happens if there is a low fee environment such that
// fee is less than long_term_fee.  Therefore, the only case where a solution becomes more
// wasteful, and we may bound our search because a better waste score is no longer possible is:
//
//  1) We have already found a solution that matches the target and the next solution has a
//  higher waste score.
//
//  2) It's a high fee environment such that adding more utxos will increase current_waste.
//
// If either 1 or 2 is true, we consider the current search path no longer viable to continue.  In
// such a case, backtrack to start a new search path.
pub fn branch_and_bound<'a, T: IntoIterator<Item = &'a WeightedUtxo> + std::marker::Copy>(
    target: Amount,
    cost_of_change: Amount,
    max_weight: Weight,
    weighted_utxos: T,
) -> Return<'a> {
    weighted_utxos
        .into_iter()
        .map(|u| u.weight())
        .try_fold(Weight::ZERO, Weight::checked_add)
        .ok_or(Overflow(Addition))?;

    let available_value: Amount = weighted_utxos
        .into_iter()
        .map(|u| u.effective_value())
        .try_fold(Amount::ZERO, Amount::checked_add)
        .ok_or(Overflow(Addition))?;

    let mut weighted_utxos: Vec<_> = weighted_utxos.into_iter().collect();

    // TODO add this restriction to UtxoPool
    if weighted_utxos.len() < 1 {
        return Err(SolutionNotFound)
    }

    // descending sort by effective_value, ascending sort by waste.
    weighted_utxos.sort_by(|a, b| {
        b.effective_value().cmp(&a.effective_value()).then(a.waste().cmp(&b.waste()))
    });

    let lookahead = build_lookahead(weighted_utxos.clone(), available_value);

    if available_value < target {
        return Err(InsufficentFunds);
    }

    let mut selection: Vec<usize> = vec![];
    let mut best_selection: Vec<usize> = vec![];

    let mut selection_amount = Amount::ZERO;

    let mut selection_waste = crate::SignedAmount::ZERO;
    let mut best_waste = crate::SignedAmount::MAX_MONEY;

    let mut selection_weight = Weight::ZERO;

    let mut max_tx_weight_exceeded = false;

    let mut next_utxo_index = 0;

    let mut iteration: u32 = 0;

    let upper_bound = (target + cost_of_change).ok().ok_or(Overflow(Addition))?;

    while iteration < ITERATION_LIMIT {
        let mut shift = false;
        let mut cut = false;

        let utxo = weighted_utxos[next_utxo_index];
        selection_amount = (selection_amount + utxo.effective_value()).unwrap();
        selection_weight += utxo.weight();
        selection_waste = (selection_waste + utxo.waste()).unwrap();
        selection.push(next_utxo_index);
        next_utxo_index += 1;
        iteration += 1;

        let tail: usize = *selection.last().unwrap();
        if (selection_amount + lookahead[tail]).unwrap() < target {
            cut = true;
        } else if selection_weight > max_weight {
            max_tx_weight_exceeded = true;
            shift = true;
        } else if selection_amount > upper_bound {
            shift = true;
        } else if weighted_utxos[0].is_fee_expensive() && selection_waste > best_waste {
            shift = true;
        } else if selection_amount >= target {
            shift = true;
            let excess = (selection_amount - target).unwrap();
            selection_waste = (selection_waste + excess.to_signed()).unwrap();
            if selection_waste <= best_waste {
                best_selection = selection.clone();
                best_waste = selection_waste;
            }
        }

        if next_utxo_index == weighted_utxos.len() {
            cut = true;
        }

        if cut {
            // deselect
            let tail: usize = *selection.last().unwrap();
            let utxo = weighted_utxos[tail];
            selection_amount = (selection_amount - utxo.effective_value()).unwrap();
            selection_weight -= utxo.weight();
            selection_waste = (selection_waste - utxo.waste()).unwrap();
            selection.pop();

            shift = true;
        }

        while shift {
            if selection.is_empty() {
                return index_to_utxo_list(
                    iteration,
                    best_selection,
                    max_tx_weight_exceeded,
                    weighted_utxos,
                );
            }

            let tail: usize = *selection.last().unwrap();
            next_utxo_index = tail + 1;

            // deselect
            let tail: usize = *selection.last().unwrap();
            let utxo = weighted_utxos[tail];
            selection_amount = (selection_amount - utxo.effective_value()).unwrap();
            selection_weight -= utxo.weight();
            selection_waste = (selection_waste - utxo.waste()).unwrap();
            selection.pop();

            shift = false;

            while weighted_utxos[next_utxo_index - 1].effective_value() == weighted_utxos[next_utxo_index].effective_value()
            {
                if next_utxo_index >= weighted_utxos.len() - 1 {
                    shift = true;
                    break;
                }
                next_utxo_index += 1;
            }
        }
    }

    index_to_utxo_list(iteration, best_selection, max_tx_weight_exceeded, weighted_utxos)
}

fn index_to_utxo_list<'a>(
    iterations: u32,
    index_list: Vec<usize>,
    max_tx_weight_exceeded: bool,
    wu: Vec<&'a WeightedUtxo>,
) -> Return<'a> {
    let mut result: Vec<_> = Vec::new();

    for i in index_list {
        let wu = wu[i];
        result.push(wu);
    }

    if result.is_empty() {
        if iterations == ITERATION_LIMIT {
            Err(IterationLimitReached)
        } else if max_tx_weight_exceeded {
            Err(MaxWeightExceeded)
        } else {
            Err(SolutionNotFound)
        }
    } else {
        Ok((iterations, result))
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;
    use std::iter::{once, zip};

    use arbitrary::{Arbitrary, Result, Unstructured};
    use arbtest::arbtest;
    use bitcoin_units::{Amount, FeeRate, Weight};

    use super::*;
    use crate::tests::{assert_ref_eq, parse_fee_rate, Selection};
    use crate::SelectionError::ProgramError;
    use crate::WeightedUtxo;

    #[derive(Debug)]
    pub struct TestBnB<'a> {
        target: &'a str,
        cost_of_change: &'a str,
        fee_rate: &'a str,
        lt_fee_rate: &'a str,
        max_weight: &'a str,
        weighted_utxos: &'a [&'a str],
        expected_utxos: &'a [&'a str],
        expected_error: Option<crate::SelectionError>,
        expected_iterations: u32,
    }

    impl TestBnB<'_> {
        fn assert(&self) {
            let target = Amount::from_str(self.target).unwrap();
            let cost_of_change = Amount::from_str(self.cost_of_change).unwrap();

            let fee_rate = parse_fee_rate(self.fee_rate);
            let lt_fee_rate = parse_fee_rate(self.lt_fee_rate);
            let max_weight: Vec<_> = self.max_weight.split(" ").collect();
            let max_weight = Weight::from_str(max_weight[0]).unwrap();

            let candidate_selection = Selection::new(self.weighted_utxos, fee_rate, lt_fee_rate);

            let result =
                branch_and_bound(target, cost_of_change, max_weight, &candidate_selection.utxos);

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

    pub struct AssertBnB {
        target: Amount,
        cost_of_change: Amount,
        max_weight: Weight,
        candidate_selection: Selection,
        expected_inputs: Vec<WeightedUtxo>,
    }

    impl AssertBnB {
        fn exec(self) {
            let target = self.target;
            let cost_of_change = self.cost_of_change;
            let max_weight = self.max_weight;
            let candidate_selection = &self.candidate_selection;
            let candidate_utxos = &candidate_selection.utxos;
            let expected_inputs = self.expected_inputs;

            let upper_bound = target.checked_add(cost_of_change);
            let result = branch_and_bound(target, cost_of_change, max_weight, candidate_utxos);

            match result {
                Ok((i, utxos)) => {
                    assert!(i > 0 || target == Amount::ZERO);
                    crate::tests::assert_target_selection(&utxos, target, upper_bound);
                }
                Err(InsufficentFunds) => {
                    let available_value = candidate_selection.available_value().unwrap();
                    assert!(available_value < target);
                }
                Err(IterationLimitReached) => {}
                Err(Overflow(_)) => {
                    let available_value = candidate_selection.available_value();
                    let weight_total = candidate_selection.weight_total();
                    assert!(
                        available_value.is_none()
                            || weight_total.is_none()
                            || upper_bound.is_none()
                    );
                }
                Err(ProgramError) => panic!("un-expected result"),
                Err(SolutionNotFound) => {
                    assert!(expected_inputs.is_empty() || target == Amount::ZERO)
                }
                Err(MaxWeightExceeded) => {
                    let weight_total = candidate_selection.weight_total().unwrap();
                    assert!(weight_total > max_weight);
                }
            }
        }
    }

    fn assert_coin_select(target_str: &str, expected_iterations: u32, expected_utxos: &[&str]) {
        TestBnB {
            target: target_str,
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB", "3 cBTC/68 vB", "4 cBTC/68 vB"],
            expected_utxos,
            expected_error: None,
            expected_iterations,
        }
        .assert();
    }

    impl<'a> Arbitrary<'a> for AssertBnB {
        fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
            let cost_of_change = Amount::arbitrary(u)?;
            let fee_rate = FeeRate::arbitrary(u)?;
            let long_term_fee_rate = FeeRate::arbitrary(u)?;
            let max_weight = Weight::arbitrary(u)?;

            let init: Vec<(Amount, Weight, bool)> = Vec::arbitrary(u)?;
            let expected_inputs: Vec<WeightedUtxo> = init
                .iter()
                .filter(|(_, _, include)| *include)
                .filter_map(|(amt, weight, _)| {
                    WeightedUtxo::new(*amt, *weight, fee_rate, long_term_fee_rate)
                })
                .collect();
            let utxos: Vec<WeightedUtxo> = init
                .iter()
                .filter_map(|(amt, weight, _)| {
                    WeightedUtxo::new(*amt, *weight, fee_rate, long_term_fee_rate)
                })
                .collect();
            let candidate_selection = Selection { utxos, fee_rate, long_term_fee_rate };

            let target_set: Vec<_> = expected_inputs.iter().map(|u| u.effective_value()).collect();

            let target: Amount = target_set
                .clone()
                .into_iter()
                .try_fold(Amount::ZERO, Amount::checked_add)
                .unwrap_or(Amount::ZERO);

            Ok(AssertBnB {
                target,
                cost_of_change,
                max_weight,
                candidate_selection,
                expected_inputs,
            })
        }
    }

    #[test]
    fn select_coins_bnb_one() { assert_coin_select("1 cBTC", 4, &["1 cBTC/68 vB"]); }

    #[test]
    fn select_coins_bnb_two() { assert_coin_select("2 cBTC", 4, &["2 cBTC/68 vB"]); }

    #[test]
    fn select_coins_bnb_three() {
        assert_coin_select("3 cBTC", 5, &["2 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_four() {
        assert_coin_select("4 cBTC", 5, &["3 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_five() {
        assert_coin_select("5 cBTC", 8, &["3 cBTC/68 vB", "2 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_six() {
        assert_coin_select("6 cBTC", 9, &["3 cBTC/68 vB", "2 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_seven() {
        assert_coin_select("7 cBTC", 6, &["4 cBTC/68 vB", "2 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_eight() {
        assert_coin_select("8 cBTC", 6, &["4 cBTC/68 vB", "3 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_nine() {
        assert_coin_select("9 cBTC", 6, &["4 cBTC/68 vB", "3 cBTC/68 vB", "2 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_ten() {
        assert_coin_select(
            "10 cBTC",
            7,
            &["4 cBTC/68 vB", "3 cBTC/68 vB", "2 cBTC/68 vB", "1 cBTC/68 vB"],
        );
    }

    #[test]
    #[should_panic]
    // the target is greater than the sum of available UTXOs.
    // therefore asserting that a selection exists should panic.
    fn select_coins_bnb_eleven_invalid_target_should_panic() {
        assert_coin_select("11 cBTC", 8, &["1 cBTC/68 vB"]);
    }

    #[test]
    #[should_panic]
    fn select_coins_bnb_params_invalid_target_should_panic() {
        // the target is greater than the sum of available UTXOs.
        // therefore asserting that a selection exists should panic.
        TestBnB {
            target: "11 cBTC",
            cost_of_change: "1 cBTC",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["1.5 cBTC/68 vB"],
            expected_utxos: &["1.5 cBTC/68 vB"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_zero() {
        TestBnB {
            target: "0",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/68 vB"],
            expected_utxos: &[],
            expected_error: Some(SolutionNotFound),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_cost_of_change() {
        // A selection that is larger than the target but less then
        // target + cost_of_change will succeed.
        let mut t = TestBnB {
            target: "1 cBTC",
            cost_of_change: "1 cBTC",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["1.5 cBTC/68 vB"],
            expected_utxos: &["1.5 cBTC/68 vB"],
            expected_error: None,
            expected_iterations: 1,
        };

        t.assert();

        // The same target and the same UTXO pool does not succeed with
        // a smaller cost_of_change.
        t.cost_of_change = "0";
        t.expected_utxos = &[];
        t.expected_error = Some(SolutionNotFound);
        t.expected_iterations = 0;
        t.assert();
    }

    #[test]
    fn select_coins_bnb_effective_value() {
        // The effective value of the utxo is less than the target.
        TestBnB {
            target: "1 cBTC",
            cost_of_change: "0",
            fee_rate: "10 sat/kwu",
            lt_fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/68 vB"],
            expected_utxos: &[],
            expected_error: Some(InsufficentFunds),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_target_greater_than_value() {
        TestBnB {
            target: "11 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB", "3 cBTC/68 vB", "4 cBTC/68 vB"],
            expected_utxos: &[],
            expected_error: Some(InsufficentFunds),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_consume_more_inputs_when_cheap() {
        TestBnB {
            target: "6 sats",
            cost_of_change: "0",
            fee_rate: "10 sat/kwu",
            lt_fee_rate: "20 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &[
                "e(1 sats)/68 vB",
                "e(2 sats)/68 vB",
                "e(3 sats)/68 vB",
                "e(4 sats)/68 vB",
            ],
            expected_utxos: &["e(3 sats)/68 vB", "e(2 sats)/68 vB", "e(1 sats)/68 vB"],
            expected_error: None,
            expected_iterations: 9,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_consume_less_inputs_when_expensive() {
        TestBnB {
            target: "6 sats",
            cost_of_change: "0",
            fee_rate: "20 sat/kwu",
            lt_fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &[
                "e(1 sats)/68 vB",
                "e(2 sats)/68 vB",
                "e(3 sats)/68 vB",
                "e(4 sats)/68 vB",
            ],
            expected_utxos: &["e(4 sats)/68 vB", "e(2 sats)/68 vB"],
            expected_error: None,
            expected_iterations: 9,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_consume_less_inputs_with_excess_when_expensive() {
        TestBnB {
            target: "6 sats",
            cost_of_change: "1 sats",
            fee_rate: "20 sat/kwu",
            lt_fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            weighted_utxos: &[
                "e(1 sats)/68 vB",
                "e(2 sats)/68 vB",
                "e(3 sats)/68 vB",
                "e(4 sats)/68 vB",
            ],
            expected_utxos: &["e(4 sats)/68 vB", "e(2 sats)/68 vB"],
            expected_error: None,
            expected_iterations: 9,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_utxo_pool_sum_overflow() {
        // Adding all UTXOs together to find the available value overflows.
        TestBnB {
            target: "1 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["2100000000000000 sats/68 vB", "1 sats/68 vB"], // [Amount::MAX, ,,]
            expected_utxos: &[],
            expected_error: Some(Overflow(Addition)),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_upper_bound_overflow() {
        // Adding cost_of_change to the target (upper bound) overflows.
        TestBnB {
            target: "1 sats",
            cost_of_change: "2100000000000000 sats", // u64::MAX
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["e(1 sats)/68 vB"],
            expected_utxos: &[],
            expected_error: Some(Overflow(Addition)),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_effective_value_tie_high_fee_rate() {
        // If the fee_rate is expensive prefer lower weight UTXOS
        // if the effective_values are equal.
        // p2wpkh weight = 272 wu
        // p2tr weight = 230 wu
        TestBnB {
            target: "100 sats",
            cost_of_change: "10 sats",
            fee_rate: "20 sat/kwu",
            lt_fee_rate: "10 sat/kwu",
            max_weight: "40000 wu",
            // index [0, 2] is skippped because of the utxo skip optimization.
            // [0, 1] is recorded, and next [0, 2] is skipped because after recording
            // [0, 1] then [0, 2] does not need to be tried since it's recognized that
            // it is the same effective_value as [0, 1].
            weighted_utxos: &["e(50 sats)/230 wu", "e(50 sats)/272 wu", "e(50 sats)/230 wu"],
            expected_utxos: &["e(50 sats)/230 wu", "e(50 sats)/230 wu"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_effective_value_tie_low_fee_rate() {
        // If the fee_rate is expensive prefer lower weight UTXOS
        // if the effective_values are equal.
        // p2wpkh weight = 272 wu
        // p2tr weight = 230 wu
        TestBnB {
            target: "100 sats",
            cost_of_change: "10 sats",
            fee_rate: "10 sat/kwu",
            lt_fee_rate: "20 sat/kwu",
            max_weight: "40000 wu",
            // index [0, 2] is skippped because of the utxo skip optimization.
            // [0, 1] is recorded, and next [0, 2] is skipped because after recording
            // [0, 1] then [0, 2] does not need to be tried since it's recognized that
            // it is the same effective_value as [0, 1].
            weighted_utxos: &["e(50 sats)/272 wu", "e(50 sats)/230 wu", "e(50 sats)/272 wu"],
            expected_utxos: &["e(50 sats)/272 wu", "e(50 sats)/272 wu"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_set_size_five() {
        TestBnB {
            target: "6 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &[
                "3 cBTC/68 vB",
                "2.9 cBTC/68 vB",
                "2 cBTC/68 vB",
                "1.0 cBTC/68 vB",
                "1 cBTC/68 vB",
            ],
            expected_utxos: &["3 cBTC/68 vB", "2 cBTC/68 vB", "1 cBTC/68 vB"],
            expected_error: None,
            expected_iterations: 13,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_set_size_seven() {
        TestBnB {
            target: "18 cBTC",
            cost_of_change: "50 sats",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &[
                "10 cBTC/68 vB",
                "7000005 sats/68 vB",
                "6000005 sats/68 vB",
                "6 cBTC/68 vB",
                "3 cBTC/68 vB",
                "2 cBTC/68 vB",
                "1000005 cBTC/68 vB",
            ],
            expected_utxos: &["10 cBTC/68 vB", "6 cBTC/68 vB", "2 cBTC/68 vB"],
            expected_error: None,
            expected_iterations: 27,
        }
        .assert();
    }

    //#[test]
    //fn select_coins_bnb_early_bail_optimization() {
        // Test the UTXO exclusion shortcut optimization.  The selection begins with
        // 7 * 4 = 28 cBTC.  Next, since the pool is sorted in descending order,
        // 5 cBTC is added which is above the target of 30.   If the UTXO exclusion
        // shortcut works, all next 5 cBTC values will be skipped since they have
        // the same effective_value and 5 cBTC was excluded.  Otherwise, trying all
        // combination of 5 cBTC will cause the iteration limit to be reached before
        // finding 2 cBTC which matches the total exactly.
        //let mut utxos =
            //vec!["7 cBTC/68 vB", "7 cBTC/68 vB", "7 cBTC/68 vB", "7 cBTC/68 vB", "2 cBTC/68 vB"];
        //for _i in 0..50_000 {
            //utxos.push("5 cBTC/68 vB");
        //}
        //TestBnB {
            //target: "30 cBTC",
            //cost_of_change: "5000 sats",
            //fee_rate: "0",
            //lt_fee_rate: "0",
            //max_weight: "40000 wu",
            //weighted_utxos: &utxos,
            //expected_utxos: &[
                //"7 cBTC/68 vB",
                //"7 cBTC/68 vB",
                //"7 cBTC/68 vB",
                //"7 cBTC/68 vB",
                //"2 cBTC/68 vB",
            //],
            //expected_error: None,
            //expected_iterations: 100_000,
        //}
        //.assert();
    //}

    #[test]
    fn select_coins_bnb_max_weight_yields_no_solution() {
        TestBnB {
            target: "16 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000",
            weighted_utxos: &[
                "10 cBTC/68 vB",
                "9 cBTC/68 vB",
                "8 cBTC/68 vB",
                "5 cBTC/10000 vB",
                "3 cBTC/68 vB",
                "1 cBTC/68 vB",
            ],
            expected_utxos: &[],
            expected_error: Some(MaxWeightExceeded),
            expected_iterations: 26,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_max_weight_without_error() {
        TestBnB {
            target: "1 cBTC",
            cost_of_change: "1000 sats",
            fee_rate: "10 sat/kwu",
            lt_fee_rate: "20 sat/kwu",
            max_weight: "40000",
            weighted_utxos: &["e(2 cBTC)/30000 wu", "e(1 cBTC)/20000 wu"],
            expected_utxos: &["e(1 cBTC)/20000 wu"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_utxo_pool_weight_overflow() {
        TestBnB {
            target: "1 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &["1 sats/18446744073709551615 wu", "1 sats/1 wu"], // [Amount::MAX, ,,]
            expected_utxos: &[],
            expected_error: Some(Overflow(Addition)),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_exhaust() {
        // Recreate make_hard from bitcoin core test suit.
        // Takes 327,661 iterations to find a solution.
        let base: usize = 2;
        let alpha = (0..17).enumerate().map(|(i, _)| base.pow(17 + i as u32));
        let target = Amount::from_sat_u32(alpha.clone().sum::<usize>() as u32);
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;
        let max_weight = Weight::from_wu(40_000);

        let beta = (0..17).enumerate().map(|(i, _)| {
            let a = base.pow(17 + i as u32);
            let b = base.pow(16 - i as u32);
            a + b
        });

        let amts: Vec<_> = zip(alpha, beta)
            // flatten requires iterable types.
            // use once() to make tuple iterable.
            .flat_map(|tup| once(tup.0).chain(once(tup.1)))
            .map(|a| Amount::from_sat_u32(a as u32))
            .collect();

        let pool: Vec<_> = amts
            .into_iter()
            .filter_map(|a| WeightedUtxo::new(a, Weight::ZERO, fee_rate, lt_fee_rate))
            .collect();

        let result = branch_and_bound(target, Amount::ONE_SAT, max_weight, &pool);

        match result {
            Err(IterationLimitReached) => {}
            _ => panic!(),
        }
    }

    //#[test]
    //fn select_coins_bnb_exhaust_v2() {
        // Takes 163,819 iterations to find a solution.
        //let base: u32 = 2;
        //let mut target = 0;
        //let max_weight = Weight::from_wu(40_000);
        //let vals = (0..15).enumerate().flat_map(|(i, _)| {
            //let a = base.pow(15 + i as u32);
            //target += a;
            //vec![a, a + 2]
        //});
        //let fee_rate = FeeRate::ZERO;
        //let lt_fee_rate = FeeRate::ZERO;

        //let amts: Vec<_> = vals.map(Amount::from_sat_u32).collect();
        //let pool: Vec<_> = amts
            //.into_iter()
            //.filter_map(|a| WeightedUtxo::new(a, Weight::ZERO, fee_rate, lt_fee_rate))
            //.collect();

        //let result =
            //branch_and_bound(Amount::from_sat_u32(target), Amount::ONE_SAT, max_weight, &pool);

        //match result {
            //Err(IterationLimitReached) => {}
            //_ => panic!(),
        //}
    //}

    //#[test]
    //fn select_coins_bnb_exhaust_with_result() {
        // This returns a result AND hits the iteration exhaust limit.
        // Takes 163,819 iterations (hits the iteration limit).
        //let base: u32 = 2;
        //let mut target = 0;
        //let max_weight = Weight::from_wu(40_000);
        //let amts = (0..15).enumerate().flat_map(|(i, _)| {
            //let a = base.pow(15 + i as u32);
            //target += a;
            //vec![a, a + 2]
        //});
        //let fee_rate = FeeRate::ZERO;
        //let lt_fee_rate = FeeRate::ZERO;

        //let mut amts: Vec<_> = amts.map(Amount::from_sat_u32).collect();

        // Add a value that will match the target before iteration exhaustion occurs.
        //amts.push(Amount::from_sat_u32(target));
        //let pool: Vec<_> = amts
            //.into_iter()
            //.filter_map(|a| WeightedUtxo::new(a, Weight::ZERO, fee_rate, lt_fee_rate))
            //.collect();

        //let (iterations, utxos) =
            //branch_and_bound(Amount::from_sat_u32(target), Amount::ONE_SAT, max_weight, &pool)
                //.unwrap();

        //assert_eq!(utxos.len(), 1);
        //assert_eq!(utxos[0].value(), Amount::from_sat_u32(target));
        //assert_eq!(100000, iterations);
    //}

    #[test]
    fn select_coins_bnb_solution_proptest() {
        arbtest(|u| {
            let assert_bnb = AssertBnB::arbitrary(u)?;
            assert_bnb.exec();

            Ok(())
        });
    }

    #[test]
    fn select_coins_bnb_thrifty_proptest() {
        arbtest(|u| {
            let candidate_selection = Selection::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let cost_of_change = Amount::arbitrary(u)?;
            let fee_rate_a = candidate_selection.fee_rate;
            let fee_rate_b = candidate_selection.long_term_fee_rate;
            let max_weight = Weight::MAX;
            let candidate_utxos = candidate_selection.utxos;

            let result_a = branch_and_bound(target, cost_of_change, max_weight, &candidate_utxos);

            let utxo_selection_attributes =
                candidate_utxos.clone().into_iter().map(|u| (u.value(), u.weight()));
            // swap lt_fee_rate and fee_rate position.
            let utxos_b: Vec<WeightedUtxo> = utxo_selection_attributes
                .filter_map(|(amt, weight)| WeightedUtxo::new(amt, weight, fee_rate_b, fee_rate_a))
                .collect();
            let result_b = branch_and_bound(target, cost_of_change, max_weight, &utxos_b);

            if let Ok((_, utxos_a)) = result_a {
                if let Ok((_, utxos_b)) = result_b {
                    let weight_sum_a = utxos_a
                        .iter()
                        .map(|u| u.weight())
                        .try_fold(Weight::ZERO, Weight::checked_add);
                    let weight_sum_b = utxos_b
                        .iter()
                        .map(|u| u.weight())
                        .try_fold(Weight::ZERO, Weight::checked_add);

                    if let Some(weight_a) = weight_sum_a {
                        if let Some(weight_b) = weight_sum_b {
                            if fee_rate_a < fee_rate_b {
                                assert!(weight_a >= weight_b);
                            }

                            if fee_rate_b < fee_rate_a {
                                assert!(weight_b >= weight_a);
                            }

                            if fee_rate_a == fee_rate_b {
                                assert!(weight_a == weight_b);
                            }
                        }
                    }
                }
            }

            Ok(())
        });
    }
}
