// SPDX-License-Identifier: CC0-1.0
//
//! Bitcoin Branch and Bound Coin Selection.
//!
//! This module introduces the Branch and Bound Coin-Selection Algorithm.

use bitcoin_units::{Amount, CheckedSum, Weight};

use crate::OverflowError::{Addition, Subtraction};
use crate::SelectionError::{
    InsufficentFunds, IterationLimitReached, MaxWeightExceeded, Overflow, SolutionNotFound,
};
use crate::{Return, UtxoPool, WeightedUtxo};

// Total_Tries in Core:
// https://github.com/bitcoin/bitcoin/blob/1d9da8da309d1dbf9aef15eb8dc43b4a2dc3d309/src/wallet/coinselection.cpp#L74
pub const ITERATION_LIMIT: u32 = 100_000;

/// Performs a deterministic depth first branch and bound search for a changeless solution.
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
/// The best solution found and the number of iterations to find it.  Note that if the iteration
/// count equals `ITERATION_LIMIT`, a better solution may exist than the one found.
///
/// # Errors
///
/// If an arithmetic overflow occurs, a solution is not present, the target can't be reached or if
/// the iteration limit is hit.
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
pub fn select_coins_bnb<'a>(
    target: Amount,
    cost_of_change: Amount,
    max_weight: Weight,
    pool: &UtxoPool<'a>,
) -> Return<'a> {
    let mut iteration = 0;
    let mut index = 0;
    let mut max_tx_weight_exceeded = false;
    let mut backtrack;

    let mut value = 0;
    let mut weight = Weight::ZERO;

    let mut current_waste = 0;
    let mut best_waste = Amount::MAX_MONEY.to_sat() as i64;

    let mut index_selection: Vec<usize> = vec![];
    let mut best_selection: Vec<usize> = vec![];

    let upper_bound = target.checked_add(cost_of_change).ok_or(Overflow(Addition))?.to_sat();
    let target = target.to_sat();

    let mut available_value: u64 = pool.available_value.to_sat();

    let weighted_utxos = pool.utxos.iter();
    let _ = weighted_utxos.clone().map(|u| u.weight()).checked_sum().ok_or(Overflow(Addition))?;
    let mut weighted_utxos: Vec<_> = weighted_utxos.collect();

    // descending sort by effective_value, ascending sort by waste.
    weighted_utxos
        .sort_by(|a, b| b.effective_value().cmp(&a.effective_value()).then(a.waste.cmp(&b.waste)));

    if available_value < target {
        return Err(InsufficentFunds);
    }

    while iteration < ITERATION_LIMIT {
        backtrack = false;

        // * If any of the conditions are met, backtrack.
        //
        // unchecked_add is used here for performance.  Before entering the search loop, all
        // utxos are summed and checked for overflow.  Since there was no overflow then, any
        // subset of addition will not overflow.
        if available_value + value < target
            // Provides an upper bound on the excess value that is permissible.
            // Since value is lost when we create a change output due to increasing the size of the
            // transaction by an output (the change output), we accept solutions that may be
            // larger than the target.  The excess is added to the solutions waste score.
            // However, values greater than value + cost_of_change are not considered.
            //
            // This creates a range of possible solutions where;
            // range = (target, target + cost_of_change]
            //
            // That is, the range includes solutions that exactly equal the target up to but not
            // including values greater than target + cost_of_change.
            || value > upper_bound
            // if current_waste > best_waste, then backtrack.  However, only backtrack if
            // it's high fee_rate environment.  During low fee environments, a utxo may
            // have negative waste, therefore adding more utxos in such an environment
            // may still result in reduced waste.
            || current_waste > best_waste && weighted_utxos[0].is_fee_expensive()
        {
            backtrack = true;
        } else if weight > max_weight {
            max_tx_weight_exceeded = true;
            backtrack = true;
        }
        // * value meets or exceeds the target.
        //   Record the solution and the waste then continue.
        else if value >= target {
            backtrack = true;

            let waste: i64 =
                (value as i64).checked_sub(target as i64).ok_or(Overflow(Subtraction))?;
            current_waste = current_waste.checked_add(waste).ok_or(Overflow(Addition))?;

            // Check if index_selection is better than the previous known best, and
            // update best_selection accordingly.
            if current_waste <= best_waste {
                best_selection = index_selection.clone();
                best_waste = current_waste;
            }

            current_waste = current_waste.checked_sub(waste).ok_or(Overflow(Subtraction))?;
        }
        // * Backtrack
        if backtrack {
            if index_selection.is_empty() {
                return index_to_utxo_list(
                    iteration,
                    best_selection,
                    max_tx_weight_exceeded,
                    weighted_utxos,
                );
            }

            loop {
                index -= 1;

                if index <= *index_selection.last().unwrap() {
                    break;
                }

                let eff_value = weighted_utxos[index].effective_value;
                available_value += eff_value;
            }

            assert_eq!(index, *index_selection.last().unwrap());
            let eff_value = weighted_utxos[index].effective_value;
            let utxo_waste = weighted_utxos[index].waste;
            let utxo_weight = weighted_utxos[index].weight();
            current_waste = current_waste.checked_sub(utxo_waste).ok_or(Overflow(Subtraction))?;
            value = value.checked_sub(eff_value).ok_or(Overflow(Addition))?;
            weight -= utxo_weight;
            index_selection.pop().unwrap();
        }
        // * Add next node to the inclusion branch.
        else {
            let eff_value = weighted_utxos[index].effective_value;
            let utxo_weight = weighted_utxos[index].weight();
            let utxo_waste = weighted_utxos[index].waste;

            // unchecked sub is used her for performance.
            // The bounds for available_value are at most the sum of utxos
            // and at least zero.
            available_value -= eff_value;

            // Check if we can omit the currently selected depending on if the last
            // was omitted.  Therefore, check if index_selection has a previous one.
            if index_selection.is_empty()
                // Check if the previous UTXO was included.
                || index - 1 == *index_selection.last().unwrap()
                // Check if the previous UTXO has the same value has the previous one.
                || weighted_utxos[index].effective_value != weighted_utxos[index - 1].effective_value
            {
                index_selection.push(index);
                current_waste = current_waste.checked_add(utxo_waste).ok_or(Overflow(Addition))?;

                // unchecked add is used here for performance.  Since the sum of all utxo values
                // did not overflow, then any positive subset of the sum will not overflow.
                value += eff_value;
                weight += utxo_weight;
            }
        }

        // no overflow is possible since the iteration count is bounded.
        index += 1;
        iteration += 1;
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
    use bitcoin_units::{Amount, CheckedSum, FeeRate, Weight};

    use super::*;
    use crate::tests::{assert_ref_eq, parse_fee_rate, SelectionCandidate};
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
            let candidate = SelectionCandidate::new(self.weighted_utxos, fee_rate, lt_fee_rate);
            let utxo_pool = crate::UtxoPool::new(&candidate.utxos).unwrap();

            let result = select_coins_bnb(target, cost_of_change, max_weight, &utxo_pool);

            match result {
                Ok((iterations, inputs)) => {
                    assert_eq!(iterations, self.expected_iterations);
                    let candidate =
                        SelectionCandidate::new(self.expected_utxos, fee_rate, lt_fee_rate);
                    assert_ref_eq(inputs, candidate.utxos);
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
        candidate: SelectionCandidate,
        expected_inputs: Vec<WeightedUtxo>,
    }

    impl AssertBnB {
        fn exec(self) {
            let target = self.target;
            let cost_of_change = self.cost_of_change;
            let max_weight = self.max_weight;
            let candidate = &self.candidate;
            let utxos = &candidate.utxos;
            let utxo_pool = crate::UtxoPool::new(&utxos).unwrap();
            let expected_inputs = self.expected_inputs;

            let upper_bound = target.checked_add(cost_of_change);
            let result = select_coins_bnb(target, cost_of_change, max_weight, &utxo_pool);

            match result {
                Ok((i, utxos)) => {
                    assert!(i > 0 || target == Amount::ZERO);
                    crate::tests::assert_target_selection(&utxos, target, upper_bound);
                }
                Err(InsufficentFunds) => {
                    let available_value = utxo_pool.available_value;
                    assert!(available_value < target);
                }
                Err(IterationLimitReached) => {}
                Err(Overflow(_)) => {
                    assert!(upper_bound.is_none());
                }
                Err(ProgramError) => panic!("un-expected result"),
                Err(SolutionNotFound) =>
                    assert!(expected_inputs.is_empty() || target == Amount::ZERO),
                Err(MaxWeightExceeded) => {
                    let weight_total = candidate.weight_total().unwrap();
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
            let tuple: Vec<_> = init
                .clone()
                .iter()
                .scan(Amount::ZERO, |state, (amt, _, _)| {
                    // only add utxos to the pool that sum to less than Amount::MAX
                    if let Some(a) = (*state + amt).ok() {
                        *state = a;
                        Some(a)
                    } else {
                        None
                    }
                })
                .zip(init.clone())
                .map(|(_, u)| u)
                .scan(Weight::ZERO, |state, (_, weight, _)| {
                    // only add utxos to the pool that sum to less than Weight::MAX
                    if let Some(w) = weight.checked_add(*state) {
                        *state = w;
                        Some(*state)
                    } else {
                        None
                    }
                })
                .zip(init.clone())
                .map(|(_, u)| u)
                .collect();

            let expected_inputs: Vec<WeightedUtxo> = tuple
                .iter()
                .filter(|(_, _, include)| *include)
                .filter_map(|(amt, weight, _)| {
                    WeightedUtxo::new(*amt, *weight, fee_rate, long_term_fee_rate)
                })
                .collect();
            let utxos: Vec<WeightedUtxo> = tuple
                .iter()
                .filter_map(|(amt, weight, _)| {
                    WeightedUtxo::new(*amt, *weight, fee_rate, long_term_fee_rate)
                })
                .collect();
            let candidate = SelectionCandidate { utxos, fee_rate, long_term_fee_rate };

            let target_set: Vec<_> = expected_inputs.iter().map(|u| u.effective_value()).collect();

            let target: Amount =
                target_set.clone().into_iter().checked_sum().unwrap_or(Amount::ZERO);

            Ok(AssertBnB { target, cost_of_change, max_weight, candidate, expected_inputs })
        }
    }

    #[test]
    fn select_coins_bnb_one() { assert_coin_select("1 cBTC", 8, &["1 cBTC/68 vB"]); }

    #[test]
    fn select_coins_bnb_two() { assert_coin_select("2 cBTC", 6, &["2 cBTC/68 vB"]); }

    #[test]
    fn select_coins_bnb_three() {
        assert_coin_select("3 cBTC", 8, &["2 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_four() {
        assert_coin_select("4 cBTC", 8, &["3 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_five() {
        assert_coin_select("5 cBTC", 12, &["3 cBTC/68 vB", "2 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_six() {
        assert_coin_select("6 cBTC", 12, &["3 cBTC/68 vB", "2 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_seven() {
        assert_coin_select("7 cBTC", 8, &["4 cBTC/68 vB", "2 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_eight() {
        assert_coin_select("8 cBTC", 8, &["4 cBTC/68 vB", "3 cBTC/68 vB", "1 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_nine() {
        assert_coin_select("9 cBTC", 6, &["4 cBTC/68 vB", "3 cBTC/68 vB", "2 cBTC/68 vB"]);
    }

    #[test]
    fn select_coins_bnb_ten() {
        assert_coin_select(
            "10 cBTC",
            8,
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
            expected_iterations: 2,
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
            expected_iterations: 12,
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
            expected_iterations: 12,
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
            expected_iterations: 12,
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
            expected_iterations: 9,
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
            expected_iterations: 9,
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
            expected_iterations: 22,
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
            expected_iterations: 44,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_early_bail_optimization() {
        // Test the UTXO exclusion shortcut optimization.  The selection begins with
        // 7 * 4 = 28 cBTC.  Next, since the pool is sorted in descending order,
        // 5 cBTC is added which is above the target of 30.   If the UTXO exclusion
        // shortcut works, all next 5 cBTC values will be skipped since they have
        // the same effective_value and 5 cBTC was excluded.  Otherwise, trying all
        // combination of 5 cBTC will cause the iteration limit to be reached before
        // finding 2 cBTC which matches the total exactly.
        let mut utxos =
            vec!["7 cBTC/68 vB", "7 cBTC/68 vB", "7 cBTC/68 vB", "7 cBTC/68 vB", "2 cBTC/68 vB"];
        for _i in 0..50_000 {
            utxos.push("5 cBTC/68 vB");
        }
        TestBnB {
            target: "30 cBTC",
            cost_of_change: "5000 sats",
            fee_rate: "0",
            lt_fee_rate: "0",
            max_weight: "40000 wu",
            weighted_utxos: &utxos,
            expected_utxos: &[
                "7 cBTC/68 vB",
                "7 cBTC/68 vB",
                "7 cBTC/68 vB",
                "7 cBTC/68 vB",
                "2 cBTC/68 vB",
            ],
            expected_error: None,
            expected_iterations: 100_000,
        }
        .assert();
    }

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
            expected_iterations: 4,
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
        let utxo_pool = crate::UtxoPool::new(&pool).unwrap();

        let result = select_coins_bnb(target, Amount::ONE_SAT, max_weight, &utxo_pool);

        match result {
            Err(IterationLimitReached) => {}
            _ => panic!(),
        }
    }

    #[test]
    fn select_coins_bnb_exhaust_v2() {
        // Takes 163,819 iterations to find a solution.
        let base: u32 = 2;
        let mut target = 0;
        let max_weight = Weight::from_wu(40_000);
        let vals = (0..15).enumerate().flat_map(|(i, _)| {
            let a = base.pow(15 + i as u32);
            target += a;
            vec![a, a + 2]
        });
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;

        let amts: Vec<_> = vals.map(Amount::from_sat_u32).collect();
        let pool: Vec<_> = amts
            .into_iter()
            .filter_map(|a| WeightedUtxo::new(a, Weight::ZERO, fee_rate, lt_fee_rate))
            .collect();
        let utxo_pool = crate::UtxoPool::new(&pool).unwrap();

        let result =
            select_coins_bnb(Amount::from_sat_u32(target), Amount::ONE_SAT, max_weight, &utxo_pool);

        match result {
            Err(IterationLimitReached) => {}
            _ => panic!(),
        }
    }

    #[test]
    fn select_coins_bnb_exhaust_with_result() {
        // This returns a result AND hits the iteration exhaust limit.
        // Takes 163,819 iterations (hits the iteration limit).
        let base: u32 = 2;
        let mut target = 0;
        let max_weight = Weight::from_wu(40_000);
        let amts = (0..15).enumerate().flat_map(|(i, _)| {
            let a = base.pow(15 + i as u32);
            target += a;
            vec![a, a + 2]
        });
        let fee_rate = FeeRate::ZERO;
        let lt_fee_rate = FeeRate::ZERO;

        let mut amts: Vec<_> = amts.map(Amount::from_sat_u32).collect();

        // Add a value that will match the target before iteration exhaustion occurs.
        amts.push(Amount::from_sat_u32(target));
        let pool: Vec<_> = amts
            .into_iter()
            .filter_map(|a| WeightedUtxo::new(a, Weight::ZERO, fee_rate, lt_fee_rate))
            .collect();
        let utxo_pool = crate::UtxoPool::new(&pool).unwrap();

        let (iterations, utxos) =
            select_coins_bnb(Amount::from_sat_u32(target), Amount::ONE_SAT, max_weight, &utxo_pool)
                .unwrap();

        assert_eq!(utxos.len(), 1);
        assert_eq!(utxos[0].value(), Amount::from_sat_u32(target));
        assert_eq!(100000, iterations);
    }

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
            let candidate = SelectionCandidate::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let cost_of_change = Amount::arbitrary(u)?;
            let fee_rate_a = candidate.fee_rate;
            let fee_rate_b = candidate.long_term_fee_rate;
            let max_weight = Weight::MAX;
            let utxos = candidate.utxos;
            let utxo_pool = crate::UtxoPool::new(&utxos).unwrap();

            let result_a = select_coins_bnb(target, cost_of_change, max_weight, &utxo_pool);

            let utxo_selection_attributes =
                utxos.clone().into_iter().map(|u| (u.value(), u.weight()));
            // swap lt_fee_rate and fee_rate position.
            let utxos_b: Vec<WeightedUtxo> = utxo_selection_attributes
                .filter_map(|(amt, weight)| WeightedUtxo::new(amt, weight, fee_rate_b, fee_rate_a))
                .collect();
            let utxo_pool_b = crate::UtxoPool::new(&utxos_b).unwrap();

            let result_b = select_coins_bnb(target, cost_of_change, max_weight, &utxo_pool_b);

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
