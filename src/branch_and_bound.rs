// SPDX-License-Identifier: CC0-1.0
//
//! Bitcoin Branch and Bound Coin Selection.
//!
//! This module introduces the Branch and Bound Coin-Selection Algorithm.

use bitcoin::amount::CheckedSum;
use bitcoin::{Amount, FeeRate};

use crate::{Return, WeightedUtxo};

/// Performs a deterministic depth first branch and bound search for a changeless solution.
///
/// A changeless solution is one that exceeds the target amount and is less than target amount plus
/// cost of creating change.  In other words, a changeless solution is a solution where it is less expensive
/// to discard the excess amount (amount over the target) than it is to create a new output
/// containing the change.
///
/// This algorithm is designed to never panic or overflow.  If a panic or overflow would occur,
/// None is returned.  Also, if no match can be found, None is returned.  The semantics may
/// change in the future to give more information about errors encountered.
///
/// # Parameters
///
/// * target: Target spend `Amount`
/// * cost_of_change: The `Amount` needed to produce a change output
/// * fee_rate: `FeeRate` used to calculate each effective_value output value
/// * long_term_fee_rate: Needed to estimate the future effective_value of an output.
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from
///
/// # Returns
///
/// * `Some((u32, Vec<WeightedUtxo>))` where `Vec<WeightedUtxo>` is non-empty and where u32 is the
///   iteration count.  The search result succeeded and a match was found.
/// * `None` un-expected results OR no match found.  A future implementation can add Error types
///   which will differentiate between an unexpected error and no match found.  Currently, a None
///   type occurs when one or more of the following criteria are met:
///     - Iteration limit hit
///     - Overflow when summing the UTXO space
///     - Not enough potential amount to meet the target, etc
///     - Target Amount is zero (no match possible)
///     - UTXO space was searched successfully however no match was found
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
pub fn select_coins_bnb<Utxo: WeightedUtxo>(
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    weighted_utxos: &[Utxo],
) -> Return<Utxo> {
    // Total_Tries in Core:
    // https://github.com/bitcoin/bitcoin/blob/1d9da8da309d1dbf9aef15eb8dc43b4a2dc3d309/src/wallet/coinselection.cpp#L74
    const ITERATION_LIMIT: u32 = 100_000;

    let mut iteration = 0;
    let mut index = 0;
    let mut backtrack;

    let mut value = 0;

    let mut current_waste = 0;
    let mut best_waste = Amount::MAX_MONEY.to_sat() as i64;

    let mut index_selection: Vec<usize> = vec![];
    let mut best_selection: Vec<usize> = vec![];

    let target = target.to_sat();
    let upper_bound = target.checked_add(cost_of_change.to_sat())?;

    let w_utxos = weighted_utxos
        .iter()
        // calculate effective_value and waste for each w_utxo.
        .map(|wu| (wu.effective_value(fee_rate), wu.waste(fee_rate, long_term_fee_rate), wu))
        // remove utxos that either had an error in the effective_value or waste calculation.
        .filter(|(eff_val, waste, _)| eff_val.is_some() && waste.is_some())
        // unwrap the option type since we know they are not None (see previous step).
        .map(|(eff_val, waste, wu)| (eff_val.unwrap(), waste.unwrap(), wu))
        // filter out all effective_values that are negative.
        .filter(|(eff_val, _, _)| eff_val.is_positive())
        // all utxo effective_values are now positive (see previous step) - cast to unsigned.
        .map(|(eff_val, waste, wu)| (eff_val.to_unsigned().unwrap(), waste, wu));

    let mut available_value: u64 = w_utxos.clone().map(|(ev, _, _)| ev).checked_sum()?.to_sat();

    // cast from Amount/SignedAmount to u64/i64 for more performant operations.
    let mut w_utxos: Vec<(u64, i64, &Utxo)> =
        w_utxos.map(|(e, w, u)| (e.to_sat(), w.to_sat(), u)).collect();

    // descending sort by effective_value using satisfaction weight as tie breaker.
    w_utxos.sort_by(|a, b| b.0.cmp(&a.0).then(b.2.weight().cmp(&a.2.weight())));

    if available_value < target || target == 0 {
        return None;
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
            || current_waste > best_waste && fee_rate > long_term_fee_rate
        {
            backtrack = true;
        }
        // * value meets or exceeds the target.
        //   Record the solution and the waste then continue.
        else if value >= target {
            backtrack = true;

            let waste: i64 = (value as i64).checked_sub(target as i64)?;
            current_waste = current_waste.checked_add(waste)?;

            // Check if index_selection is better than the previous known best, and
            // update best_selection accordingly.
            if current_waste <= best_waste {
                best_selection = index_selection.clone();
                best_waste = current_waste;
            }

            current_waste = current_waste.checked_sub(waste)?;
        }
        // * Backtrack
        if backtrack {
            if index_selection.is_empty() {
                return index_to_utxo_list(iteration, best_selection, w_utxos);
            }

            loop {
                index -= 1;

                if index <= *index_selection.last().unwrap() {
                    break;
                }

                let (eff_value, _, _) = w_utxos[index];
                available_value += eff_value;
            }

            assert_eq!(index, *index_selection.last().unwrap());
            let (eff_value, utxo_waste, _) = w_utxos[index];
            current_waste = current_waste.checked_sub(utxo_waste)?;
            value = value.checked_sub(eff_value)?;
            index_selection.pop().unwrap();
        }
        // * Add next node to the inclusion branch.
        else {
            let (eff_value, utxo_waste, _) = w_utxos[index];

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
                || w_utxos[index].0 != w_utxos[index - 1].0
            {
                index_selection.push(index);
                current_waste = current_waste.checked_add(utxo_waste)?;

                // unchecked add is used here for performance.  Since the sum of all utxo values
                // did not overflow, then any positive subset of the sum will not overflow.
                value += eff_value;
            }
        }

        // no overflow is possible since the iteration count is bounded.
        index += 1;
        iteration += 1;
    }

    index_to_utxo_list(iteration, best_selection, w_utxos)
}

fn index_to_utxo_list<Utxo: WeightedUtxo>(
    iterations: u32,
    index_list: Vec<usize>,
    wu: Vec<(u64, i64, &Utxo)>,
) -> Return<Utxo> {
    let mut result: Vec<_> = Vec::new();
    let list = index_list;

    for i in list {
        let wu = wu[i].2;
        result.push(wu);
    }

    if result.is_empty() {
        None
    } else {
        Some((iterations, result))
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;
    use std::iter::{once, zip};

    use arbitrary::{Arbitrary, Unstructured};
    use arbtest::arbtest;
    use bitcoin::{Amount, SignedAmount, Weight};

    use super::*;
    use crate::tests::{assert_proptest_bnb, assert_ref_eq, parse_fee_rate, Utxo, UtxoPool};
    use crate::{effective_value, WeightedUtxo};

    #[derive(Debug)]
    pub struct TestBnB<'a> {
        target: &'a str,
        cost_of_change: &'a str,
        fee_rate: &'a str,
        lt_fee_rate: &'a str,
        weighted_utxos: &'a [&'a str],
        expected_utxos: Option<&'a [&'a str]>,
        expected_iterations: u32,
    }

    impl TestBnB<'_> {
        fn assert(&self) {
            let target = Amount::from_str(self.target).unwrap();
            let cost_of_change = Amount::from_str(self.cost_of_change).unwrap();

            let fee_rate = parse_fee_rate(self.fee_rate);
            let lt_fee_rate = parse_fee_rate(self.lt_fee_rate);

            let pool: UtxoPool = UtxoPool::new(self.weighted_utxos, fee_rate);

            let result =
                select_coins_bnb(target, cost_of_change, fee_rate, lt_fee_rate, &pool.utxos);

            if let Some((iterations, inputs)) = result {
                assert_eq!(iterations, self.expected_iterations);

                let expected: UtxoPool = UtxoPool::new(self.expected_utxos.unwrap(), fee_rate);
                assert_ref_eq(inputs, expected.utxos);
            } else {
                assert!(self.expected_utxos.is_none());
                // Remove this check once iteration count is returned by error
                assert_eq!(self.expected_iterations, 0);
            }
        }
    }

    fn assert_coin_select(target_str: &str, expected_iterations: u32, expected_utxos: &[&str]) {
        TestBnB {
            target: target_str,
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB", "3 cBTC/68 vB", "4 cBTC/68 vB"],
            expected_utxos: Some(expected_utxos),
            expected_iterations,
        }
        .assert();
    }

    // Use in place of arbitrary_in_range()
    // see: https://github.com/rust-fuzz/arbitrary/pull/192
    fn arb_amount_in_range(u: &mut Unstructured, r: std::ops::RangeInclusive<u64>) -> Amount {
        let u = u.int_in_range::<u64>(r).unwrap();
        Amount::from_sat(u)
    }

    // Use in place of arbitrary_in_range()
    // see: https://github.com/rust-fuzz/arbitrary/pull/192
    fn arb_fee_rate_in_range(u: &mut Unstructured, r: std::ops::RangeInclusive<u64>) -> FeeRate {
        let u = u.int_in_range::<u64>(r).unwrap();
        FeeRate::from_sat_per_kwu(u)
    }

    // Calculate the maximum fee-rate that would make the corresponding Utxo have a non-negative
    // effective value.  Remember, the effective_value is calculated as value - (fee_rate *
    // weight).  Therefore, if fee_rate * weight is larger than value, the effective value becomes
    // negative and the Utxo will be discarded during selection.
    fn calculate_max_fee_rate(amount: Amount, weight: Weight) -> FeeRate {
        let mut result = FeeRate::ZERO;

        if let Some(fee_rate) = amount.checked_div_by_weight_floor(weight) {
            if fee_rate > FeeRate::ZERO {
                result = fee_rate
            }
        };

        result
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
            weighted_utxos: &["1.5 cBTC/68 vB"],
            expected_utxos: Some(&["1.5 cBTC/68 vB"]),
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
            weighted_utxos: &["1 cBTC/68 vB"],
            expected_utxos: None,
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
            weighted_utxos: &["1.5 cBTC/68 vB"],
            expected_utxos: Some(&["1.5 cBTC/68 vB"]),
            expected_iterations: 2,
        };

        t.assert();

        // The same target and the same UTXO pool does not succeed with
        // a smaller cost_of_change.
        t.cost_of_change = "0";
        t.expected_utxos = None;
        t.expected_iterations = 0;
        t.assert();
    }

    #[test]
    fn select_coins_bnb_effective_value() {
        TestBnB {
            target: "1 cBTC",
            cost_of_change: "0",
            fee_rate: "10 sat/kwu",
            lt_fee_rate: "10 sat/kwu",
            weighted_utxos: &["1 cBTC/68 vB"],
            expected_utxos: None,
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_skip_effective_negative_effective_value() {
        TestBnB {
            target: "1 cBTC",
            cost_of_change: "1 cBTC",
            fee_rate: "10 sat/kwu",
            lt_fee_rate: "10 sat/kwu",
            weighted_utxos: &["1.5 cBTC/68 vB", "1 sat/68 vB"],
            expected_utxos: Some(&["1.5 cBTC/68 vB"]),
            expected_iterations: 2,
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
            weighted_utxos: &["1 cBTC/68 vB", "2 cBTC/68 vB", "3 cBTC/68 vB", "4 cBTC/68 vB"],
            expected_utxos: None,
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
            weighted_utxos: &[
                "e(1 sats)/68 vB",
                "e(2 sats)/68 vB",
                "e(3 sats)/68 vB",
                "e(4 sats)/68 vB",
            ],
            expected_utxos: Some(&["e(3 sats)/68 vB", "e(2 sats)/68 vB", "e(1 sats)/68 vB"]),
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
            weighted_utxos: &[
                "e(1 sats)/68 vB",
                "e(2 sats)/68 vB",
                "e(3 sats)/68 vB",
                "e(4 sats)/68 vB",
            ],
            expected_utxos: Some(&["e(4 sats)/68 vB", "e(2 sats)/68 vB"]),
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
            weighted_utxos: &[
                "e(1 sats)/68 vB",
                "e(2 sats)/68 vB",
                "e(3 sats)/68 vB",
                "e(4 sats)/68 vB",
            ],
            expected_utxos: Some(&["e(4 sats)/68 vB", "e(2 sats)/68 vB"]),
            expected_iterations: 12,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_utxo_pool_sum_overflow() {
        TestBnB {
            target: "1 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: &["18446744073709551615 sats/68 vB", "1 sats/68 vB"], // [u64::MAX, 1 sat]
            expected_utxos: None,
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_upper_bound_overflow() {
        TestBnB {
            target: "1 sats",
            cost_of_change: "18446744073709551615 sats", // u64::MAX
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: &["1 sats/68 vB"],
            expected_utxos: None,
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_utxo_greater_than_max_money() {
        TestBnB {
            target: "1 sats",
            cost_of_change: "18141417255681066410 sats",
            fee_rate: "1 sat/kwu",
            lt_fee_rate: "0",
            weighted_utxos: &["8740670712339394302 sats/68 vB"],
            expected_utxos: None,
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
            // index [0, 2] is skippped because of the utxo skip optimization.
            // [0, 1] is recorded, and next [0, 2] is skipped because after recording
            // [0, 1] then [0, 2] does not need to be tried since it's recognized that
            // it is the same effective_value as [0, 1].
            weighted_utxos: &["e(50 sats)/230 wu", "e(50 sats)/272 wu", "e(50 sats)/230 wu"],
            expected_utxos: Some(&["e(50 sats)/230 wu", "e(50 sats)/230 wu"]),
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
            // index [0, 2] is skippped because of the utxo skip optimization.
            // [0, 1] is recorded, and next [0, 2] is skipped because after recording
            // [0, 1] then [0, 2] does not need to be tried since it's recognized that
            // it is the same effective_value as [0, 1].
            weighted_utxos: &["e(50 sats)/272 wu", "e(50 sats)/230 wu", "e(50 sats)/272 wu"],
            expected_utxos: Some(&["e(50 sats)/272 wu", "e(50 sats)/272 wu"]),
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
            weighted_utxos: &[
                "3 cBTC/68 vB",
                "2.9 cBTC/68 vB",
                "2 cBTC/68 vB",
                "1.0 cBTC/68 vB",
                "1 cBTC/68 vB",
            ],
            expected_utxos: Some(&["3 cBTC/68 vB", "2 cBTC/68 vB", "1 cBTC/68 vB"]),
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
            weighted_utxos: &[
                "10 cBTC/68 vB",
                "7000005 sats/68 vB",
                "6000005 sats/68 vB",
                "6 cBTC/68 vB",
                "3 cBTC/68 vB",
                "2 cBTC/68 vB",
                "1000005 cBTC/68 vB",
            ],
            expected_utxos: Some(&["10 cBTC/68 vB", "6 cBTC/68 vB", "2 cBTC/68 vB"]),
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
            weighted_utxos: &utxos,
            expected_utxos: Some(&[
                "7 cBTC/68 vB",
                "7 cBTC/68 vB",
                "7 cBTC/68 vB",
                "7 cBTC/68 vB",
                "2 cBTC/68 vB",
            ]),
            expected_iterations: 100_000,
        }
        .assert();
    }

    #[test]
    fn select_coins_bnb_exhaust() {
        // Recreate make_hard from bitcoin core test suit.
        // Takes 327,661 iterations to find a solution.
        let base: usize = 2;
        let alpha = (0..17).enumerate().map(|(i, _)| base.pow(17 + i as u32));
        let target = Amount::from_sat(alpha.clone().sum::<usize>() as u64);

        let beta = (0..17).enumerate().map(|(i, _)| {
            let a = base.pow(17 + i as u32);
            let b = base.pow(16 - i as u32);
            a + b
        });

        let amts: Vec<_> = zip(alpha, beta)
            // flatten requires iterable types.
            // use once() to make tuple iterable.
            .flat_map(|tup| once(tup.0).chain(once(tup.1)))
            .map(|a| Amount::from_sat(a as u64))
            .collect();

        let pool: Vec<_> = amts.into_iter().map(|a| Utxo::new(a, Weight::ZERO)).collect();

        let list = select_coins_bnb(target, Amount::ONE_SAT, FeeRate::ZERO, FeeRate::ZERO, &pool);

        assert!(list.is_none());
    }

    #[test]
    fn select_coins_bnb_exhaust_v2() {
        // Takes 163,819 iterations to find a solution.
        let base: usize = 2;
        let mut target = 0;
        let vals = (0..15).enumerate().flat_map(|(i, _)| {
            let a = base.pow(15 + i as u32) as u64;
            target += a;
            vec![a, a + 2]
        });

        let amts: Vec<_> = vals.map(Amount::from_sat).collect();
        let pool: Vec<_> = amts.into_iter().map(|a| Utxo::new(a, Weight::ZERO)).collect();

        let list = select_coins_bnb(
            Amount::from_sat(target),
            Amount::ONE_SAT,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &pool,
        );

        assert!(list.is_none());
    }

    #[test]
    fn select_coins_bnb_exhaust_with_result() {
        // This returns a result AND hits the iteration exhaust limit.
        // Takes 163,819 iterations (hits the iteration limit).
        let base: usize = 2;
        let mut target = 0;
        let amts = (0..15).enumerate().flat_map(|(i, _)| {
            let a = base.pow(15 + i as u32) as u64;
            target += a;
            vec![a, a + 2]
        });

        let mut amts: Vec<_> = amts.map(Amount::from_sat).collect();

        // Add a value that will match the target before iteration exhaustion occurs.
        amts.push(Amount::from_sat(target));
        let pool: Vec<_> = amts.into_iter().map(|a| Utxo::new(a, Weight::ZERO)).collect();

        let (iterations, utxos) = select_coins_bnb(
            Amount::from_sat(target),
            Amount::ONE_SAT,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &pool,
        )
        .unwrap();

        assert_eq!(utxos.len(), 1);
        assert_eq!(utxos[0].value(), Amount::from_sat(target));
        assert_eq!(100000, iterations);
    }

    #[test]
    fn select_one_of_one_idealized_proptest() {
        let minimal_non_dust: u64 = 1;
        let effective_value_max: u64 = SignedAmount::MAX.to_sat() as u64;

        arbtest(|u| {
            let amount = arb_amount_in_range(u, minimal_non_dust..=effective_value_max);
            let utxo = Utxo::new(amount, Weight::ZERO);
            let pool: Vec<Utxo> = vec![utxo.clone()];

            let (_i, utxos) =
                select_coins_bnb(utxo.value(), Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &pool)
                    .unwrap();

            assert_ref_eq(utxos, pool.clone());

            Ok(())
        });
    }

    #[test]
    fn select_one_of_many_proptest() {
        arbtest(|u| {
            let pool = UtxoPool::arbitrary(u)?;
            let utxos = pool.utxos.clone();

            let utxo = u.choose(&utxos)?;

            let max_fee_rate = calculate_max_fee_rate(utxo.value(), utxo.weight());
            let fee_rate = arb_fee_rate_in_range(u, 0..=max_fee_rate.to_sat_per_kwu());

            if let Some(eff_value) = effective_value(fee_rate, utxo.weight(), utxo.value()) {
                let target = eff_value.to_unsigned().unwrap();
                let result = select_coins_bnb(target, Amount::ZERO, fee_rate, fee_rate, &utxos);

                if let Some((_i, utxos)) = result {
                    let sum: SignedAmount = utxos
                        .clone()
                        .into_iter()
                        .map(|u| effective_value(fee_rate, u.weight(), u.value()).unwrap())
                        .sum();
                    let amount_sum = sum.to_unsigned().unwrap();
                    assert_eq!(amount_sum, target);

                    // TODO add checked_sum to Weight
                    let weight_sum = utxos
                        .iter()
                        .try_fold(Weight::ZERO, |acc, itm| acc.checked_add(itm.weight()));

                    assert!(weight_sum.unwrap() <= utxo.weight());
                } else {
                    // if result was none, then assert that fail happened because overflow when
                    // summing pool.  In the future, assert specific error when added.
                    let available_value = utxos.into_iter().map(|u| u.value()).checked_sum();
                    assert!(available_value.is_none());
                }
            }

            Ok(())
        });
    }

    #[test]
    fn select_many_of_many_proptest() {
        arbtest(|u| {
            let pool = UtxoPool::arbitrary(u)?;
            let utxos = pool.utxos.clone();

            // generate all the possible utxos subsets
            let mut gen = exhaustigen::Gen::new();
            let mut subsets: Vec<Vec<&Utxo>> = Vec::new();
            while !gen.done() {
                let s = gen.gen_subset(&pool.utxos).collect::<Vec<_>>();
                subsets.push(s);
            }

            // choose a set at random to be the target
            let target_selection: &Vec<&Utxo> = u.choose(&subsets).unwrap();

            // find the minmum fee_rate that will result in all utxos having a posiive
            // effective_value
            let mut fee_rates: Vec<FeeRate> = target_selection
                .iter()
                .map(|u| calculate_max_fee_rate(u.value(), u.weight()))
                .collect();
            fee_rates.sort();

            let min_fee_rate = fee_rates.first().unwrap_or(&FeeRate::ZERO).to_sat_per_kwu();
            let fee_rate = arb_fee_rate_in_range(u, 0..=min_fee_rate);

            let effective_values: Vec<SignedAmount> = target_selection
                .iter()
                .map(|u| {
                    let e = effective_value(fee_rate, u.weight(), u.value());
                    e.unwrap_or(SignedAmount::ZERO)
                })
                .collect();

            let eff_values_sum = effective_values.into_iter().checked_sum();

            // if None, then this random subset is an invalid target (skip)
            if let Some(sum) = eff_values_sum {
                let target = sum.to_unsigned().unwrap();
                let result = select_coins_bnb(target, Amount::ZERO, fee_rate, fee_rate, &utxos);

                if let Some((_i, utxos)) = result {
                    let effective_value_sum: Amount = utxos
                        .clone()
                        .into_iter()
                        .map(|u| {
                            effective_value(fee_rate, u.weight(), u.value())
                                .unwrap()
                                .to_unsigned()
                                .unwrap()
                        })
                        .sum();
                    assert_eq!(effective_value_sum, target);

                    // TODO checked_add not available in Weight
                    let result_sum = utxos
                        .iter()
                        .try_fold(Weight::ZERO, |acc, item| acc.checked_add(item.weight()));

                    let target_sum = target_selection
                        .iter()
                        .try_fold(Weight::ZERO, |acc, item| acc.checked_add(item.weight()));

                    if let Some(s) = target_sum {
                        assert!(result_sum.unwrap() <= s);
                    }
                } else {
                    let available_value = utxos.into_iter().map(|u| u.value()).checked_sum();
                    assert!(
                        available_value.is_none()
                            || target_selection.is_empty()
                            || target == Amount::ZERO
                    );
                }
            }

            Ok(())
        });
    }

    #[test]
    fn select_bnb_proptest() {
        arbtest(|u| {
            let pool = UtxoPool::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let cost_of_change = Amount::arbitrary(u)?;
            let fee_rate = FeeRate::arbitrary(u)?;
            let lt_fee_rate = FeeRate::arbitrary(u)?;

            let utxos = pool.utxos.clone();

            let result = select_coins_bnb(target, cost_of_change, fee_rate, lt_fee_rate, &utxos);

            assert_proptest_bnb(target, cost_of_change, fee_rate, lt_fee_rate, pool, result);

            Ok(())
        });
    }
}
