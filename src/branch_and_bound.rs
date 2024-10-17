// SPDX-License-Identifier: CC0-1.0
//
//! Bitcoin Branch and Bound Coin Selection.
//!
//! This module introduces the Branch and Bound Coin Selection Algorithm.

use bitcoin::amount::CheckedSum;
use bitcoin::{Amount, FeeRate, SignedAmount};

use crate::WeightedUtxo;

/// Select coins bnb performs a depth first branch and bound search.  The search traverses a
/// binary tree with a maximum depth n where n is the size of the target UTXO pool.
///
/// See also core: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>
///
/// Returns a vector of `WeightedUtxo` that meet or exceed the target `Amount` when summed.
/// The `Amount` returned will not exceed the target by more than target + delta where delta is
/// the cost of producing a change output.
///
/// The vector returned seeks to minimize the excess, which is the difference between the target
/// `Amount` and vector sum.  If no match can be found, None is returned.
///
/// This algorithem is designed to never panic or overflow.  If a panic or overflow would occur,
/// None is returned.  Also, if no match can be found, None is returned.  The semantics may
/// change in the future to give more information about errors encountered.
///
/// # Returns
/// * `Some(Vec<WeightedUtxo>)` where `Vec<WeightedUtxo>` is not empty on match.
/// * `None` No match found or un-expected results.
///
/// # Arguments
/// * target: Target spend `Amount`
/// * cost_of_change: The `Amount` needed to produce a change output
/// * fee_rate: `FeeRate` used to calculate each effective_value output value
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from

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
//  1) We have already found a solution that matchs the target and the next solution has a
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
) -> Option<std::vec::IntoIter<&Utxo>> {
    // Total_Tries in Core:
    // https://github.com/bitcoin/bitcoin/blob/1d9da8da309d1dbf9aef15eb8dc43b4a2dc3d309/src/wallet/coinselection.cpp#L74
    const ITERATION_LIMIT: i32 = 100_000;

    let mut iteration = 0;
    let mut index = 0;
    let mut backtrack;

    let mut value = Amount::ZERO;

    let mut current_waste: SignedAmount = SignedAmount::ZERO;
    let mut best_waste = SignedAmount::MAX_MONEY;

    let mut index_selection: Vec<usize> = vec![];
    let mut best_selection: Option<Vec<usize>> = None;

    let upper_bound = target.checked_add(cost_of_change)?;

    // Creates a tuple of (effective_value, waste, weighted_utxo)
    let mut w_utxos: Vec<(Amount, SignedAmount, &Utxo)> = weighted_utxos
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
        .map(|(eff_val, waste, wu)| (eff_val.to_unsigned().unwrap(), waste, wu))
        .collect();

    w_utxos.sort_by_key(|u| u.0);
    w_utxos.reverse();

    let mut available_value = w_utxos.clone().into_iter().map(|(ev, _, _)| ev).checked_sum()?;

    if available_value < target {
        return None;
    }

    while iteration < ITERATION_LIMIT {
        backtrack = false;

        // * If any of the conditions are met, backtrack.
        //
        // unchecked_add is used here for performance.  Before entering the search loop, all
        // utxos are summed and checked for overflow.  Since there was no overflow then, any
        // subset of addition will not overflow.
        if available_value.unchecked_add(value) < target
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

            let v = value.to_signed().ok()?;
            let t = target.to_signed().ok()?;
            let waste: SignedAmount = v.checked_sub(t)?;
            current_waste = current_waste.checked_add(waste)?;

            // Check if index_selection is better than the previous known best, and
            // update best_selection accordingly.
            if current_waste <= best_waste {
                best_selection = Some(index_selection.clone());
                best_waste = current_waste;
            }

            current_waste = current_waste.checked_sub(waste)?;
        }
        // * Backtrack
        if backtrack {
            if index_selection.is_empty() {
                return index_to_utxo_list(best_selection, w_utxos);
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
            current_waste = current_waste.checked_add(utxo_waste)?;

            index_selection.push(index);

            // unchecked add is used here for performance.  Since the sum of all utxo values
            // did not overflow, then any positive subset of the sum will not overflow.
            value = value.unchecked_add(eff_value);

            // unchecked sub is used her for performance.
            // The bounds for available_value are at most the sum of utxos
            // and at least zero.
            available_value = available_value.unchecked_sub(eff_value);
        }

        // no overflow is possible since the iteration count is bounded.
        index += 1;
        iteration += 1;
    }

    return index_to_utxo_list(best_selection, w_utxos);
}

// Copy the index list into a list such that for each
// index, the corresponding w_utxo is copied.
fn index_to_utxo_list<Utxo: WeightedUtxo>(
    index_list: Option<Vec<usize>>,
    wu: Vec<(Amount, SignedAmount, &Utxo)>,
) -> Option<std::vec::IntoIter<&Utxo>> {
    // Doing this to satisfy the borrow checker such that the
    // refs &WeightedUtxo in `wu` have the same lifetime as the
    // returned &WeightedUtxo.
    let origin: Vec<_> = wu.iter().map(|(_, _, u)| *u).collect();
    let mut result = origin.clone();
    result.clear();

    // copy over the origin items into result that are present
    // in the index_list.
    if let Some(i_list) = index_list {
        for i in i_list {
            result.push(origin[i])
        }
        Some(result.into_iter())
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;
    use std::iter::{once, zip};

    use bitcoin::{Amount, Weight};

    use super::*;
    use crate::tests::{build_utxo, Utxo};
    use crate::WeightedUtxo;

    #[derive(Debug)]
    pub struct ParamsStr<'a> {
        target: &'a str,
        cost_of_change: &'a str,
        fee_rate: &'a str,
        lt_fee_rate: &'a str,
        weighted_utxos: Vec<&'a str>,
    }

    fn build_pool(fee: Amount) -> Vec<Utxo> {
        let amts = [
            Amount::from_str("1 cBTC").unwrap() + fee,
            Amount::from_str("2 cBTC").unwrap() + fee,
            Amount::from_str("3 cBTC").unwrap() + fee,
            Amount::from_str("4 cBTC").unwrap() + fee,
        ];

        let mut pool = vec![];

        for a in amts {
            let utxo = build_utxo(a, Weight::ZERO);
            pool.push(utxo);
        }

        pool
    }

    fn format_utxo_list(i: &[&Utxo]) -> Vec<String> {
        i.iter().map(|u| u.value().to_string()).collect()
    }

    fn format_expected_str_list(e: &[&str]) -> Vec<String> {
        e.iter().map(|s| Amount::from_str(s).unwrap().to_string()).collect()
    }

    fn assert_coin_select(target_str: &str, expected_inputs: &[&str]) {
        let fee = Amount::ZERO;
        let target = Amount::from_str(target_str).unwrap();
        let utxos = build_pool(fee);
        let inputs: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &utxos)
                .unwrap()
                .collect();

        let input_str_list: Vec<_> = format_utxo_list(&inputs);
        let expected_str_list: Vec<_> = format_expected_str_list(expected_inputs);
        assert_eq!(input_str_list, expected_str_list);
    }

    // This is a temporary patch and can be removed when a new relesae of rust-bitcoin is
    // published.  See: https://github.com/rust-bitcoin/rust-bitcoin/pull/3346
    fn amount_from_str_patch(amount: &str) -> Amount {
        let a = Amount::from_str(amount);

        match a {
            Ok(a) => a,
            Err(_) => Amount::ZERO,
        }
    }

    fn assert_coin_select_params(p: &ParamsStr, expected_inputs: &[&str]) {
        let fee_rate = p.fee_rate.parse::<u64>().unwrap(); // would be nice if  FeeRate had
                                                           // from_str like Amount::from_str()
        let lt_fee_rate = p.lt_fee_rate.parse::<u64>().unwrap();

        let expected_str_list: Vec<_> =
            expected_inputs.iter().map(|s| Amount::from_str(s).unwrap().to_string()).collect();
        let target = Amount::from_str(p.target).unwrap();
        let cost_of_change = amount_from_str_patch(p.cost_of_change);
        let fee_rate = FeeRate::from_sat_per_kwu(fee_rate);
        let lt_fee_rate = FeeRate::from_sat_per_kwu(lt_fee_rate);

        let w_utxos: Vec<_> = p
            .weighted_utxos
            .iter()
            .map(|s| Amount::from_str(s).unwrap())
            .map(|a| build_utxo(a, Weight::ZERO))
            .collect();
        let iter = select_coins_bnb(target, cost_of_change, fee_rate, lt_fee_rate, &w_utxos);

        if expected_str_list.is_empty() {
            assert!(iter.is_none());
        } else {
            let inputs: Vec<_> = iter.unwrap().collect();
            let input_str_list: Vec<_> = format_utxo_list(&inputs);
            assert_eq!(input_str_list, expected_str_list);
        }
    }

    #[test]
    fn select_coins_bnb_one() { assert_coin_select("1 cBTC", &["1 cBTC"]); }

    #[test]
    fn select_coins_bnb_two() { assert_coin_select("2 cBTC", &["2 cBTC"]); }

    #[test]
    fn select_coins_bnb_three() { assert_coin_select("3 cBTC", &["2 cBTC", "1 cBTC"]); }

    #[test]
    fn select_coins_bnb_four() { assert_coin_select("4 cBTC", &["3 cBTC", "1 cBTC"]); }

    #[test]
    fn select_coins_bnb_five() { assert_coin_select("5 cBTC", &["3 cBTC", "2 cBTC"]); }

    #[test]
    fn select_coins_bnb_six() { assert_coin_select("6 cBTC", &["3 cBTC", "2 cBTC", "1 cBTC"]); }

    #[test]
    fn select_coins_bnb_seven() { assert_coin_select("7 cBTC", &["4 cBTC", "2 cBTC", "1 cBTC"]); }

    #[test]
    fn select_coins_bnb_eight() { assert_coin_select("8 cBTC", &["4 cBTC", "3 cBTC", "1 cBTC"]); }

    #[test]
    fn select_coins_bnb_nine() { assert_coin_select("9 cBTC", &["4 cBTC", "3 cBTC", "2 cBTC"]); }

    #[test]
    fn select_coins_bnb_ten() {
        assert_coin_select("10 cBTC", &["4 cBTC", "3 cBTC", "2 cBTC", "1 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_cost_of_change() {
        let mut params = ParamsStr {
            target: "1 cBTC",
            cost_of_change: "1 cBTC",
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: vec!["1.5 cBTC"],
        };

        assert_coin_select_params(&params, &["1.5 cBTC"]);

        params.cost_of_change = "0";
        assert_coin_select_params(&params, &[]);
    }

    #[test]
    fn select_coins_bnb_effective_value() {
        let params = ParamsStr {
            target: "1 cBTC",
            cost_of_change: "0",
            fee_rate: "10",
            lt_fee_rate: "10",
            weighted_utxos: vec!["1 cBTC"],
        };

        assert_coin_select_params(&params, &[]);
    }

    #[test]
    fn select_coins_bnb_skip_effective_negative_effective_value() {
        let params = ParamsStr {
            target: "1 cBTC",
            cost_of_change: "1 cBTC",
            fee_rate: "10",
            lt_fee_rate: "10",
            weighted_utxos: vec!["1.5 cBTC", "1 sat"],
        };

        assert_coin_select_params(&params, &["1.5 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_target_greater_than_value() {
        let params = ParamsStr {
            target: "11 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: vec!["1 cBTC", "2 cBTC", "3 cBTC", "4 cBTC"],
        };

        assert_coin_select_params(&params, &[]);
    }

    #[test]
    fn select_coins_bnb_consume_more_inputs_when_cheap() {
        let params = ParamsStr {
            target: "6 sats",
            cost_of_change: "0",
            fee_rate: "10",
            lt_fee_rate: "20",
            weighted_utxos: vec!["3 sats", "4 sats", "5 sats", "6 sats"], // eff_values: [1, 2, 3, 4]
        };

        assert_coin_select_params(&params, &["5 sats", "4 sats", "3 sats"]);
    }

    #[test]
    fn select_coins_bnb_consume_less_inputs_when_expensive() {
        let params = ParamsStr {
            target: "6 sats",
            cost_of_change: "0",
            fee_rate: "20",
            lt_fee_rate: "10",
            weighted_utxos: vec!["5 sats", "6 sats", "7 sats", "8 sats"], // eff_values: [1, 2, 3, 4]
        };

        assert_coin_select_params(&params, &["8 sats", "6 sats"]);
    }

    #[test]
    fn select_coins_bnb_consume_less_inputs_with_excess_when_expensive() {
        let params = ParamsStr {
            target: "6 sats",
            cost_of_change: "1 sats",
            fee_rate: "20",
            lt_fee_rate: "10",
            weighted_utxos: vec!["5 sats", "6 sats", "7 sats", "9 sats"], // eff_values: [1, 2, 3, 4]
        };

        assert_coin_select_params(&params, &["9 sats", "5 sats"]);
    }

    #[test]
    fn select_coins_bnb_utxo_pool_sum_overflow() {
        let params = ParamsStr {
            target: "1 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: vec!["18446744073709551615 sats", "1 sats"], // [u64::MAX, 1 sat]
        };

        assert_coin_select_params(&params, &[]);
    }

    #[test]
    fn select_coins_bnb_upper_bound_overflow() {
        let params = ParamsStr {
            target: "1 sats",
            cost_of_change: "18446744073709551615 sats", // u64::MAX
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: vec!["1 sats"],
        };

        assert_coin_select_params(&params, &[]);
    }

    #[test]
    fn select_coins_bnb_set_size_five() {
        let params = ParamsStr {
            target: "6 cBTC",
            cost_of_change: "0",
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: vec!["3 cBTC", "2.9 cBTC", "2 cBTC", "1.0 cBTC", "1 cBTC"],
        };

        assert_coin_select_params(&params, &["3 cBTC", "2 cBTC", "1 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_set_size_seven() {
        let params = ParamsStr {
            target: "18 cBTC",
            cost_of_change: "50 sats",
            fee_rate: "0",
            lt_fee_rate: "0",
            weighted_utxos: vec![
                "10 cBTC",
                "7000005 sats",
                "6000005 sats",
                "6 cBTC",
                "3 cBTC",
                "2 cBTC",
                "1000005 cBTC",
            ],
        };

        assert_coin_select_params(&params, &["10 cBTC", "6 cBTC", "2 cBTC"]);
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

        let pool: Vec<_> = amts.into_iter().map(|a| build_utxo(a, Weight::ZERO)).collect();

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
        let pool: Vec<_> = amts.into_iter().map(|a| build_utxo(a, Weight::ZERO)).collect();

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
        let pool: Vec<_> = amts.into_iter().map(|a| build_utxo(a, Weight::ZERO)).collect();

        let mut list = select_coins_bnb(
            Amount::from_sat(target),
            Amount::ONE_SAT,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &pool,
        )
        .unwrap();

        assert_eq!(list.len(), 1);
        assert_eq!(list.next().unwrap().value(), Amount::from_sat(target));
    }
}
