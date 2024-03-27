// SPDX-License-Identifier: CC0-1.0
//
//! Bitcoin Branch and Bound Coin Selection.
//!
//! This module introduces the Branch and Bound Coin Selection Algorithm.

use crate::Coin;
use bitcoin::amount::CheckedSum;
use bitcoin::Amount;
use bitcoin::SignedAmount;

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
pub fn select_coins_bnb(
    target: Amount,
    cost_of_change: Amount,
    coins: &[Coin],
) -> Option<std::vec::IntoIter<&Coin>> {
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

    let mut coins: Vec<_> = coins.iter().collect();
    coins.sort_by_key(|c| c.effective_value);
    coins.reverse();

    let mut available_value = coins.clone().into_iter().map(|c| c.effective_value).checked_sum()?;

    if available_value < target {
        return None;
    }

    let fee_rate = coins[0].fee_rate;
    let long_term_fee_rate = coins[0].long_term_fee_rate;

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
                return index_to_utxo_list(best_selection, coins);
            }

            loop {
                index -= 1;

                if index <= *index_selection.last().unwrap() {
                    break;
                }

                available_value += coins[index].effective_value;
            }

            assert_eq!(index, *index_selection.last().unwrap());
            current_waste = current_waste.checked_sub(coins[index].waste)?;
            value = value.checked_sub(coins[index].effective_value)?;
            index_selection.pop().unwrap();
        }
        // * Add next node to the inclusion branch.
        else {
            current_waste = current_waste.checked_add(coins[index].waste)?;

            index_selection.push(index);

            // unchecked add is used here for performance.  Since the sum of all utxo values
            // did not overflow, then any positive subset of the sum will not overflow.
            value = value.unchecked_add(coins[index].effective_value);

            // unchecked sub is used her for performance.
            // The bounds for available_value are at most the sum of utxos
            // and at least zero.
            available_value = available_value.unchecked_sub(coins[index].effective_value);
        }

        // no overflow is possible since the iteration count is bounded.
        index += 1;
        iteration += 1;
    }

    return index_to_utxo_list(best_selection, coins);
}

// Copy the index list into a list such that for each
// index, the corresponding w_utxo is copied.
fn index_to_utxo_list(
    index_list: Option<Vec<usize>>,
    coins: Vec<&Coin>,
) -> Option<std::vec::IntoIter<&Coin>> {
    // Doing this to satisfy the borrow checker such that the
    // refs &WeightedUtxo in `wu` have the same lifetime as the
    // returned &WeightedUtxo.
    let origin: Vec<_> = coins.clone();

    let mut result = vec![];
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
    use super::*;
    use crate::Coin;
    use bitcoin::Amount;
    use bitcoin::FeeRate;
    use bitcoin::ScriptBuf;
    use bitcoin::SignedAmount;
    use bitcoin::TxOut;
    use bitcoin::Weight;
    use core::str::FromStr;

    fn select_coins_bnb_given_target(target_str: &str, expected_inputs: &[&str]) {
        let target = Amount::from_str(target_str).unwrap();
        let coin = create_coin(FeeRate::ZERO, FeeRate::ZERO);
        let mut inputs: Vec<_> = select_coins_bnb(target, Amount::ZERO, &coin).unwrap().collect();
        assert_eq!(inputs.len(), expected_inputs.len());

        inputs.sort();
        for (i, _) in inputs.iter().enumerate() {
            assert_eq!(inputs[i].utxo.value, Amount::from_str(expected_inputs[i]).unwrap());
        }
    }

    fn create_coin_from_eff_values(eff_values: Vec<Amount>) -> Vec<Coin> {
        let no_op = TxOut { value: Amount::ZERO, script_pubkey: ScriptBuf::new() };
        let fee_rate = FeeRate::ZERO;
        let long_term_fee_rate = FeeRate::ZERO;

        eff_values
            .iter()
            .map(|e| Coin {
                utxo: no_op.clone(),
                effective_value: *e,
                waste: SignedAmount::ZERO,
                fee_rate,
                long_term_fee_rate,
            })
            .collect()
    }

    fn create_coin_with_waste(waste: SignedAmount) -> Vec<Coin> {
        let no_op = TxOut { value: Amount::ZERO, script_pubkey: ScriptBuf::new() };
        let fee_rate = FeeRate::ZERO;
        let long_term_fee_rate = FeeRate::ZERO;

        let coin_one = Coin {
            utxo: no_op.clone(),
            effective_value: Amount::from_str("1 cBTC").unwrap(),
            waste,
            fee_rate,
            long_term_fee_rate,
        };

        let coin_two = Coin {
            utxo: no_op.clone(),
            effective_value: Amount::from_str("2 cBTC").unwrap(),
            waste,
            fee_rate,
            long_term_fee_rate,
        };

        let coin_three = Coin {
            utxo: no_op.clone(),
            effective_value: Amount::from_str("3 cBTC").unwrap(),
            waste,
            fee_rate,
            long_term_fee_rate,
        };

        let coin_four = Coin {
            utxo: no_op.clone(),
            effective_value: Amount::from_str("4 cBTC").unwrap(),
            waste,
            fee_rate,
            long_term_fee_rate,
        };

        vec![coin_one, coin_two, coin_three, coin_four]
    }

    fn create_coin(fee_rate: FeeRate, lt_fee_rate: FeeRate) -> Vec<Coin> {
        let output_one =
            TxOut { value: Amount::from_str("1 cBTC").unwrap(), script_pubkey: ScriptBuf::new() };

        let output_two =
            TxOut { value: Amount::from_str("2 cBTC").unwrap(), script_pubkey: ScriptBuf::new() };

        let output_three =
            TxOut { value: Amount::from_str("3 cBTC").unwrap(), script_pubkey: ScriptBuf::new() };

        let output_four =
            TxOut { value: Amount::from_str("4 cBTC").unwrap(), script_pubkey: ScriptBuf::new() };

        let coin_one = Coin::new(output_one, fee_rate, lt_fee_rate, Weight::ZERO).unwrap();
        let coin_two = Coin::new(output_two, fee_rate, lt_fee_rate, Weight::ZERO).unwrap();
        let coin_three = Coin::new(output_three, fee_rate, lt_fee_rate, Weight::ZERO).unwrap();
        let coin_four = Coin::new(output_four, fee_rate, lt_fee_rate, Weight::ZERO).unwrap();

        vec![coin_one, coin_two, coin_three, coin_four]
    }

    #[test]
    fn select_coins_bnb_one() {
        select_coins_bnb_given_target("1 cBTC", &["1 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_two() {
        select_coins_bnb_given_target("2 cBTC", &["2 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_three() {
        select_coins_bnb_given_target("3 cBTC", &["1 cBTC", "2 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_four() {
        select_coins_bnb_given_target("4 cBTC", &["1 cBTC", "3 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_five() {
        select_coins_bnb_given_target("5 cBTC", &["2 cBTC", "3 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_six() {
        select_coins_bnb_given_target("6 cBTC", &["1 cBTC", "2 cBTC", "3 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_seven() {
        select_coins_bnb_given_target("7 cBTC", &["1 cBTC", "2 cBTC", "4 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_eight() {
        select_coins_bnb_given_target("8 cBTC", &["1 cBTC", "3 cBTC", "4 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_nine() {
        select_coins_bnb_given_target("9 cBTC", &["2 cBTC", "3 cBTC", "4 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_ten() {
        select_coins_bnb_given_target("10 cBTC", &["1 cBTC", "2 cBTC", "3 cBTC", "4 cBTC"]);
    }

    #[test]
    fn select_coins_bnb_cost_of_change() {
        let target = Amount::from_str("1 cBTC").unwrap();

        // Since cost of change here is one, we accept any solution
        // between 1 and 2.  Range = (1, 2]
        let cost_of_change = target;

        let tx_out =
            TxOut { value: Amount::from_str("1.5 cBTC").unwrap(), script_pubkey: ScriptBuf::new() };
        let coin = Coin::new(tx_out, FeeRate::ZERO, FeeRate::ZERO, Weight::ZERO).unwrap();
        let coins = &[coin];

        let list: Vec<_> = select_coins_bnb(target, cost_of_change, coins).unwrap().collect();

        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("1.5 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_target_greater_than_value() {
        let target = Amount::from_str("11 cBTC").unwrap();
        let coin = create_coin(FeeRate::ZERO, FeeRate::ZERO);

        let list = select_coins_bnb(target, Amount::ZERO, &coin);
        assert!(list.is_none());
    }

    #[test]
    fn select_coins_bnb_consume_more_inputs_when_cheap() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let coin = create_coin_with_waste(SignedAmount::from_str("-2 sats").unwrap());

        // the possible combinations are 2,4 or 1,2,3
        // fees are cheap, so use 1,2,3
        let list: Vec<_> = select_coins_bnb(target, Amount::ZERO, &coin).unwrap().collect();

        assert_eq!(list.len(), 3);
        assert_eq!(list[0].effective_value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[1].effective_value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[2].effective_value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_consume_less_inputs_when_expensive() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let coin = create_coin_with_waste(SignedAmount::from_str("2 sats").unwrap());

        // the possible combinations are 2,4 or 1,2,3
        // fees are expensive, so use 2,4
        let list: Vec<_> = select_coins_bnb(target, Amount::ZERO, &coin).unwrap().collect();

        assert_eq!(list.len(), 2);
        assert_eq!(list[0].effective_value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].effective_value, Amount::from_str("2 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_utxo_pool_sum_overflow() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let value = SignedAmount::MAX.to_unsigned().unwrap();

        let tx_out = TxOut { value, script_pubkey: ScriptBuf::new() };
        let coin_one =
            Coin::new(tx_out.clone(), FeeRate::ZERO, FeeRate::ZERO, Weight::ZERO).unwrap();
        let coin_two =
            Coin::new(tx_out.clone(), FeeRate::ZERO, FeeRate::ZERO, Weight::ZERO).unwrap();

        let coins = &[coin_one, coin_two];

        let list = select_coins_bnb(target, Amount::ZERO, coins);
        assert!(list.is_none());
    }

    #[test]
    fn select_coins_bnb_upper_bound_overflow() {
        // the upper_bound is target + cost_of_change.
        // adding these two together returns NONE on overflow.
        let target = Amount::MAX;
        let cost_of_change = Amount::MAX;
        let coin = create_coin(FeeRate::ZERO, FeeRate::ZERO);

        let list = select_coins_bnb(target, cost_of_change, &coin);
        assert!(list.is_none());
    }

    #[test]
    fn select_coins_bnb_set_size_five() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let cost_of_change = Amount::ZERO;
        let eff_vals = vec![
            Amount::from_str("3 cBTC").unwrap(),
            Amount::from_str("2.9 cBTC").unwrap(),
            Amount::from_str("2 cBTC").unwrap(),
            Amount::from_str("1.9 cBTC").unwrap(),
            Amount::from_str("1 cBTC").unwrap(),
        ];

        let coins = create_coin_from_eff_values(eff_vals);
        let list: Vec<_> = select_coins_bnb(target, cost_of_change, &coins).unwrap().collect();

        assert_eq!(list.len(), 3);
        assert_eq!(list[0].effective_value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[1].effective_value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[2].effective_value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_set_size_seven() {
        let target = Amount::from_str("18 cBTC").unwrap();
        let cost_of_change = Amount::from_str("50 sats").unwrap();
        let eff_vals = vec![
            Amount::from_str("10 cBTC").unwrap(),
            Amount::from_str("7 cBTC").unwrap() + Amount::from_str("5 sats").unwrap(),
            Amount::from_str("6 cBTC").unwrap() + Amount::from_str("5 sats").unwrap(),
            Amount::from_str("6 cBTC").unwrap(),
            Amount::from_str("3 cBTC").unwrap(),
            Amount::from_str("2 cBTC").unwrap(),
            Amount::from_str("1 cBTC").unwrap() + Amount::from_str("5 sats").unwrap(),
        ];

        let coins = create_coin_from_eff_values(eff_vals);
        let list: Vec<_> = select_coins_bnb(target, cost_of_change, &coins).unwrap().collect();

        assert_eq!(list.len(), 3);
        assert_eq!(list[0].effective_value, Amount::from_str("10 cBTC").unwrap());
        assert_eq!(list[1].effective_value, Amount::from_str("6 cBTC").unwrap());
        assert_eq!(list[2].effective_value, Amount::from_str("2 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_exhaust() {
        // Takes 163,819 iterations to find a solution.
        let base: usize = 2;
        let mut target = 0;
        let vals = (0..15).enumerate().flat_map(|(i, _)| {
            let a = base.pow(15 + i as u32) as u64;
            target += a;
            vec![a, a + 2]
        });

        let eff_vals: Vec<_> = vals.map(Amount::from_sat).collect();
        let coins = create_coin_from_eff_values(eff_vals);
        let list = select_coins_bnb(Amount::from_sat(target), Amount::ONE_SAT, &coins);

        assert!(list.is_none());
    }

    #[test]
    fn select_coins_bnb_exhaust_with_result() {
        // This returns a result AND hits the iteration exhaust limit.

        // Takes 163,819 iterations (hits the iteration limit).
        let base: usize = 2;
        let mut target = 0;
        let vals = (0..15).enumerate().flat_map(|(i, _)| {
            let a = base.pow(15 + i as u32) as u64;
            target += a;
            vec![a, a + 2]
        });

        let mut eff_vals: Vec<_> = vals.map(Amount::from_sat).collect();

        // Add a value that will match the target before iteration exhaustion occurs.
        eff_vals.push(Amount::from_sat(target));
        let coins = create_coin_from_eff_values(eff_vals);
        let mut list = select_coins_bnb(Amount::from_sat(target), Amount::ONE_SAT, &coins).unwrap();

        assert_eq!(list.len(), 1);
        assert_eq!(list.next().unwrap().effective_value, Amount::from_sat(target));
    }
}
