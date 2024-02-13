// SPDX-License-Identifier: CC0-1.0
//
//! Bitcoin Branch and Bound Selection.
//!
//! This module introduces the Branch and Bound Coin Selection Algorithm.

use crate::WeightedUtxo;
use bitcoin::amount::CheckedSum;
use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::SignedAmount;

/// Select coins bnb performs a depth first branch and bound search.  The search traverses a
/// binary tree with a maximum depth n where n is the size of the UTXO pool to be searched.
///
/// See also core: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>
///
/// Returns a vector of `WeightedUtxo` that meet or exceed the target `Amount` when summed.
/// The `Amount` returned will not exceed the target by more than target + delta where delta is
/// the cost of producing a change output.
///
/// The vector returned seeks to minimize the waste, which is the difference between the target
/// `Amount` and sum of the vector returned.  If no match can be found, None is returned.
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

// This search can be thought of as exploring a binary tree where the left branch is the inclusion
// of a node and the right branch is the exclusion.  For example, if the utxo set consist of a
// list of utxos: [4,3,2,1], and the target is 5, the selection process works as follows:
//
// Start at 4 and try including 4 in the total the first iteration.  We therefore have a tree with
// only one root node that is less than the total, so the next iteration occurs.  The second
// iteration examines a tree where 4 is the root and the left branch is 3.
//      o
//     /
//    4
//   /
//  3
//
// At this point, the total sums to 7 which exceeds the target of 5.  7 may be recorded as a
// solution with a waste of 2 (7 - 5). Next, 3 is removed from the left branch and it becomes
// the right branch since 3 is now excluded.  We now backtrack to 4.
//      o
//     /
//    4
//   / \
//      3
//
// We next try adding 2 to the inclusion branch.
//      o
//     /
//    4
//   / \
//  2   3
//
// The sum of the left inclusion branch is now 6.  Once again, we find the total
// exceeds 5, so we record 6 as a solution with a waste of 1, our best solution so far.
// Once again, we now add 2 to the exclusion branch and backtrack to 4.
//      o
//     /
//    4
//   / \
//      3
//     / \
//        2
//
// Finally, we add 1 to the inclusion branch.  This ends our depth first search by matching two
// conditions, it is both the leaf node (end of the list) and matches our search criteria of
// matching 5 with minimal waste (0).  Both 4 and 1 are on the left inclusion branch.  We therefore
// record our solution and backtrack to next try the exclusion branch of our root node 4.
//      o
//     / \
//    4
//   / \
//  1   3
//       \
//        2
//
// We try excluding 4 now
//      o
//     / \
//    3   4
//
// 3 is less than our target, so we next add 2 to our inclusion branch
//      o
//     / \
//    3   4
//   /
//  2
//
// We now stop our search again noticing that 3 and 2 equals our target as 5, and since this
// solution was found last, then [3, 2] overwrites the previously found solution [4, 1].  We next
// backtrack and exclude our root node of this subtree 3.  Since our new sub tree starting at 2
// doesn't have enough value left to meet the target, we conclude our search at [3, 2].
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
// wasteful, and we may bound our search because a better waste score is no longer possible
//
//  a) We have already found a solution and the next solution is greater then the previous.
//  b) It's a high fee environment such that adding more utxos will increase current_waste.
//
// If either a or b is true, we consider the search path no longer viable to continue down.
pub fn select_coins_bnb(
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    long_term_fee_rate: FeeRate,
    weighted_utxos: &[WeightedUtxo],
) -> Option<std::vec::IntoIter<&'_ WeightedUtxo>> {
    // Total_Tries in Core:
    // https://github.com/bitcoin/bitcoin/blob/1d9da8da309d1dbf9aef15eb8dc43b4a2dc3d309/src/wallet/coinselection.cpp#L74
    const ITERATION_LIMIT: i32 = 100_000;

    let mut iteration = 0;
    let mut index = 0;
    let mut backtrack;
    let mut backtrack_subtree;

    let mut value = Amount::ZERO;

    let mut current_waste: SignedAmount = SignedAmount::ZERO;
    let mut best_waste = SignedAmount::MAX_MONEY;

    let mut index_selection: Vec<usize> = vec![];
    let mut best_selection: Option<Vec<usize>> = None;

    let upper_bound = target.checked_add(cost_of_change)?;

    // TODO - since all serach algorithms operate on effective_value,
    // this statement should be moved to lib and then passed to both
    // bnb and srd.
    //
    // TODO - can this be simplified with filter_map()
    //
    // Creates a tuple of (effective_value, waste, weighted_utxo)
    // * filter out effective values and wastes that are None (error).
    // * filter out negative effective values.
    let mut w_utxos: Vec<(Amount, SignedAmount, &WeightedUtxo)> = weighted_utxos
        .iter()
        // calculate effective_value and waste for each w_utxo.
        .map(|wu| (wu.effective_value(fee_rate), wu.waste(fee_rate, long_term_fee_rate), wu))
        // remove utxos that either had an error in the effective_value or waste calculation.
        .filter(|(eff_val, waste, _)| !eff_val.is_none() && !waste.is_none())
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
        // There are two conditions for backtracking:
        //
        // 1: Not enough value to make it to target.
        //    This condition happens before reaching a leaf node.
        //    Looking for a leaf node condition should not make a difference.
        //    This backtrack removes more than one node and instead starts
        //    the exploration of a new subtree.
        //
        // From:
        //      o
        //     / \
        //    4
        //   / \
        //  1   3
        //     / \
        //        2
        //
        // To:
        //      o
        //     / \
        //    3   4
        //
        //
        // 2: value meets or exceeded target.
        //    In this condition, we only backtrack one node
        //
        // From:
        //      o
        //     /
        //    4
        //   /
        //  3
        //
        // To:
        //      o
        //     / \
        //    4   3

        // Set initial loop state
        backtrack = false;
        backtrack_subtree = false;

        // * not enough value to make it to the target.
        //   Therefore, explore a new new subtree.
        //
        // unchecked_add is used here for performance.  Before entering the search loop, all
        // utxos are summed and checked for overflow.  Since there was no overflow then, any
        // subset of addition will not overflow.
        if available_value.unchecked_add(value) < target {
            backtrack_subtree = true;
        }
        // This optimization provides an upper bound on the amount of waste that is acceptable.
        // Since value is lost when we create a change output due to increasing the size of the
        // transaction by an output, we accept solutions that may be larger than the target as
        // if they are exactly equal to the target and consider the overage waste or a throw
        // away amount.  However we do not consider values greater than value + cost_of_change.
        //
        // This effectively creates a range of possible solution where;
        // range = (target, target + cost_of_change]
        //
        // That is, the range includes solutions that exactly equal the target up to but not
        // including values greater than target + cost_of_change.
        //
        // if current_waste > best_waste, then backtrack.  However, only backtrack if
        // it's high fee_rate environment.  During low fee environments, a utxo may
        // have negative waste, therefore adding more utxos in such an environment
        // may still result in reduced waste.
        else if value > upper_bound || current_waste > best_waste && fee_rate > long_term_fee_rate
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

        // * Backtrack one node
        if backtrack {
            let last_index = index_selection.pop().unwrap();
            let (eff_value, utxo_waste, _) = w_utxos[last_index];

            current_waste = current_waste.checked_sub(utxo_waste)?;
            value = value.checked_sub(eff_value)?;
            index -= 1;
            assert_eq!(index, last_index);
        }
        // * Backtrack to new tree
        else if backtrack_subtree {
            // No new subtree left to explore.
            if index_selection.is_empty() {
                return index_to_utxo_list(best_selection, w_utxos);
            }

            // Anchor the new subtree at the next available index.
            //
            // if our index selection is: [0,1,2,3]
            // then copy the head 0 into index.
            // At the end of this loop, index is incremented to 1.
            // Therefore, we will be starting our next search tree at index 1.
            index = index_selection[0];

            // Reset waste counter since we are starting a new search branch.
            current_waste = SignedAmount::ZERO;

            // The available value of the next iteration.  This should never overflow
            // since the value is always less than the last available_value calculation.
            available_value = w_utxos[index + 1..].iter().map(|&(v, _, _)| v).sum();

            // If the new subtree does not have enough value, we are done searching.
            if available_value < target {
                return index_to_utxo_list(best_selection, w_utxos);
            }

            // Start a new selection and add the root of the new subtree to the index selection.
            index_selection.clear();
            value = Amount::ZERO;
        }
        // * Add next node to the inclusion branch.
        else {
            let (eff_value, utxo_waste, _) = w_utxos[index];
            current_waste = current_waste.checked_add(utxo_waste)?;

            index_selection.push(index);

            // unchecked add is used her for performance.  Since the sum of all utxo values
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
fn index_to_utxo_list(
    index_list: Option<Vec<usize>>,
    wu: Vec<(Amount, SignedAmount, &WeightedUtxo)>,
) -> Option<std::vec::IntoIter<&'_ WeightedUtxo>> {
    // Doing this to satisfy the borrow checker such that the
    // refs &WeightedUtxo in `wu` have the same lifetime as the
    // returned &WeightedUtxo.
    let origin: Vec<_> = wu.iter().map(|(_, _, u)| *u).collect();
    let mut result = origin.clone();
    result.clear();

    // copy over the origin iterms into result that are present
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
    use crate::WeightedUtxo;
    use bitcoin::Amount;
    use bitcoin::ScriptBuf;
    use bitcoin::SignedAmount;
    use bitcoin::TxOut;
    use bitcoin::Weight;
    use core::str::FromStr;

    fn create_weighted_utxos(fee: Amount) -> Vec<WeightedUtxo> {
        let amts = [
            Amount::from_str("1 cBTC").unwrap() + fee,
            Amount::from_str("2 cBTC").unwrap() + fee,
            Amount::from_str("3 cBTC").unwrap() + fee,
            Amount::from_str("4 cBTC").unwrap() + fee,
        ];

        amts.iter()
            .map(|amt| WeightedUtxo {
                satisfaction_weight: Weight::ZERO,
                utxo: TxOut { value: *amt, script_pubkey: ScriptBuf::new() },
            })
            .collect()
    }

    #[test]
    fn select_coins_bnb_one() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_two() {
        let target = Amount::from_str("2 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("2 cBTC").unwrap());
    }

    #[test]

    fn select_coins_bnb_three() {
        let target = Amount::from_str("3 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 2);
        assert_eq!(list[0].utxo.value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_four() {
        let target = Amount::from_str("4 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 2);
        assert_eq!(list[0].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_five() {
        let target = Amount::from_str("5 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 2);
        assert_eq!(list[0].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("2 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_six() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_seven() {
        let target = Amount::from_str("7 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_eight() {
        let target = Amount::from_str("8 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_nine() {
        let target = Amount::from_str("9 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("2 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_ten() {
        let target = Amount::from_str("10 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);

        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 4);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[3].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_cost_of_change() {
        let target = Amount::from_str("1 cBTC").unwrap();

        // Since cost of change here is one, we accept any solution
        // between 1 and 2.  Range = (1, 2]
        let cost_of_change = target;

        let weighted_utxos = vec![WeightedUtxo {
            satisfaction_weight: Weight::ZERO,
            utxo: TxOut {
                value: Amount::from_str("1.5 cBTC").unwrap(),
                script_pubkey: ScriptBuf::new(),
            },
        }];

        let wu = weighted_utxos.clone();

        let list: Vec<_> =
            select_coins_bnb(target, cost_of_change, FeeRate::ZERO, FeeRate::ZERO, &wu)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("1.5 cBTC").unwrap());

        let index_list = select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &wu);
        assert!(index_list.is_none());
    }

    #[test]
    fn select_coins_bnb_effective_value() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let fee_rate = FeeRate::from_sat_per_kwu(10);
        let satisfaction_weight = Weight::from_wu(204);

        let weighted_utxos = vec![WeightedUtxo {
            satisfaction_weight,
            utxo: TxOut {
                // This would be a match using value, however since effective_value is used
                // the effective_value is calculated, this will fall short of the target.
                value: Amount::from_str("1 cBTC").unwrap(),
                script_pubkey: ScriptBuf::new(),
            },
        }];

        let wu = weighted_utxos.clone();
        let index_list = select_coins_bnb(target, Amount::ZERO, fee_rate, fee_rate, &wu);
        assert!(index_list.is_none());
    }

    #[test]
    fn select_coins_bnb_skip_effective_negative_effective_value() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let fee_rate = FeeRate::from_sat_per_kwu(10);
        let satisfaction_weight = Weight::from_wu(204);

        // Since cost of change here is one, we accept any solution
        // between 1 and 2.  Range = (1, 2]
        let cost_of_change = target;

        let weighted_utxos = vec![
            WeightedUtxo {
                satisfaction_weight: Weight::ZERO,
                utxo: TxOut {
                    value: Amount::from_str("1.5 cBTC").unwrap(),
                    script_pubkey: ScriptBuf::new(),
                },
            },
            WeightedUtxo {
                satisfaction_weight,
                utxo: TxOut {
                    // If this had no fee, a 1 sat utxo would be included since
                    // there would be less waste.  However, since there is a weight
                    // and fee to spend it, the effective value is negative, so
                    // it will not be included.
                    value: Amount::from_str("1 sat").unwrap(),
                    script_pubkey: ScriptBuf::new(),
                },
            },
        ];

        let wu = weighted_utxos.clone();
        let list: Vec<_> =
            select_coins_bnb(target, cost_of_change, fee_rate, fee_rate, &wu).unwrap().collect();
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("1.5 cBTC").unwrap());
    }

    #[test]
    fn select_coins_bnb_target_greater_than_value() {
        let target = Amount::from_str("11 cBTC").unwrap();
        let weighted_utxos = create_weighted_utxos(Amount::ZERO);
        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos);
        assert!(list.is_none());
    }

    #[test]
    fn select_coins_bnb_consume_more_inputs_when_cheap() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let fee = Amount::from_str("2 sats").unwrap();
        let weighted_utxos = create_weighted_utxos(fee);

        let fee_rate = FeeRate::from_sat_per_kwu(10);
        let lt_fee_rate = FeeRate::from_sat_per_kwu(20);

        // the possible combinations are 2,4 or 1,2,3
        // fees are cheap, so use 1,2,3
        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, fee_rate, lt_fee_rate, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("3 cBTC").unwrap() + fee);
        assert_eq!(list[1].utxo.value, Amount::from_str("2 cBTC").unwrap() + fee);
        assert_eq!(list[2].utxo.value, Amount::from_str("1 cBTC").unwrap() + fee);
    }

    #[test]
    fn select_coins_bnb_consume_less_inputs_when_expensive() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let fee = Amount::from_str("4 sats").unwrap();
        let weighted_utxos = create_weighted_utxos(fee);

        let fee_rate = FeeRate::from_sat_per_kwu(20);
        let lt_fee_rate = FeeRate::from_sat_per_kwu(10);

        // the possible combinations are 2,4 or 1,2,3
        // fees are expensive, so use 2,4
        let list: Vec<_> =
            select_coins_bnb(target, Amount::ZERO, fee_rate, lt_fee_rate, &weighted_utxos)
                .unwrap()
                .collect();

        assert_eq!(list.len(), 2);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap() + fee);
        assert_eq!(list[1].utxo.value, Amount::from_str("2 cBTC").unwrap() + fee);
    }

    #[test]
    fn select_coins_bnb_utxo_pool_sum_overflow() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let satisfaction_weight = Weight::from_wu(204);
        let value = SignedAmount::MAX.to_unsigned().unwrap();
        let weighted_utxos = vec![
            WeightedUtxo {
                satisfaction_weight,
                utxo: TxOut { value, script_pubkey: ScriptBuf::new() },
            },
            WeightedUtxo {
                satisfaction_weight,
                utxo: TxOut { value, script_pubkey: ScriptBuf::new() },
            },
        ];
        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos);
        assert!(list.is_none());
    }

    #[test]
    fn select_coins_bnb_upper_bound_overflow() {
        // the upper_bound is target + cost_of_change.
        // adding these two together returns NONE on overflow.
        let target = Amount::MAX;
        let cost_of_change = Amount::MAX;

        let satisfaction_weight = Weight::from_wu(204);
        let weighted_utxos = vec![WeightedUtxo {
            satisfaction_weight,
            utxo: TxOut { value: target, script_pubkey: ScriptBuf::new() },
        }];

        let list =
            select_coins_bnb(target, cost_of_change, FeeRate::ZERO, FeeRate::ZERO, &weighted_utxos);
        assert!(list.is_none());
    }
}
