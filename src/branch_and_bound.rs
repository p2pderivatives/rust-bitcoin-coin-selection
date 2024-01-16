// SPDX-License-Identifier: CC0-1.0
//
//! Bitcoin Branch and Bound Selection.
//!
//! This module introduces the Branch and Bound Coin Selection Algorithm.

use crate::WeightedUtxo;
use bitcoin::Amount;
use bitcoin::FeeRate;

/// Select coins bnb performs a depth first branch and bound search on binary tree.
///
/// See also core: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>
///
/// Returns a collection of `WeightedUtxo` that meet or exceed the target `Amount` when summed.
/// The collection returned seeks to minimize the waste, which is the difference between the target
/// `Amount` and sum of the `WeightedUtxo` collection.  If no match can be found, an empty
/// collection is returned wrapped by the option type.  However, if an un-expected error was
/// encountered, `None` is returned.
///
/// # Returns
/// * `Some(Vec<WeightedUtxo>)` where `Vec<WeightedUtxo>` is not empty on match.
/// * `Some(vec![])` if no match could be fouund.
/// * `None` if some un-expected behavior occurred such as an overflow.
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
// Start at 4 and try including 4 in the total the first loop.  We therefore have a tree with only
// one root node that is less than the total, so the next iteration occurs.  The second iteration
// examines a tree where 4 is the root and the left branch is 3.
//      o
//     /
//    4
//   /
//  3
//
// At this point, the total is determined to be 7 which exceeds the target of 5.  We therefore
// remove 3 from the left branch and it becomes the right branch since 3 is now excluded
// (backtrack).
//      o
//     /
//    4
//   / \
//      3
//
// We next try including 2 on the left branch of 3 (add 2 to the inclusion branch).
//      o
//     /
//    4
//   / \
//      3
//     /
//    2
//
// The sum is now 6, since the sum of the right branch totals 6.  Once again, we find the total
// exceeds 5, so we explore the exclusion branch of 2.
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
// matching 5.  Both 4 and 1 are on the left inclusion branch.  We therefore record our solution
// and backtrack to next try the exclusion branch of our root node 4.
//      o
//     / \
//    4
//   / \
//      3
//     / \
//        2
//       /
//      1
//
// We try excluding 4 now
//      o
//     / \
//        4
//       / \
//      3
//
// 3 is less than our target, so we next add 2 to our inclusion branch
//      o
//     / \
//        4
//       / \
//      3
//     /
//    2
//
// We now stop our search again noticing that 3 and 2 equals our target as 5, and since this
// solution was found last, then [3, 2] overwrites the previously found solution [4, 1].  We next
// backtrack and exclude our root node of this sub tree 3.  Since our new sub tree starting at 2
// doesn't have enough value left to meet the target, we conclude our search at [3, 2].
pub fn select_coins_bnb(
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    weighted_utxos: &mut [WeightedUtxo],
) -> Option<Vec<&WeightedUtxo>> {
    // Total_Tries in Core:
    // https://github.com/bitcoin/bitcoin/blob/1d9da8da309d1dbf9aef15eb8dc43b4a2dc3d309/src/wallet/coinselection.cpp#L74
    const ITERATION_LIMIT: i32 = 100_000;

    let mut iteration = 0;
    let mut index = 0;
    let mut backtrack;
    let mut backtrack_subtree;

    let mut value = Amount::ZERO;
    let mut waste = Amount::MAX_MONEY;

    let mut index_selection: Vec<usize> = vec![];
    let mut best_selection: Option<Vec<usize>> = None;

    // Create a tuple of (effective_value, weighted_utxo) and filter out negative values
    // and errors (effective_values that are None).  The effective_value will be used
    // during the coin-selection process, and the weighted_utxo is index into on return.
    let mut effective_values: Vec<(Amount, &WeightedUtxo)> = weighted_utxos
        .iter()
        .map(|wu| (wu.effective_value(fee_rate), wu))
        .filter(|(eff_val, _)| !eff_val.is_none())
        .map(|(eff_val, wu)| (eff_val.unwrap(), wu))
        .filter(|(eff_val, _)| eff_val.is_positive())
        .map(|(eff_val, wu)| (eff_val.to_unsigned().unwrap(), wu))
        .collect();

    effective_values.sort_by_key(|u| u.0);
    effective_values.reverse();

    // TODO check for overflow
    let mut available_value = effective_values.iter().fold(Amount::ZERO, |mut s, &(v, _)| {
        s += v;
        s
    });

    if available_value < target {
        return Some(Vec::new());
    }

    while iteration < ITERATION_LIMIT {
        // There are two conditions for backtracking:
        //
        // 1_ Not enough value to make it to target.
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
        //      3
        //     / \
        //        2
        //       /
        //      1
        //
        // To:
        //      o
        //     / \
        //        4
        //       / \
        //      3
        //
        //
        // 2_ value meets or exceeded target.
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
        //     /
        //    4
        //   / \
        //      3

        // Set initial loop state
        backtrack = false;
        backtrack_subtree = false;

        // * not enough value to make it to the target.
        //   Therefore, explore a new new subtree.
        if available_value + value < target {
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
        else if value > target + cost_of_change {
            backtrack = true;
        }
        // * value meets or exceeds the target.
        //   Record the solution and the waste then continue.
        //
        // Check if index_selection is better than the previous known best, and
        // update best_selection accordingly.
        else if value >= target {
            backtrack = true;

            let current_waste = value - target;

            if current_waste <= waste {
                best_selection = Some(index_selection.clone());
                waste = current_waste;
            }
        }

        // * Backtrack
        if backtrack {
            let last_index = index_selection.pop().unwrap();
            let (eff_value, _) = effective_values[last_index];
            value -= eff_value;
            index -= 1;
            assert_eq!(index, last_index);
        }
        // * Backtrack to new tree
        else if backtrack_subtree {
            // No new subtree left to explore.
            if index_selection.is_empty() {
                return index_to_utxo_list(best_selection, effective_values);
            }

            // Anchor the new subtree at the next available index.
            // The next iteration, the index will be incremented by one.
            index = index_selection[0];

            // The available value of the next iteration.  This should never overflow
            // since the value is always less than the last available_value calculation.
            available_value =
                effective_values[index + 1..].iter().fold(Amount::ZERO, |mut s, &(v, _)| {
                    s += v;
                    s
                });

            // If the new subtree does not have enough value, we are done searching.
            if available_value < target {
                return index_to_utxo_list(best_selection, effective_values);
            }

            // Start a new selection and add the root of the new subtree to the index selection.
            index_selection.clear();
            value = Amount::ZERO;
        }
        // * Add next node to the inclusion branch.
        else {
            let (eff_value, _) = effective_values[index];

            index_selection.push(index);
            value += eff_value;
            available_value -= eff_value;
        }

        index += 1;
        iteration += 1;
    }

    index_to_utxo_list(best_selection, effective_values)
}

fn index_to_utxo_list(
    index_list: Option<Vec<usize>>,
    effective_values: Vec<(Amount, &WeightedUtxo)>,
) -> Option<Vec<&WeightedUtxo>> {
    index_list.map(|i_list| i_list.iter().map(|i: &usize| effective_values[*i].1).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::WeightedUtxo;
    use bitcoin::Amount;
    use bitcoin::ScriptBuf;
    use bitcoin::TxOut;
    use bitcoin::Weight;
    use core::str::FromStr;

    fn create_weighted_utxos() -> Vec<WeightedUtxo> {
        let amts = [
            Amount::from_str("1 cBTC").unwrap(),
            Amount::from_str("2 cBTC").unwrap(),
            Amount::from_str("3 cBTC").unwrap(),
            Amount::from_str("4 cBTC").unwrap(),
        ];

        amts.iter()
            .map(|amt| WeightedUtxo {
                satisfaction_weight: Weight::ZERO,
                utxo: TxOut { value: *amt, script_pubkey: ScriptBuf::new() },
            })
            .collect()
    }

    #[test]
    fn one() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn two() {
        let target = Amount::from_str("2 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("2 cBTC").unwrap());
    }

    #[test]
    fn three() {
        let target = Amount::from_str("3 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 2);
        assert_eq!(list[0].utxo.value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn four() {
        let target = Amount::from_str("4 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 2);
        assert_eq!(list[0].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn five() {
        let target = Amount::from_str("5 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 2);
        assert_eq!(list[0].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("2 cBTC").unwrap());
    }

    #[test]
    fn six() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn seven() {
        let target = Amount::from_str("7 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn eight() {
        let target = Amount::from_str("8 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn nine() {
        let target = Amount::from_str("9 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 3);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("2 cBTC").unwrap());
    }

    #[test]
    fn ten() {
        let target = Amount::from_str("10 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list.len(), 4);
        assert_eq!(list[0].utxo.value, Amount::from_str("4 cBTC").unwrap());
        assert_eq!(list[1].utxo.value, Amount::from_str("3 cBTC").unwrap());
        assert_eq!(list[2].utxo.value, Amount::from_str("2 cBTC").unwrap());
        assert_eq!(list[3].utxo.value, Amount::from_str("1 cBTC").unwrap());
    }

    #[test]
    fn cost_of_change() {
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

        let mut wu = weighted_utxos.clone();

        let list = select_coins_bnb(target, cost_of_change, FeeRate::ZERO, &mut wu).unwrap();

        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("1.5 cBTC").unwrap());

        let index_list = select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut wu);
        assert_eq!(index_list, None);
    }

    #[test]
    fn effective_value() {
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

        let mut wu = weighted_utxos.clone();
        let index_list = select_coins_bnb(target, Amount::ZERO, fee_rate, &mut wu).unwrap();
        assert!(index_list.is_empty());
    }

    #[test]
    fn skip_effective_negative_effective_value() {
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

        let mut wu = weighted_utxos.clone();
        let list = select_coins_bnb(target, cost_of_change, fee_rate, &mut wu).unwrap();
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].utxo.value, Amount::from_str("1.5 cBTC").unwrap());
    }

    #[test]
    fn target_greater_than_value() {
        let target = Amount::from_str("11 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert!(list.is_empty());
    }

    // TODO - rework this test.
    //#[test]
    //fn utxo_pool_sum_overflow() {
    //let target = Amount::from_str("1 cBTC").unwrap();
    //let satisfaction_weight = Weight::from_wu(204);
    //let mut weighted_utxos = vec![
    //WeightedUtxo {
    //satisfaction_weight,
    //utxo: TxOut { value: Amount::MAX, script_pubkey: ScriptBuf::new() },
    //},
    //WeightedUtxo {
    //satisfaction_weight,
    //utxo: TxOut { value: Amount::MAX, script_pubkey: ScriptBuf::new() },
    //},
    //];

    //let list = select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos);
    //assert!(list.is_none());
    //}
}
