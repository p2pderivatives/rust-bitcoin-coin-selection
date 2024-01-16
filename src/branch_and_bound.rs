// SPDX-License-Identifier: CC0-1.0
//
//! Bitcoin Branch and Bound Selection.
//!
//! This module introduces the Branch and Bound Coin Selection Algorithm.

use crate::WeightedUtxo;
use bitcoin::amount::CheckedSum;
use bitcoin::transaction::effective_value;
use bitcoin::Amount;
use bitcoin::SignedAmount;
use bitcoin::FeeRate;
use core::cmp::Reverse;

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
    long_term_fee_rate: FeeRate,
    weighted_utxos: &mut [WeightedUtxo],
) -> Option<Vec<WeightedUtxo>> {
    println!("* bnb start *");
    // Total_Tries in Core:
    // https://github.com/bitcoin/bitcoin/blob/1d9da8da309d1dbf9aef15eb8dc43b4a2dc3d309/src/wallet/coinselection.cpp#L74
    const ITERATION_LIMIT: i32 = 100_000;

    //println!("fee_rate: {:?} long_term_fee_rate: {:?}", fee_rate, long_term_fee_rate);

    let mut iteration = 0;
    let mut index = 0;
    let mut backtrack;
    let mut backtrack_subtree;

    let mut value = Amount::ZERO;
    let mut waste = Amount::MAX_MONEY;
    let mut best_future_fee = SignedAmount::MAX_MONEY;

    // given a utxo_pool of [4,3,2,1] and a target of 6, we may select
    // 3,2,1.  However, if the fee environment is high, where long_term_fee = 1
    // and fee = 2, then future_fee_diff 3 * 1 = 3.  However, a secondary
    // selection is 4,2 where future_fee_diff is 2 * 1 = 2.
    //let mut future_fee = Amount::ZERO;

    let mut index_selection: Vec<usize> = vec![];
    let mut best_selection: Option<Vec<usize>> = None;
    let mut utxo_candidate_amounts: Vec<(Amount, SignedAmount)> = vec![];
    let mut available_value = Amount::ZERO;
    let mut future_fee = SignedAmount::ZERO;

    for u in &mut *weighted_utxos {
        let effective_value = effective_value(fee_rate, u.satisfaction_weight, u.utxo.value)?;

        // Discard negative effective values.
        let amount = match effective_value.to_unsigned() {
            Ok(amt) => amt,
            Err(_) => continue,
        };

        available_value += amount;

        // TODO used checked versions of this.
        let fee = fee_rate * u.satisfaction_weight;
        //println!("fee: {:?}", fee);
        // TODO used checked versions of this.
        let long_term_fee = long_term_fee_rate * u.satisfaction_weight;
        //println!("long_teram_fee: {:?}", fee);
        // TODO used checked versions of this.
        let future_fee_diff: SignedAmount = fee.to_signed().unwrap() - long_term_fee.to_signed().unwrap(); 

        //println!("differnetial: {}", future_fee_diff);

        utxo_candidate_amounts.push((amount, future_fee_diff));
    }

    //println!("utxo_candidate_amounts: {:?}", utxo_candidate_amounts);

    if available_value < target {
        return Some(Vec::new());
    }

    utxo_candidate_amounts.sort();
    utxo_candidate_amounts.reverse();

    //println!("{:?}", utxo_candidate_amounts);
    while iteration < ITERATION_LIMIT {
        //println!("value: {:?} target: {:?} index: {:?}", value, target, index);
        //println!("future fee: {:?} value: {:?} best future fee: {:?}", future_fee, value, best_future_fee);
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
            println!("potential match at index_selection: {:?}", index_selection);
            backtrack = true;

            let current_waste = value - target;
            println!("current_waste: {:?} future_fee: {:?}", current_waste, future_fee);

            //println!("** check future fee: {}", future_fee);
            //println!("check conditions for recording a result");
            //println!("value: {:?}, current_waste: {:?}, waste: {:?}, future_fee: {:?}, best_future_fee: {:?}", value, current_waste, waste, future_fee, best_future_fee);
            if current_waste <= waste && future_fee <= best_future_fee {
                //println!("updating selection {:?}", index_selection);
                best_selection = Some(index_selection.clone());
                best_future_fee = future_fee;
                waste = current_waste;
            }
        }

        // * Backtrack
        if backtrack {
            let last_index = index_selection.pop().unwrap();
            let (v, f) = utxo_candidate_amounts[last_index];
            value -= v;
            future_fee -= f;
            index -= 1;
            assert_eq!(index, last_index);
        }
        // * Backtrack to new tree
        else if backtrack_subtree {
            println!("** perf subtree backtrack at index: {} index_selection: {:?}", index, index_selection);
            // No new subtree left to explore.
            if index_selection.is_empty() {
                return index_to_utxo_list(best_selection, weighted_utxos);
            }

            // Anchor the new subtree at the next available index.
            // The next iteration, the index will be incremented by one.
            index = index_selection[0];

            // The available value of the next iteration.  This should never overflow
            // since the value is always less than the last available_value calculation.
            available_value = utxo_candidate_amounts[index + 1..].iter().fold(Amount::ZERO, |mut s, u| {
                s += u.0;
                s
            });

            // If the new subtree does not have enough value, we are done searching.
            if available_value < target {
                println!("done looking. remaining amount: {} at index: {}", available_value, index);
                return index_to_utxo_list(best_selection, weighted_utxos);
            }

            // Start a new selection and add the root of the new subtree to the index selection.
            index_selection.clear();
            value = Amount::ZERO;
            future_fee = SignedAmount::ZERO;
        }
        // * Add next node to the inclusion branch.
        else {
            let (utxo_value, current_future_fee) = utxo_candidate_amounts[index];
            index_selection.push(index);
            println!("{:?}", index_selection);
            future_fee += current_future_fee;
            value += utxo_value;
            available_value -= utxo_value;
        }

        index += 1;
        iteration += 1;
    }

    index_to_utxo_list(best_selection, weighted_utxos)
}

fn index_to_utxo_list(
    index_list: Option<Vec<usize>>,
    weighted_utxos: &mut [WeightedUtxo],
) -> Option<Vec<WeightedUtxo>> {
    weighted_utxos.sort_by_key(|w| Reverse(w.utxo.value));
    index_list.map(|i_list| i_list.iter().map(|i: &usize| weighted_utxos[*i].clone()).collect())
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

    fn expected_list(
        index_list: Vec<usize>,
        weighted_utxos: &mut [WeightedUtxo],
    ) -> Vec<WeightedUtxo> {
        index_to_utxo_list(Some(index_list), weighted_utxos).unwrap()
    }

    #[test]
    fn one() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![3];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn two() {
        let target = Amount::from_str("2 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![2];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn three() {
        let target = Amount::from_str("3 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![2, 3];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn four() {
        let target = Amount::from_str("4 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![1, 3];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn five() {
        let target = Amount::from_str("5 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![1, 2];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn six() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![1, 2, 3];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn seven() {
        let target = Amount::from_str("7 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![0, 2, 3];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn eight() {
        let target = Amount::from_str("8 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![0, 1, 3];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn nine() {
        let target = Amount::from_str("9 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![0, 1, 2];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn ten() {
        let target = Amount::from_str("10 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![0, 1, 2, 3];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn cost_of_change() {
        let target = Amount::from_str("1 cBTC").unwrap();

        // Since cost of change here is one, we accept any solution
        // between 1 and 2.  Range = (1, 2]
        let cost_of_change = target;
        let expected_i_list = vec![0];

        let mut weighted_utxos = vec![WeightedUtxo {
            satisfaction_weight: Weight::ZERO,
            utxo: TxOut {
                value: Amount::from_str("1.5 cBTC").unwrap(),
                script_pubkey: ScriptBuf::new(),
            },
        }];

        let list = select_coins_bnb(
            target,
            cost_of_change,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos.clone(),
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));

        let index_list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        );
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

        let index_list = select_coins_bnb(
            target,
            Amount::ZERO,
            fee_rate,
            FeeRate::ZERO,
            &mut weighted_utxos.clone(),
        )
        .unwrap();
        assert_eq!(index_list, Vec::new());
    }

    #[test]
    fn skip_effective_negative_effective_value() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let fee_rate = FeeRate::from_sat_per_kwu(10);
        let satisfaction_weight = Weight::from_wu(204);
        let expected_i_list = vec![0];

        // Since cost of change here is one, we accept any solution
        // between 1 and 2.  Range = (1, 2]
        let cost_of_change = target;

        let mut weighted_utxos = vec![
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

        let list = select_coins_bnb(
            target,
            cost_of_change,
            fee_rate,
            FeeRate::ZERO,
            &mut weighted_utxos.clone(),
        )
        .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn target_greater_than_value() {
        let target = Amount::from_str("11 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        )
        .unwrap();
        assert_eq!(list, Vec::new());
    }

    #[test]
    fn utxo_pool_sum_overflow() {
        let target = Amount::from_str("1 cBTC").unwrap();
        let mut weighted_utxos = vec![
            WeightedUtxo {
                satisfaction_weight: Weight::ZERO,
                utxo: TxOut { value: Amount::MAX, script_pubkey: ScriptBuf::new() },
            },
            WeightedUtxo {
                satisfaction_weight: Weight::ZERO,
                utxo: TxOut { value: Amount::MAX, script_pubkey: ScriptBuf::new() },
            },
        ];

        let list = select_coins_bnb(
            target,
            Amount::ZERO,
            FeeRate::ZERO,
            FeeRate::ZERO,
            &mut weighted_utxos,
        );

        assert!(list.is_none());
    }

    #[test]
    fn select_less_outputs_if_fee_rate_is_high() {
        let target = Amount::from_str("5.9 cBTC").unwrap();
        let expected_i_list = vec![2, 4];
        let rate = FeeRate::from_sat_per_vb(1).expect("1 sat/byte is valid");
        let satisfaction_weight = Weight::from_wu(204);

        let mut weighted_utxos = vec![
            WeightedUtxo {
                satisfaction_weight,
                utxo: TxOut { value: Amount::from_str("1 cBTC").unwrap(), script_pubkey: ScriptBuf::new() },
            },
            WeightedUtxo {
                satisfaction_weight,
                utxo: TxOut { value: Amount::from_str("2 cBTC").unwrap(), script_pubkey: ScriptBuf::new() },
            },
            WeightedUtxo {
                satisfaction_weight,
                utxo: TxOut { value: Amount::from_str("3 cBTC").unwrap(), script_pubkey: ScriptBuf::new() },
            },
            WeightedUtxo {
                satisfaction_weight,
                utxo: TxOut { value: Amount::from_str("4 cBTC").unwrap(), script_pubkey: ScriptBuf::new() },
            },
        ];

        let list = select_coins_bnb(
            target,
            Amount::from_str("1 cBTC").unwrap(),
            rate,
            FeeRate::ZERO,
            &mut weighted_utxos,
        ).unwrap();
        println!("* results:");
        println!("{:?}", list);
        //assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }
}
