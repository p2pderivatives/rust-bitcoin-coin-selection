//! Rust Bitcoin coin selection library.
//!
//! This library provides efficient algorithms to compose a set of unspent transaction outputs
//! (UTXOs).

// Coding conventions.
#![deny(non_upper_case_globals)]
#![deny(non_camel_case_types)]
#![deny(non_snake_case)]
#![deny(unused_mut)]
#![deny(missing_docs)]
// Experimental features we need.
#![cfg_attr(bench, feature(test))]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(bench)]
extern crate test;

mod single_random_draw;

use bitcoin::amount::CheckedSum;
use bitcoin::blockdata::transaction::effective_value;
use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::TxOut;
use bitcoin::Weight;

use crate::single_random_draw::select_coins_srd;
use rand::thread_rng;

/// Trait that a UTXO struct must implement to be used as part of the coin selection
/// algorithm.
pub trait Utxo: Clone {
    /// Return the value of the UTXO.
    fn get_value(&self) -> u64;
}

// https://github.com/bitcoin/bitcoin/blob/f722a9bd132222d9d5cd503b5af25c905b205cdb/src/wallet/coinselection.h#L20
const CHANGE_LOWER: Amount = Amount::from_sat(50_000);

/// This struct contains the weight of all params needed to satisfy the UTXO.
///
/// The idea of using a WeightUtxo type was inspired by the BDK implementation:
/// <https://github.com/bitcoindevkit/bdk/blob/feafaaca31a0a40afc03ce98591d151c48c74fa2/crates/bdk/src/types.rs#L181>
#[derive(Clone, Debug, PartialEq)]
// note, change this to private?  No good reason to be public.
pub struct WeightedUtxo {
    /// The satisfaction_weight is the size of the required params to satisfy the UTXO.
    pub satisfaction_weight: Weight,
    /// The corresponding UTXO.
    pub utxo: TxOut,
}

/// Select coins first using BnB algorithm similar to what is done in bitcoin
/// core see: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>,
/// and falls back on a random UTXO selection. Returns none if the target cannot
/// be reached with the given utxo pool.
/// Requires compilation with the "rand" feature.
#[cfg(feature = "rand")]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins<T: Utxo>(
    target: Amount,
    cost_of_change: Amount,
    fee_rate: FeeRate,
    weighted_utxos: &mut [WeightedUtxo],
) -> Option<Vec<WeightedUtxo>> {
    let coins = select_coins_bnb(target, cost_of_change, fee_rate, weighted_utxos);

    if coins.is_none() {
        select_coins_srd(target, fee_rate, weighted_utxos, &mut thread_rng())
    } else {
        coins
    }
}

fn index_to_utxo_list(
    index_list: Option<Vec<usize>>,
    weighted_utxos: &mut [WeightedUtxo],
) -> Option<Vec<WeightedUtxo>> {
    index_list.map(|i_list| i_list.iter().map(|i: &usize| weighted_utxos[*i].clone()).collect())
}

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
/// * Some(Vec<WeightedUtxo>) where Vec<WeightedUtxo> is not empty on match.
/// * Some(vec![]) if no match could be fouund.
/// * None if some un-expected behavior occurred such as an overflow.
///
/// # Arguments
/// * `target` - Target spend `Amount`
/// * `cost_of_change` - The `Amount` needed to produce a change output
/// * `fee_rate` - `FeeRate` used to calculate each effective_value output value
/// * `weighted_utxos` - The candidate Weighted UTXOs from which to choose a selection from

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
) -> Option<Vec<WeightedUtxo>> {
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
    let mut utxo_candidate_amounts: Vec<Amount> = vec![];

    for u in &mut *weighted_utxos {
        let effective_value = effective_value(fee_rate, u.satisfaction_weight, u.utxo.value)?;

        // Discard negative effective values.
        let amount = match effective_value.to_unsigned() {
            Ok(amt) => amt,
            Err(_) => continue,
        };

        utxo_candidate_amounts.push(amount);
    }

    let mut available_value = utxo_candidate_amounts.iter().cloned().checked_sum()?;

    if available_value < target {
        return Some(Vec::new());
    }

    utxo_candidate_amounts.sort();
    utxo_candidate_amounts.reverse();

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
            value -= utxo_candidate_amounts[last_index];
            index -= 1;
            assert_eq!(index, last_index);
        }
        // * Backtrack to new tree
        else if backtrack_subtree {
            // No new subtree left to explore.
            if index_selection.is_empty() {
                return index_to_utxo_list(best_selection, weighted_utxos);
            }

            // Anchor the new subtree at the next available index.
            // The next iteration, the index will be incremented by one.
            index = index_selection.remove(0);

            // The available value of the next iteration.
            available_value = utxo_candidate_amounts[index + 1..].iter().cloned().checked_sum()?;

            // If the new subtree does not have enough value, we are done searching.
            if available_value < target {
                return index_to_utxo_list(best_selection, weighted_utxos);
            }

            // Start a new selection and add the root of the new subtree to the index selection.
            index_selection.clear();
            value = Amount::ZERO;
        }
        // * Add next node to the inclusion branch.
        else {
            let utxo_value = utxo_candidate_amounts[index];

            index_selection.push(index);
            value += utxo_value;
            available_value -= utxo_value;
        }

        index += 1;
        iteration += 1;
    }

    index_to_utxo_list(best_selection, weighted_utxos)
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

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn two() {
        let target = Amount::from_str("2 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![2];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn three() {
        let target = Amount::from_str("3 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![2, 3];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn four() {
        let target = Amount::from_str("4 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![1, 3];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn five() {
        let target = Amount::from_str("5 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![1, 2];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn six() {
        let target = Amount::from_str("6 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![1, 2, 3];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn seven() {
        let target = Amount::from_str("7 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![0, 2, 3];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn eight() {
        let target = Amount::from_str("8 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![0, 1, 3];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn nine() {
        let target = Amount::from_str("9 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![0, 1, 2];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn ten() {
        let target = Amount::from_str("10 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let expected_i_list = vec![0, 1, 2, 3];

        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
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

        let list =
            select_coins_bnb(target, cost_of_change, FeeRate::ZERO, &mut weighted_utxos.clone())
                .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));

        let index_list = select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos);
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

        let index_list =
            select_coins_bnb(target, Amount::ZERO, fee_rate, &mut weighted_utxos.clone()).unwrap();
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

        let list = select_coins_bnb(target, cost_of_change, fee_rate, &mut weighted_utxos.clone())
            .unwrap();
        assert_eq!(list, expected_list(expected_i_list, &mut weighted_utxos));
    }

    #[test]
    fn target_greater_than_value() {
        let target = Amount::from_str("11 cBTC").unwrap();
        let mut weighted_utxos = create_weighted_utxos();
        let list =
            select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos).unwrap();
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

        let list = select_coins_bnb(target, Amount::ZERO, FeeRate::ZERO, &mut weighted_utxos);

        assert!(list.is_none());
    }
}

#[cfg(bench)]
mod benches {
    use crate::select_coins_bnb;
    use crate::Utxo;
    use test::Bencher;

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct MinimalUtxo {
        value: u64,
    }

    impl Utxo for MinimalUtxo {
        fn get_value(&self) -> u64 {
            self.value
        }
    }

    #[bench]
    /// Creates a UTXO pool of 1,000 coins that do not match and one coin
    /// that will be a match when combined with any of the other 1,000 coins.
    ///
    /// Matching benchmark of Bitcoin core coin-selection benchmark.
    // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/bench/coin_selection.cpp#L44
    fn bench_select_coins_bnb(bh: &mut Bencher) {
        // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/consensus/amount.h#L15
        /// The amount of satoshis in one BTC.
        const COIN: u64 = 100_000_000;

        // https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.h#L18
        /// lower bound for randomly-chosen target change amount
        const CHANGE_LOWER: u64 = 50_000;

        let u = MinimalUtxo { value: 1000 * COIN };
        let mut utxo_pool = vec![u; 1000];
        utxo_pool.push(MinimalUtxo { value: 3 * COIN });

        bh.iter(|| {
            let result =
                select_coins_bnb(1003 * COIN, CHANGE_LOWER, &mut utxo_pool.clone()).unwrap();
            assert_eq!(2, result.len());
            assert_eq!(1000 * COIN, result[0].value);
            assert_eq!(3 * COIN, result[1].value);
        });
    }
}
