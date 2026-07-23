// SPDX-License-Identifier: CC0-1.0
//
//! Coin Grinder.
//!
//! This module introduces the Coin Grinder selection algorithm.
//!
use bitcoin_units::{Amount, Weight};

use crate::OverflowError::Addition;
use crate::SelectionError::{
    InsufficentFunds, IterationLimitReached, MaxWeightExceeded, Overflow, SolutionNotFound,
};
use crate::{Return, WeightedUtxo};

const ITERATION_LIMIT: u32 = 100_000;

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

// Provides a lookup to determine the minimum UTXO weight after a given index.
fn build_min_tail_weight(weighted_utxos: Vec<&WeightedUtxo>) -> Vec<Weight> {
    let weights: Vec<_> = weighted_utxos.into_iter().map(|u| u.weight()).rev().collect();
    let mut prev = Weight::MAX;
    let mut result = Vec::new();
    for w in weights {
        result.push(prev);
        prev = std::cmp::min(prev, w);
    }
    result.into_iter().rev().collect()
}

fn index_to_utxo_list(
    iterations: u32,
    index_list: Vec<usize>,
    max_tx_weight_exceeded: bool,
    wu: Vec<&WeightedUtxo>,
) -> Return<'_> {
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

// Estimate if any combination of remaining inputs would be higher than `best_weight`
fn is_remaining_weight_higher(
    weight_total: Weight,
    min_tail_weight: Weight,
    target: Amount,
    amount_total: Amount,
    tail_amount: Amount,
    best_weight: Weight,
) -> Option<bool> {
    // amount remaining until the target is reached.
    let remaining_amount = target.checked_sub(amount_total)?;

    // number of inputs left to reach the target.
    let utxo_count = remaining_amount.to_sat().div_ceil(tail_amount.to_sat());

    // sum of input weights if all inputs are the best possible weight.
    let remaining_weight = min_tail_weight * utxo_count;

    // add remaining_weight to the current running weight total.
    let best_possible_weight = weight_total + remaining_weight;

    Some(best_possible_weight > best_weight)
}

/// Deterministic Branch and Bound search that minimizes the input weight.
///
/// This algorithm selects the set of inputs that meets the total target and has the lowest
/// total weight.  The total target includes a `change_target` to budget for creating a change
/// output.  Therefore, the total target is at least target + change_target.  That is, the range
/// of possible solutions falls within [target + change_output, INF].
///
/// See also: [bitcoin coin selection](https://github.com/bitcoin/bitcoin/blob/62bd61de110b057cbfd6e31e4d0b727d93119c72/src/wallet/coinselection.cpp#L204)
///
/// See discussion [here](https://murch.one/erhardt2016coinselection.pdf) at section 6.4.3
/// that prioritizing input weight will lead to a fragmentation of the UTXO set.  Therefore, prefer
/// this search only when fee_rate is high, since a set of UTXOs with minimal weight will lead to a
/// cheaper constructed transaction in the short term.  However, in the long-term, this
/// prioritization can lead to more UTXOs to choose from (fragmentation).
///
/// # Parameters
///
/// * target: Target spend `Amount`
/// * change_target: The minimum `Amount` that is budgeted for creating a change output.
///   Therefore, solution reange is [target + change_target, inf] inclusive.
/// * max_selection_weight: The maximum allowable selection weight
/// * fee_rate: The fee_rate used to calculate the effective_value of each candidate Utxo
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from
///
/// # Returns
///
/// A tuple `(u32, Vec<&'a WeightedUtxo>` is returned on success where `u32` is the number of
/// iterations to find the solution and `Vec<&'a WeightedUtxo>` is the best found selection.
/// Note that if the iteration count equals `ITERATION_LIMIT`, a better solution may exist than the
/// one found.
pub fn coin_grinder<'a, T: IntoIterator<Item = &'a WeightedUtxo> + std::marker::Copy>(
    target: Amount,
    change_target: Amount,
    max_selection_weight: Weight,
    weighted_utxos: T,
) -> Return<'a> {
    weighted_utxos
        .into_iter()
        .map(|u| u.weight())
        .try_fold(Weight::ZERO, Weight::checked_add)
        .ok_or(Overflow(Addition))?;

    let available_value = weighted_utxos
        .into_iter()
        .map(|u| u.effective_value())
        .try_fold(Amount::ZERO, Amount::checked_add)
        .ok_or(Overflow(Addition))?;

    let mut weighted_utxos: Vec<_> = weighted_utxos.into_iter().collect();
    weighted_utxos.sort();

    let lookahead = build_lookahead(weighted_utxos.clone(), available_value);
    let min_tail_weight = build_min_tail_weight(weighted_utxos.clone());

    let total_target = target.checked_add(change_target).ok_or(Overflow(Addition))?;

    if available_value < total_target {
        return Err(InsufficentFunds);
    }

    if weighted_utxos.is_empty() {
        return Err(SolutionNotFound);
    }

    if target == Amount::ZERO {
        return Err(SolutionNotFound);
    }

    let mut selection: Vec<usize> = vec![];
    let mut best_selection: Vec<usize> = vec![];

    let mut amount_total: Amount = Amount::ZERO;
    let mut best_amount: Amount = Amount::MAX;

    let mut weight_total: Weight = Weight::ZERO;
    let mut best_weight: Weight = max_selection_weight;
    let mut max_tx_weight_exceeded = false;

    let mut next_utxo_index = 0;
    let mut iteration: u32 = 0;

    loop {
        // Given a target of 11, and candidate set: [10/2, 7/1, 5/1, 4/2]
        //
        //      o
        //     /
        //  10/2
        //   /
        // 17/3
        //
        // A solution 17/3 is recorded, however the total of 11 is exceeded.
        // Therefor, 7/1 is shifted to the exclusion branch and 5/1 is added.
        //
        //      o
        //     / \
        //  10/2
        //   / \
        //   17/3
        //    /
        //  15/3
        //
        // This operation happens when "shift" is true.  That is, move from
        // the inclusion branch 17/3 via the omission branch 10/2 to it's
        // inclusion-branch child 15/3
        let mut shift = false;

        // Given a target of 11, and candidate set: [10/2, 7/1, 5/1, 4/2]
        // Solutions, 17/3 (shift) 15/3 (shift) and 14/4 are evaluated.
        //
        // At this point, the leaf node 14/4 makes a shift impossible
        // since there is not an inclusion-branch child.  In other words,
        // this is a leaf node.
        //
        //      o
        //     /
        //  10/2
        //    \
        //     \
        //     /
        //   14/4
        //
        // Instead we go to the omission branch of the nodes last ancestor.
        // That is, we "cut" removing every child of 10/2 and shift 10/2
        // to the omission branch.
        //
        //      o
        //     / \
        //      10/2
        let mut cut = false;

        let utxo = weighted_utxos[next_utxo_index];
        let eff_value = utxo.effective_value();

        amount_total = (amount_total + eff_value).unwrap();
        weight_total += utxo.weight();

        selection.push(next_utxo_index);
        next_utxo_index += 1;
        iteration += 1;

        let tail: usize = *selection.last().unwrap();
        if (amount_total + lookahead[tail]).unwrap() < total_target {
            cut = true;
        } else if weight_total > best_weight {
            max_tx_weight_exceeded = true;
            if weighted_utxos[tail].weight() <= min_tail_weight[tail] {
                cut = true;
            } else {
                shift = true;
            }
        } else if amount_total >= total_target {
            shift = true;
            if weight_total < best_weight
                || weight_total == best_weight && amount_total < best_amount
            {
                best_selection = selection.clone();
                best_weight = weight_total;
                best_amount = amount_total;
            }
        } else if !best_selection.is_empty() {
            if let Some(is_higher) = is_remaining_weight_higher(
                weight_total,
                min_tail_weight[tail],
                total_target,
                amount_total,
                weighted_utxos[tail].effective_value(),
                best_weight,
            ) {
                if is_higher {
                    if weighted_utxos[tail].weight() <= min_tail_weight[tail] {
                        cut = true;
                    } else {
                        shift = true;
                    }
                }
            }
        }

        if iteration >= ITERATION_LIMIT {
            return index_to_utxo_list(
                iteration,
                best_selection,
                max_tx_weight_exceeded,
                weighted_utxos,
            );
        }

        // check if evaluating a leaf node.
        if next_utxo_index == weighted_utxos.len() {
            cut = true;
        }

        if cut {
            // deselect
            let utxo = weighted_utxos[*selection.last().unwrap()];
            let eff_value = utxo.effective_value();

            amount_total = (amount_total - eff_value).unwrap();
            weight_total -= utxo.weight();
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

            next_utxo_index = selection.last().unwrap() + 1;

            // deselect
            let utxo = weighted_utxos[*selection.last().unwrap()];
            let eff_value = utxo.effective_value();

            amount_total = (amount_total - eff_value).unwrap();
            weight_total -= utxo.weight();
            selection.pop();

            shift = false;

            // skip all next inputs that are equivalent to the current input
            // if the current input didn't contribute to a solution.
            while weighted_utxos[next_utxo_index - 1].effective_value()
                == weighted_utxos[next_utxo_index].effective_value()
            {
                if next_utxo_index >= weighted_utxos.len() - 1 {
                    shift = true;
                    break;
                }
                next_utxo_index += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {}
