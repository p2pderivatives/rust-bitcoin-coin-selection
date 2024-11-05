// SPDX-License-Identifier: CC0-1.0
//
//! Coin Grinder.
//!
//! This module introduces the Coin Grinder selection Algorithm
//!
/// Coin Grinder is a DFS-based selection Algorithm which optimises for transaction weight.
///
/// # Parameters
///
/// * target: Target spend `Amount`
/// * change_target: A bound on the `Amount` to increase target by with which to create a change
/// output.
/// * max_selection_weight: Maximum allowable selection weight. 
/// * fee_rate: Needed to calculate the effective_value.
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from

use crate::WeightedUtxo;
use bitcoin::Amount;
use bitcoin::FeeRate;
use bitcoin::Weight;
use bitcoin::amount::CheckedSum;

/// Performs a Branch Bound search that prioritizes input weight instead of amount.  That is,
/// select the set of utxos that at least meets the target amount and has the lowest input
/// weight.
///
/// See also: <https://github.com/bitcoin/bitcoin/blob/62bd61de110b057cbfd6e31e4d0b727d93119c72/src/wallet/coinselection.cpp#L204>
///
/// There is discussion here: <https://murch.one/erhardt2016coinselection.pdf> at section 6.4.3
/// that prioritizing input weight will lead to a fragmentation of the UTXO set.  Therefore, prefer
/// this search only in extreme conditions where fee_rate is high, since a set of UTXOs with minimal
/// weight will lead to a cheaper constructed transaction in the short term.  However, in the
/// long-term, this prioritization can lead to more UTXOs to choose from.
///
/// # Parameters
///
/// * target: Target spend `Amount`
/// * cost_target: The minimum `Amount` that is budgeted for creating a change output
/// * max_selection_weight: The upper bound on the acceptable weight
/// * fee_rate: The fee_rate used to calculate the effective_value of each candidate Utxo
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from
///
/// # Returns
///
/// * `Some(Vec<WeightedUtxo>)` where `Vec<WeightedUtxo>` is some (non-empty) vector.
///    The search result succedded and a match was found.
/// * `None` un-expected results OR no match found.  A future implementation can add Error types
///   which will differentiate between an unexpected error and no match found.  Currently, a None
///   type occurs when one or more of the following criteria are met:
///     - Iteration limit hit
///     - Overflow when summing the UTXO space
///     - Not enough potential amount to meet the target, etc
///     - Target Amount is zero (no match possible)
///     - UTXO space was searched succefully however no match was found

// The sum of UTXO amounts after this UTXO index, e.g. lookahead[5] = Σ(UTXO[6+].amount)
fn build_lookahead<Utxo: WeightedUtxo>(lookahead: Vec<(Amount, &Utxo)>, available_value: Amount) -> Vec<Amount>{
    lookahead.iter().map(|(e, _w)| e).scan(available_value, |state, &u| {
        *state = *state - u;
        Some(*state)
    }).collect()
}

// Creates a tuple of (effective_value, weighted_utxo)
fn calc_effective_values<'a, Utxo: WeightedUtxo>(weighted_utxos: &'a [Utxo], fee_rate: FeeRate) -> Vec<(Amount, &'a Utxo)> {
    weighted_utxos
        .iter()
        // calculate effective_value and waste for each w_utxo.
        .map(|wu| (wu.effective_value(fee_rate), wu))
        // remove utxos that either had an error in the effective_value calculation.
        .filter(|(eff_val, _)| eff_val.is_some())
        // unwrap the option type since we know they are not None (see previous step).
        .map(|(eff_val, wu)| (eff_val.unwrap(), wu))
        // filter out all effective_values that are negative.
        .filter(|(eff_val, _)| eff_val.is_positive())
        // all utxo effective_values are now positive (see previous step) - cast to unsigned.
        .map(|(eff_val, wu)| (eff_val.to_unsigned().unwrap(), wu))
        .collect()
}

// The minimum UTXO weight among the remaining UTXOs after this UTXO index, e.g. min_tail_weight[5] = min(UTXO[6+].weight)
fn build_min_group_weight<'a, Utxo: WeightedUtxo>(weighted_utxos: Vec<(Amount, &Utxo)>) -> Vec<Weight> { 
    let mut min_group_weight: Vec<Weight> = vec![];
    let mut min = Weight::MAX;

    for (_, u) in &weighted_utxos {
        min_group_weight.push(min);
        let weight = u.satisfaction_weight();

        if weight < min {
            min = weight;
        }
    }

    min_group_weight.into_iter().rev().collect()
}

fn index_to_utxo_list<Utxo: WeightedUtxo>(
    index_list: Vec<usize>,
    wu: Vec<(Amount, &Utxo)>,
) -> Option<std::vec::IntoIter<&Utxo>> {
    let mut result: Vec<_> = Vec::new();
    let list = index_list;

    for i in list {
        let wu = wu[i].1;
        result.push(wu);
    }

    if result.is_empty() {
        None
    } else {
        Some(result.into_iter())
    }
}

pub fn select_coins<Utxo: WeightedUtxo>(
    target: Amount,
    change_target: Amount,
    max_selection_weight: Weight,
    fee_rate: FeeRate,
    weighted_utxos: &[Utxo],
) -> Option<std::vec::IntoIter<&Utxo>> {
    let mut w_utxos = calc_effective_values::<Utxo>(weighted_utxos, fee_rate.clone());
    let available_value = w_utxos.clone().into_iter().map(|(ev, _)| ev).checked_sum()?;

    // descending sort by effective_value using weight as tie breaker.
    w_utxos.sort_by(|a, b| { 
        b.0.cmp(&a.0)
            .then(b.1.satisfaction_weight().cmp(&a.1.satisfaction_weight()))
    });

    let lookahead = build_lookahead(w_utxos.clone(), available_value);

    //let min_group_weight = w_utxos.clone();
    let min_group_weight = build_min_group_weight(w_utxos.clone());

    let total_target = target + change_target;

    if available_value < total_target {
        return None
    }

    let mut selection: Vec<usize> = vec![];
    let mut best_selection: Vec<usize> = vec![];

    let mut amount_sum: Amount = Amount::ZERO;
    let mut best_amount_sum: Amount = Amount::MAX;

    let mut weight_sum: Weight = Weight::ZERO;
    let mut best_weight_sum: Weight = max_selection_weight;

    let _tx_weight_exceeded = false;

    let mut next_utxo_index = 0;

    loop {
        let mut cut = false;
        let mut shift = false;

        // EXPLORE
        let (eff_value, u) = w_utxos[next_utxo_index];

        amount_sum += eff_value;
        weight_sum += u.weight();
        selection.push(next_utxo_index);
        next_utxo_index += 1;

        let tail: usize = *selection.last().unwrap();

        // no possibility of hitting the total along this branch.
        // CUT
        if amount_sum + lookahead[tail] < total_target {
            cut = true;
        } else if weight_sum > best_weight_sum {
            // check if a better solution could exist.  IE there exists a utxo with a better
            // weight along the current branch
            if w_utxos[tail].1.weight() <= min_group_weight[tail] {
                // neither the inclusion branch nor the omission branch will
                // will find a better solution, therefore do not continue and
                // instead explore the penultimate selected UTXO.
                //
                // if this is a leaf node it's implied that no better solution
                // will be forthcoming.
                cut = true;
            } else {
                // explore the omission branch since adding a descendant may
                // improve the result.
                shift = true;
            }
        } else if amount_sum >= total_target {
            shift = true;
            if weight_sum < best_weight_sum || weight_sum == best_weight_sum && amount_sum < best_amount_sum {
                best_selection = selection.clone();
                best_weight_sum = weight_sum;
                best_amount_sum = amount_sum;
            }
        }

        // check if evaluating a leaf node.
        if next_utxo_index == w_utxos.len() {
            cut = true;
        }

        if cut {
            // deselect
            let (eff_value, u) = w_utxos[*selection.last().unwrap()];
            amount_sum -= eff_value;
            weight_sum -= u.weight();
            selection.pop();

            shift = true;
        }

        if shift {
            if selection.is_empty() {
                return index_to_utxo_list(best_selection, w_utxos)  
            }

            next_utxo_index = selection.last().unwrap() + 1;

            // deselect
            let (eff_value, u) = w_utxos[*selection.last().unwrap()];
            amount_sum -= eff_value;
            weight_sum -= u.weight();
            selection.pop();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;
    use crate::tests::{build_utxo, Utxo};
    use crate::coin_grinder::select_coins;

    #[derive(Debug)]
    pub struct ParamsStr<'a> {
        target: &'a str,
        change_target: &'a str,
        max_weight: &'a str,
        fee_rate: &'a str,
        weighted_utxos: Vec<&'a str>,
    }

    fn format_utxo_list(i: &[&Utxo]) -> Vec<String> {
        i.iter().map(|u| u.value().to_string()).collect()
    }

    fn build_utxos(weighted_utxos: Vec<&str>) -> Vec<Utxo>{
        weighted_utxos
            .iter()
            .map(|s| {
                let v: Vec<_> = s.split("/").collect();
                match v.len() {
                    3 => {
                        let a = Amount::from_str(v[0]).unwrap();
                        let w = Weight::from_wu(v[1].parse().unwrap());
                        let s = Weight::from_wu(v[2].parse().unwrap());
                        (a, w, s)
                    }
                    2 => {
                        let a = Amount::from_str(v[0]).unwrap();
                        let w = Weight::from_wu(v[1].parse().unwrap());
                        let s = w - Weight::from_wu(160);
                        (a, w, s)
                    }
                    1 => {
                        let a = Amount::from_str(v[0]).unwrap();
                        (a, Weight::ZERO, Weight::ZERO)
                    }
                    _ => panic!(),
                }
            })
            //.map(|(a, w)| build_utxo(a, w, w - Weight::from_wu(160)))
            .map(|(a, w, s)| build_utxo(a, w, s))
            .collect()
    }

    fn assert_coin_select_params(p: &ParamsStr, expected_inputs: Option<&[&str]>) {
        let fee_rate = p.fee_rate.parse::<u64>().unwrap(); // would be nice if  FeeRate had
                                                            //from_str like Amount::from_str()
        let target = Amount::from_str(p.target).unwrap();
        let change_target = Amount::from_str(p.change_target).unwrap();
        let fee_rate = FeeRate::from_sat_per_vb(fee_rate).unwrap();
        let max_weight = Weight::from_str(p.max_weight).unwrap();

        let w_utxos: Vec<_> = build_utxos(p.weighted_utxos.clone());

        let iter = select_coins(target, change_target, max_weight, fee_rate, &w_utxos);

        if expected_inputs.is_none() {
            assert!(iter.is_none());
        } else {
            let inputs: Vec<_> = iter.unwrap().collect();
            let expected_str_list: Vec<String> = expected_inputs
                .unwrap()
                .iter()
                .map(|s| Amount::from_str(s).unwrap().to_string())
                .collect();
            let input_str_list: Vec<String> = format_utxo_list(&inputs);
            assert_eq!(input_str_list, expected_str_list);
        }
    }

    #[test]
    fn min_group_weight() {
        let weighted_utxos = vec![
            "10 sats/8/8",
            "7 sats/4/4",
            "5 sats/4/4",
            "4 sats/8/8"
        ];

        let utxos: Vec<_> = build_utxos(weighted_utxos);
        let eff_values: Vec<(Amount, &Utxo)> = calc_effective_values(&utxos, FeeRate::ZERO);
        let min_group_weight = build_min_group_weight(eff_values.clone());

        let expect: Vec<Weight> = vec![
            4u64,
            4u64,
            8u64,
            18446744073709551615u64
        ].iter().map(|w| Weight::from_wu(*w)).collect();
        assert_eq!(min_group_weight, expect);
    }

    #[test]
    fn lookahead() {
        let weighted_utxos = vec![
            "10 sats/8/8",
            "7 sats/4/4",
            "5 sats/4/4",
            "4 sats/8/8"
        ];

        let utxos: Vec<_> = build_utxos(weighted_utxos);
        let eff_values: Vec<(Amount, &Utxo)> = calc_effective_values(&utxos, FeeRate::ZERO);
        let available_value = Amount::from_str("26 sats").unwrap();
        let lookahead = build_lookahead(eff_values, available_value);  

        let expect: Vec<Amount> = vec![
            "16 sats",
            "9 sats",
            "4 sats",
            "0 sats"
        ].iter().map(|s| Amount::from_str(s).unwrap()).collect();

        assert_eq!(lookahead, expect);
    }

    #[test]
    fn coin_grinder_example_solution() {
        let params = ParamsStr {
            target: "11 sats",
            change_target: "0",
            max_weight: "100",
            fee_rate: "0", //from sat per vb
            weighted_utxos: vec![
                "10 sats/8/8",
                "7 sats/4/4",
                "5 sats/4/4",
                "4 sats/8/8"
            ]
        };

        assert_coin_select_params(&params, Some(&["7 sats", "5 sats"]));
    }
}
