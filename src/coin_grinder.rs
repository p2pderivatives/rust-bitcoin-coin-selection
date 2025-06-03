// SPDX-License-Identifier: CC0-1.0
//
//! Coin Grinder.
//!
//! This module introduces the Coin Grinder selection algorithm.
//!
use bitcoin::amount::CheckedSum;
use bitcoin::{Amount, FeeRate, Weight};

use crate::WeightedUtxo;

const ITERATION_LIMIT: u32 = 100_000;

// The sum of UTXO amounts after this UTXO index, e.g. lookahead[5] = Σ(UTXO[6+].amount)
fn build_lookahead<Utxo: WeightedUtxo>(
    lookahead: Vec<(Amount, &Utxo)>,
    available_value: Amount,
) -> Vec<Amount> {
    lookahead
        .iter()
        .map(|(e, _w)| e)
        .scan(available_value, |state, &u| {
            *state -= u;
            Some(*state)
        })
        .collect()
}

// Creates a tuple of (effective_value, weighted_utxo)
fn calc_effective_values<Utxo: WeightedUtxo>(
    weighted_utxos: &[Utxo],
    fee_rate: FeeRate,
) -> Vec<(Amount, &Utxo)> {
    weighted_utxos
        .iter()
        // calculate effective_value for each w_utxo.
        .map(|wu| (wu.effective_value(fee_rate), wu))
        // remove utxos that had an error in the effective_value calculation.
        .filter(|(eff_val, _)| eff_val.is_some())
        // unwrap the option type since we know they are not None (see previous step).
        .map(|(eff_val, wu)| (eff_val.unwrap(), wu))
        // filter out all effective_values that are negative.
        .filter(|(eff_val, _)| eff_val.is_positive())
        // all utxo effective_values are now positive (see previous step) - cast to unsigned.
        .map(|(eff_val, wu)| (eff_val.to_unsigned().unwrap(), wu))
        .collect()
}

// Provides a lookup to determine the minimum UTXO weight after a given index.
fn build_min_tail_weight<Utxo: WeightedUtxo>(weighted_utxos: Vec<(Amount, &Utxo)>) -> Vec<Weight> {
    let weights: Vec<_> = weighted_utxos.into_iter().map(|(_, u)| u.weight()).rev().collect();
    let mut prev = Weight::MAX;
    let mut result = Vec::new();
    for w in weights {
        result.push(prev);
        prev = std::cmp::min(prev, w);
    }
    result.into_iter().rev().collect()
}

fn index_to_utxo_list<Utxo: WeightedUtxo>(
    iteration: u32,
    index_list: Vec<usize>,
    wu: Vec<(Amount, &Utxo)>,
) -> Option<(u32, std::vec::IntoIter<&Utxo>)> {
    let mut result: Vec<_> = Vec::new();
    let list = index_list;

    for i in list {
        let wu = wu[i].1;
        result.push(wu);
    }

    if result.is_empty() {
        None
    } else {
        Some((iteration, result.into_iter()))
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
    // TODO use checked div rounding up
    let utxo_count = (remaining_amount.to_sat() + tail_amount.to_sat() - 1) / tail_amount.to_sat();

    // sum of input weights if all inputs are the best possible weight.
    let remaining_weight = min_tail_weight * utxo_count;

    // add remaining_weight to the current running weight total.
    let best_possible_weight = weight_total + remaining_weight;

    Some(best_possible_weight > best_weight)
}

/// Performs a Branch Bound search that prioritizes input weight.  That is, select the set of
/// outputs that meets the `total_target` and has the lowest total weight.  This algorithm produces a
/// change output unlike [`select_coins_bnb`]. Therefore, in order to ensure that
/// the change output can be paid for, the `total_target` is calculated as target plus
/// `change_target` where `change_target` is the budgeted amount that pays for the change output.
/// The `change_target` is the budgeted amount to pay for the change output.
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
/// * change_target: The minimum `Amount` that is budgeted for creating a change output
/// * max_selection_weight: The upper bound on the acceptable weight
/// * fee_rate: The fee_rate used to calculate the effective_value of each candidate Utxo
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from
///
/// # Returns
///
/// * `Some(Vec<WeightedUtxo>)` where `Vec<WeightedUtxo>` is some (non-empty) vector.
///   The search result succeeded and a match was found.
/// * `None` un-expected results OR no match found.  A future implementation can add Error types
///   which will differentiate between an unexpected error and no match found.  Currently, a None
///   type occurs when one or more of the following criteria are met:
///     - Iteration limit hit
///     - Overflow when summing the UTXO pool
///     - Not enough potential amount to meet the target
///     - Target Amount is zero (no match possible)
///     - UTXO pool was searched successfully however no match was found
pub fn select_coins<Utxo: WeightedUtxo>(
    target: Amount,
    change_target: Amount,
    max_selection_weight: Weight,
    fee_rate: FeeRate,
    weighted_utxos: &[Utxo],
) -> Option<(u32, std::vec::IntoIter<&Utxo>)> {
    // TODO replaced with checked_sum() on next rust-bitcoin release.
    weighted_utxos.iter().map(|u| u.weight()).try_fold(Weight::ZERO, Weight::checked_add)?;

    let mut w_utxos = calc_effective_values::<Utxo>(weighted_utxos, fee_rate);

    let available_value = w_utxos.clone().into_iter().map(|(ev, _)| ev).checked_sum()?;

    // descending sort by effective_value using satisfaction weight as tie breaker.
    w_utxos.sort_by(|a, b| b.0.cmp(&a.0).then(b.1.weight().cmp(&a.1.weight())));

    let lookahead = build_lookahead(w_utxos.clone(), available_value);
    let min_tail_weight = build_min_tail_weight(w_utxos.clone());

    let total_target = target.checked_add(change_target)?;

    if available_value < total_target || available_value == Amount::ZERO {
        return None;
    }

    let mut selection: Vec<usize> = vec![];
    let mut best_selection: Vec<usize> = vec![];

    let mut amount_total: Amount = Amount::ZERO;
    let mut best_amount: Amount = Amount::MAX;

    let mut weight_total: Weight = Weight::ZERO;
    let mut best_weight: Weight = max_selection_weight;

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

        let (eff_value, u) = w_utxos[next_utxo_index];

        amount_total += eff_value;
        weight_total += u.weight();

        selection.push(next_utxo_index);
        next_utxo_index += 1;
        iteration += 1;

        let tail: usize = *selection.last().unwrap();
        if amount_total + lookahead[tail] < total_target {
            cut = true;
        } else if weight_total > best_weight {
            if w_utxos[tail].1.weight() <= min_tail_weight[tail] {
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
                w_utxos[tail].0,
                best_weight,
            ) {
                if is_higher {
                    if w_utxos[tail].1.weight() <= min_tail_weight[tail] {
                        cut = true;
                    } else {
                        shift = true;
                    }
                }
            }
        }

        if iteration >= ITERATION_LIMIT {
            return index_to_utxo_list(iteration, best_selection, w_utxos);
        }

        // check if evaluating a leaf node.
        if next_utxo_index == w_utxos.len() {
            cut = true;
        }

        if cut {
            // deselect
            let (eff_value, u) = w_utxos[*selection.last().unwrap()];
            amount_total -= eff_value;
            weight_total -= u.weight();
            selection.pop();
            shift = true;
        }

        while shift {
            if selection.is_empty() {
                return index_to_utxo_list(iteration, best_selection, w_utxos);
            }

            next_utxo_index = selection.last().unwrap() + 1;

            // deselect
            let (eff_value, u) = w_utxos[*selection.last().unwrap()];
            amount_total -= eff_value;
            weight_total -= u.weight();
            selection.pop();

            shift = false;

            // skip all next inputs that are equivalent to the current input
            // if the current input didn't contribute to a solution.
            while w_utxos[next_utxo_index - 1].0 == w_utxos[next_utxo_index].0 {
                if next_utxo_index >= w_utxos.len() - 1 {
                    shift = true;
                    break;
                }
                next_utxo_index += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;
    use crate::coin_grinder::select_coins;
    use crate::tests::{parse_fee_rate, Utxo, UtxoPool};

    #[derive(Debug)]
    pub struct TestCoinGrinder<'a> {
        target: &'a str,
        change_target: &'a str,
        max_weight: &'a str,
        fee_rate: &'a str,
        weighted_utxos: &'a [&'a str],
        expected_utxos: Option<&'a [&'a str]>,
        expected_iterations: u32,
    }

    fn format_utxo_list(i: &[&Utxo]) -> Vec<String> {
        i.iter().map(|u| u.value().to_string()).collect()
    }

    impl TestCoinGrinder<'_> {
        fn assert(&self) {
            let fee_rate = parse_fee_rate(self.fee_rate);
            let target = Amount::from_str(self.target).unwrap();
            let change_target = Amount::from_str(self.change_target).unwrap();
            let max_weight = Weight::from_str(self.max_weight).unwrap();

            let pool: UtxoPool = UtxoPool::new(self.weighted_utxos, fee_rate);

            let result = select_coins(target, change_target, max_weight, fee_rate, &pool.utxos);

            if self.expected_utxos.is_none() {
                assert!(result.is_none());
            } else {
                let (iteration_count, iter) = result.unwrap();
                assert_eq!(iteration_count, self.expected_iterations);
                let inputs: Vec<_> = iter.collect();
                let expected_str_list: Vec<String> = self
                    .expected_utxos
                    .unwrap()
                    .iter()
                    .map(|s| Amount::from_str(s).unwrap().to_string())
                    .collect();
                let input_str_list: Vec<String> = format_utxo_list(&inputs);
                assert_eq!(input_str_list, expected_str_list);
            }
        }
    }

    #[test]
    fn min_tail_weight() {
        let weighted_utxos = &["29 sats/36 wu", "19 sats/40 wu", "11 sats/44 wu"];

        let pool: UtxoPool = UtxoPool::new(weighted_utxos, FeeRate::ZERO);
        let eff_values: Vec<(Amount, &Utxo)> = calc_effective_values(&pool.utxos, FeeRate::ZERO);
        let min_tail_weight = build_min_tail_weight(eff_values.clone());

        let expect: Vec<Weight> =
            [40u64, 44u64, 18446744073709551615u64].iter().map(|w| Weight::from_wu(*w)).collect();
        assert_eq!(min_tail_weight, expect);
    }

    #[test]
    fn lookahead() {
        let weighted_utxos = vec!["10 sats/8 wu", "7 sats/4 wu", "5 sats/4 wu", "4 sats/8 wu"];

        let pool: UtxoPool = UtxoPool::new(&weighted_utxos, FeeRate::ZERO);
        let eff_values: Vec<(Amount, &Utxo)> = calc_effective_values(&pool.utxos, FeeRate::ZERO);
        let available_value = Amount::from_str("26 sats").unwrap();
        let lookahead = build_lookahead(eff_values, available_value);

        let expect: Vec<Amount> = ["16 sats", "9 sats", "4 sats", "0 sats"]
            .iter()
            .map(|s| Amount::from_str(s).unwrap())
            .collect();

        assert_eq!(lookahead, expect);
    }

    #[test]
    fn example_solution() {
        TestCoinGrinder {
            target: "11 sats",
            change_target: "0",
            max_weight: "100",
            fee_rate: "0",
            weighted_utxos: &["10 sats/8 wu", "7 sats/4 wu", "5 sats/4 wu", "4 sats/8 wu"],
            expected_utxos: Some(&["7 sats", "5 sats"]),
            expected_iterations: 8,
        }
        .assert();
    }

    #[test]
    fn insufficient_funds() {
        // 1) Insufficient funds, select all provided coins and fail
        // https://github.com/bitcoin/bitcoin/blob/43e71f74988b2ad87e4bfc0e1b5c921ab86ec176/src/wallet/test/coinselector_tests.cpp#L1135
        TestCoinGrinder {
            target: "49.5 BTC",
            change_target: "1000000 sats",
            max_weight: "10000",
            fee_rate: "0",
            weighted_utxos: &["1 BTC/0", "2 BTC/0"],
            expected_utxos: None,
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn max_weight_exceeded() {
        // 2) Test max weight exceeded
        // https://github.com/bitcoin/bitcoin/blob/43e71f74988b2ad87e4bfc0e1b5c921ab86ec176/src/wallet/test/coinselector_tests.cpp#L1153
        let mut wu = Vec::new();
        for _i in 0..10 {
            wu.push("1 BTC/272 wu");
            wu.push("2 BTC/272 wu");
        }

        TestCoinGrinder {
            target: "29.5 BTC",
            change_target: "1000000 sats",
            max_weight: "3000",
            fee_rate: "5 sat/vB",
            weighted_utxos: &wu[..],
            expected_utxos: None,
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn max_weight_with_result() {
        // 3) Test that the lowest-weight solution is found when some combinations would exceed the allowed weight
        // https://github.com/bitcoin/bitcoin/blob/43e71f74988b2ad87e4bfc0e1b5c921ab86ec176/src/wallet/test/coinselector_tests.cpp#L1171
        let mut wu = Vec::new();
        let mut expected = Vec::new();

        for _i in 0..60 {
            wu.push("0.33 BTC/272 wu");
        }
        for _i in 0..10 {
            wu.push("2 BTC/272 wu");
        }

        for _i in 0..10 {
            expected.push("2 BTC");
        }
        for _i in 0..17 {
            expected.push("0.33 BTC");
        }

        TestCoinGrinder {
            target: "25.33 BTC",
            change_target: "1000000 sats",
            max_weight: "10000",
            fee_rate: "5 sat/vB",
            weighted_utxos: &wu[..],
            expected_utxos: Some(&expected),
            expected_iterations: 37,
        }
        .assert();
    }

    #[test]
    fn select_lighter_utxos() {
        // 4) Test that two less valuable UTXOs with a combined lower weight are preferred over a more valuable heavier UTXO
        // https://github.com/bitcoin/bitcoin/blob/43e71f74988b2ad87e4bfc0e1b5c921ab86ec176/src/wallet/test/coinselector_tests.cpp#L1193
        TestCoinGrinder {
            target: "1.9 BTC",
            change_target: "1000000 sats",
            max_weight: "400000",
            fee_rate: "5 sat/vB",
            weighted_utxos: &["2 BTC/592 wu", "1 BTC/272 wu", "1 BTC/272 wu"],
            expected_utxos: Some(&["1 BTC", "1 BTC"]),
            expected_iterations: 3,
        }
        .assert();
    }

    #[test]
    fn select_best_weight() {
        // 5) Test finding a solution in a UTXO pool with mixed weights
        // https://github.com/bitcoin/bitcoin/blob/43e71f74988b2ad87e4bfc0e1b5c921ab86ec176/src/wallet/test/coinselector_tests.cpp#L1215
        let wu = &[
            "1 BTC/600 wu",
            "2 BTC/1000 wu",
            "3 BTC/1400 wu",
            "4 BTC/600 wu",
            "5 BTC/1000 wu",
            "6 BTC/1400 wu",
            "7 BTC/600 wu",
            "8 BTC/1000 wu",
            "9 BTC/1400 wu",
            "10 BTC/600 wu",
            "11 BTC/1000 wu",
            "12 BTC/1400 wu",
            "13 BTC/600 wu",
            "14 BTC/1000 wu",
            "15 BTC/1400 wu",
        ];

        TestCoinGrinder {
            target: "30 BTC",
            change_target: "1000000 sats",
            max_weight: "400000",
            fee_rate: "5 sat/vB",
            weighted_utxos: wu,
            expected_utxos: Some(&["14 BTC", "13 BTC", "4 BTC"]),
            expected_iterations: 92,
        }
        .assert();
    }

    #[test]
    fn lightest_among_many_clones() {
        // 6) Test that the lightest solution among many clones is found
        // https://github.com/bitcoin/bitcoin/blob/43e71f74988b2ad87e4bfc0e1b5c921ab86ec176/src/wallet/test/coinselector_tests.cpp#L1244
        let mut wu = vec!["4 BTC/400 wu", "3 BTC/400 wu", "2 BTC/400 wu", "1 BTC/400 wu"];

        for _i in 0..100 {
            wu.push("8 BTC/4000 wu");
            wu.push("7 BTC/3200 wu");
            wu.push("6 BTC/2400 wu");
            wu.push("5 BTC/1600 wu");
        }

        TestCoinGrinder {
            target: "989999999 sats",
            change_target: "1000000 sats",
            max_weight: "400000",
            fee_rate: "5 sat/vB",
            weighted_utxos: &wu[..],
            expected_utxos: Some(&["4 BTC", "3 BTC", "2 BTC", "1 BTC"]),
            expected_iterations: 38,
        }
        .assert();
    }

    #[test]
    fn skip_tiny_inputs() {
        // 7) Test that lots of tiny UTXOs can be skipped if they are too heavy while there are enough funds in lookahead
        // https://github.com/bitcoin/bitcoin/blob/43e71f74988b2ad87e4bfc0e1b5c921ab86ec176/src/wallet/test/coinselector_tests.cpp#L1153
        let mut wu = vec!["1.8 BTC/10000 wu", "1 BTC/4000 wu", "1 BTC/4000 wu"];
        let mut tiny = vec![];
        for i in 0..100 {
            tiny.push(0.01 * 100000000_f64 + i as f64);
        }
        let tiny: Vec<String> = tiny.iter().map(|a| format!("{} sats/440 wu", a)).collect();
        let mut tiny: Vec<&str> = tiny.iter().map(|s| s as &str).collect();
        wu.append(&mut tiny);

        TestCoinGrinder {
            target: "1.9 BTC",
            change_target: "1000000 sats",
            max_weight: "400000",
            fee_rate: "5 sat/vB",
            weighted_utxos: &wu[..],
            expected_utxos: Some(&["1 BTC", "1 BTC"]),
            expected_iterations: 7,
        }
        .assert();
    }

    #[test]
    fn coins_with_max_weight_does_not_overflow() {
        TestCoinGrinder {
            target: "11 sats",
            change_target: "0",
            max_weight: "100",
            fee_rate: "0",
            weighted_utxos: &[
                "10 sats/18446744073709551615 wu", //u64::MAX
                "7 sats/4 wu",
                "5 sats/4 wu",
                "4 sats/18446744073709551615 wu", //u64::MAX
            ],
            expected_utxos: None,
            expected_iterations: 8,
        }
        .assert();
    }

    #[test]
    fn max_target_and_max_change_target() {
        TestCoinGrinder {
            target: "18446744073709551615 sats",        //u64::MAX
            change_target: "18446744073709551615 sats", //u64::MAX
            max_weight: "100",
            fee_rate: "0",
            weighted_utxos: &["10 sats/8 wu", "7 sats/4 wu", "5 sats/4 wu", "4 sats/8 wu"],
            expected_utxos: None,
            expected_iterations: 8,
        }
        .assert();
    }

    #[test]
    fn no_availalbe_value() {
        TestCoinGrinder {
            target: "0",        //u64::MAX
            change_target: "0", //u64::MAX
            max_weight: "0",
            fee_rate: "0",
            weighted_utxos: &[],
            expected_utxos: None,
            expected_iterations: 0,
        }
        .assert();
    }
}
