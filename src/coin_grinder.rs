// SPDX-License-Identifier: CC0-1.0
//
//! Coin Grinder.
//!
//! This module introduces the Coin Grinder selection algorithm.
//!
use bitcoin_units::{Amount, CheckedSum, Weight};

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

fn index_to_utxo_list<'a>(
    iteration: u32,
    index_list: Vec<usize>,
    iterations: u32,
    max_tx_weight_exceeded: bool,
    wu: Vec<&'a WeightedUtxo>,
) -> Return<'a> {
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
        Ok((iteration, result))
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
/// change output unlike the vanilla branch and bound algorithm. Therefore, in order to ensure that
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
/// * max_selection_weight: The maximum allowable selection weight
/// * fee_rate: The fee_rate used to calculate the effective_value of each candidate Utxo
/// * weighted_utxos: The candidate Weighted UTXOs from which to choose a selection from
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
        .checked_sum()
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
                iteration,
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
                    iteration,
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
mod tests {
    use std::str::FromStr;

    use arbitrary::Arbitrary;
    use arbtest::arbtest;
    use bitcoin_units::FeeRate;

    use super::*;
    use crate::tests::{assert_ref_eq, parse_fee_rate, Selection};

    #[derive(Debug)]
    pub struct TestCoinGrinder<'a> {
        target: &'a str,
        change_target: &'a str,
        max_weight: &'a str,
        fee_rate: &'a str,
        weighted_utxos: &'a [&'a str],
        expected_utxos: &'a [&'a str],
        expected_error: Option<crate::SelectionError>,
        expected_iterations: u32,
    }

    impl TestCoinGrinder<'_> {
        fn assert(&self) {
            let fee_rate = parse_fee_rate(self.fee_rate);
            let lt_fee_rate = FeeRate::ZERO;
            let target = Amount::from_str(self.target).unwrap();
            let change_target = Amount::from_str(self.change_target).unwrap();
            let max_weight = Weight::from_str(self.max_weight).unwrap();

            let candidate = Selection::new(self.weighted_utxos, fee_rate, lt_fee_rate);
            let result = coin_grinder(target, change_target, max_weight, &candidate.utxos);

            match result {
                Ok((iterations, inputs)) => {
                    assert_eq!(iterations, self.expected_iterations);
                    let candidate = Selection::new(self.expected_utxos, fee_rate, lt_fee_rate);
                    assert_ref_eq(inputs, candidate.utxos);
                }
                Err(e) => {
                    let expected_error = self.expected_error.clone().unwrap();
                    assert!(self.expected_utxos.is_empty());
                    assert_eq!(e, expected_error);
                }
            }
        }
    }

    #[test]
    fn min_tail_weight() {
        let weighted_utxos = &["29 sats/36 wu", "19 sats/40 wu", "11 sats/44 wu"];

        let candidate = Selection::new(weighted_utxos, FeeRate::ZERO, FeeRate::MAX);
        let min_tail_weight = build_min_tail_weight(candidate.utxos.iter().collect());

        let expect: Vec<Weight> =
            [40u64, 44u64, 18446744073709551615u64].iter().map(|w| Weight::from_wu(*w)).collect();
        assert_eq!(min_tail_weight, expect);
    }

    #[test]
    fn lookahead() {
        let weighted_utxos = vec!["10 sats/8 wu", "7 sats/4 wu", "5 sats/4 wu", "4 sats/8 wu"];

        let candidate = Selection::new(&weighted_utxos, FeeRate::ZERO, FeeRate::MAX);
        let available_value = Amount::from_str("26 sats").unwrap();
        let lookahead = build_lookahead(candidate.utxos.iter().collect(), available_value);

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
            expected_utxos: &["7 sats/4 wu", "5 sats/4 wu"],
            expected_error: None,
            expected_iterations: 8,
        }
        .assert();
    }

    #[test]
    fn insufficient_funds() {
        TestCoinGrinder {
            target: "49.5 BTC",
            change_target: "1000000 sats",
            max_weight: "10000",
            fee_rate: "0",
            weighted_utxos: &["1 BTC/272 wu", "2 BTC/272 wu"],
            expected_utxos: &[],
            expected_error: Some(InsufficentFunds),
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
            expected_utxos: &[],
            expected_error: Some(MaxWeightExceeded),
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
            expected.push("2 BTC/272 wu");
        }
        for _i in 0..17 {
            expected.push("0.33 BTC/272 wu");
        }

        TestCoinGrinder {
            target: "25.33 BTC",
            change_target: "1000000 sats",
            max_weight: "10000",
            fee_rate: "5 sat/vB",
            weighted_utxos: &wu[..],
            expected_utxos: &expected,
            expected_error: None,
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
            expected_utxos: &["1 BTC/272 wu", "1 BTC/272 wu"],
            expected_error: None,
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
            expected_utxos: &["14 BTC/1000 wu", "13 BTC/600 wu", "4 BTC/600 wu"],
            expected_error: None,
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
            expected_utxos: &["4 BTC/400 wu", "3 BTC/400 wu", "2 BTC/400 wu", "1 BTC/400 wu"],
            expected_error: None,
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
            expected_utxos: &["1 BTC/4000 wu", "1 BTC/4000 wu"],
            expected_error: Some(IterationLimitReached),
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
            expected_utxos: &[],
            expected_error: Some(Overflow(Addition)),
            expected_iterations: 8,
        }
        .assert();
    }

    #[test]
    fn max_target_and_max_change_target() {
        TestCoinGrinder {
            target: "2100000000000000 sats",        //Amount::MAX
            change_target: "2100000000000000 sats", //Amount::MAX
            max_weight: "100",
            fee_rate: "0",
            weighted_utxos: &["10 sats/8 wu", "7 sats/4 wu", "5 sats/4 wu", "4 sats/8 wu"],
            expected_utxos: &[],
            expected_error: Some(Overflow(Addition)),
            expected_iterations: 8,
        }
        .assert();
    }

    #[test]
    fn no_available_value() {
        TestCoinGrinder {
            target: "0",
            change_target: "0",
            max_weight: "0",
            fee_rate: "0",
            weighted_utxos: &[],
            expected_utxos: &[],
            expected_error: Some(SolutionNotFound),
            expected_iterations: 0,
        }
        .assert();
    }

    #[test]
    fn effective_value_tie() {
        // A secondary sort by weight will evaluate the lightest UTXOs first when effective_value
        // is a tie.
        TestCoinGrinder {
            target: "1500 sats",
            change_target: "100 sats",
            max_weight: "1000",
            fee_rate: "10 sat/kwu",
            weighted_utxos: &["e(1000 sats)/592 wu", "e(1000 sats)/272 wu", "e(1000 sats)/272 wu"],
            expected_utxos: &["e(1000 sats)/272 wu", "e(1000 sats)/272 wu"],
            expected_error: None,
            expected_iterations: 2,
        }
        .assert();
    }

    #[test]
    fn coin_grinder_proptest_lowest_weight_solution() {
        // This tests that coin-grinder will find the lowest weight solution.  To do so, create two
        // random UTXOs sets, one of which has weight greater than zero, the other with weights
        // equal to zero.  Then merge the two sets and assert coin-grinder finds the solution with
        // the zero weight UTXOs.
        arbtest(|u| {
            let exclusion_set = Selection::arbitrary(u)?;
            let inclusion_set = Selection::arbitrary(u)?;

            let mut weight_pool: Vec<_> = exclusion_set
                .utxos
                .iter()
                .filter_map(|utxo| {
                    let w = u.int_in_range::<u64>(1..=Weight::MAX.to_wu()).unwrap();
                    let wu = Weight::from_wu(w);
                    WeightedUtxo::new(
                        utxo.value,
                        wu,
                        exclusion_set.fee_rate,
                        exclusion_set.long_term_fee_rate,
                    )
                })
                .collect();

            let mut weightless_pool: Vec<_> = inclusion_set
                .utxos
                .iter()
                .map(|utxo| {
                    WeightedUtxo::new(
                        utxo.value,
                        Weight::ZERO,
                        inclusion_set.fee_rate,
                        inclusion_set.long_term_fee_rate,
                    )
                    .unwrap()
                })
                .filter(|utxo| utxo.value == Amount::ZERO)
                .collect();

            if let Some(target) = weightless_pool.iter().map(|utxo| utxo.value()).checked_sum() {
                if !weightless_pool.is_empty() {
                    weightless_pool.sort_by(|a, b| {
                        b.value().cmp(&a.value()).then(b.weight().cmp(&a.weight()))
                    });
                    weight_pool.append(&mut weightless_pool.clone());
                    if weight_pool.iter().map(|utxo| utxo.value()).checked_sum().is_some() {
                        let weight_sum = weight_pool
                            .iter()
                            .try_fold(Weight::ZERO, |acc, itm| acc.checked_add(itm.weight()));
                        if weight_sum.is_some() {
                            let change_target = Amount::ZERO;
                            let max_selection_weight = Weight::MAX;
                            let (count, utxos) = coin_grinder(
                                target,
                                change_target,
                                max_selection_weight,
                                &weight_pool,
                            )
                            .unwrap();
                            let utxos: Vec<_> = utxos.into_iter().cloned().collect();

                            assert_eq!(weightless_pool, utxos);
                            assert!(count > 0);
                        }
                    }
                }
            }

            Ok(())
        });
    }

    #[test]
    fn coin_grinder_proptest_any_solution() {
        arbtest(|u| {
            let candidate_selection = Selection::arbitrary(u)?;
            let target = Amount::arbitrary(u)?;
            let change_target = Amount::arbitrary(u)?;
            let max_weight = Weight::arbitrary(u)?;

            let result =
                coin_grinder(target, change_target, max_weight, &candidate_selection.utxos);

            match result {
                Ok((i, utxos)) => {
                    assert!(i > 0);
                    crate::tests::assert_target_selection(&utxos, target, None);
                }
                Err(Overflow(_)) => {
                    let available_value = candidate_selection.available_value();
                    let weight_total = candidate_selection.weight_total();
                    assert!(
                        available_value.is_none()
                            || weight_total.is_none()
                            || target.checked_add(change_target).is_none()
                    );
                }
                Err(InsufficentFunds) => {
                    let available_value = candidate_selection.available_value().unwrap();
                    assert!(available_value < (target + change_target).unwrap());
                }
                Err(IterationLimitReached) => {}
                Err(SolutionNotFound) => {
                    assert!(candidate_selection.utxos.is_empty() || target == Amount::ZERO)
                }
                Err(MaxWeightExceeded) => {
                    let weight_total = candidate_selection.weight_total().unwrap();
                    assert!(weight_total > max_weight);
                }
                Err(crate::SelectionError::ProgramError) => panic!("un-expected error"),
            }

            Ok(())
        });
    }
}
