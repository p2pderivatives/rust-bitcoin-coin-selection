// SPDX-License-Identifier: CC0-1.0
//
//! Single Random Draw Algorithem.
//!
//! This module introduces the Single Random Draw Coin-Selection Algorithm.

use bitcoin::blockdata::transaction::effective_value;
use bitcoin::{Amount, FeeRate};
use rand::seq::SliceRandom;

use crate::{WeightedUtxo, CHANGE_LOWER};

/// Randomly select coins for the given target by shuffling the UTXO pool and
/// taking UTXOs until the given target is reached.
///
/// The fee_rate can have an impact on the selection process since the fee
/// must be paid for in addition to the target.  However, the total fee
/// is dependant on the number of UTXOs consumed and the new inputs created.
/// The selection strategy therefore calculates the fees of what is known
/// ahead of time (the number of UTXOs create and the transaction header),
/// and then then for each new input, the effective_value is tracked which
/// deducts the fee for each individual input at selection time.  For more
/// discussion see the following:
///
/// <https://bitcoin.stackexchange.com/questions/103654/calculating-fee-based-on-fee-rate-for-bitcoin-transaction/114847#114847>
///
/// # Parameters
///
/// * `target` - target value to send to recipient.  Include the fee to pay for
///    the known parts of the transaction excluding the fee for the inputs.
/// * `fee_rate` - ratio of transaction amount per size.
/// * `weighted_utxos` - Weighted UTXOs from which to sum the target amount.
/// * `rng` - used primarily by tests to make the selection deterministic.
///
/// # Returns
///
/// * `Some(Vec<WeightedUtxo>)` where `Vec<WeightedUtxo>` is empty on no matches found.  An empty
///   vec signifies that all possibilities where explored successfully and no match could be
///   found with the given parameters.
/// * `None` un-expected results during search.  A future implementation can replace all `None`
///   returns with a more informative error.  Example of error: iteration limit hit, overflow
///   when summing the UTXO space, Not enough potential amount to meet the target, etc.
pub fn select_coins_srd<'a, R: rand::Rng + ?Sized, Utxo: WeightedUtxo>(
    target: Amount,
    fee_rate: FeeRate,
    weighted_utxos: &'a [Utxo],
    rng: &mut R,
) -> Option<std::vec::IntoIter<&'a Utxo>> {
    if target > Amount::MAX_MONEY {
        return None;
    }

    let mut result: Vec<_> = weighted_utxos.iter().collect();
    let mut origin = result.to_owned();
    origin.shuffle(rng);

    result.clear();

    let threshold = target.checked_add(CHANGE_LOWER)?;

    let mut value = Amount::ZERO;

    for w_utxo in origin {
        let utxo_value = w_utxo.value();
        let utxo_weight = w_utxo.satisfaction_weight();
        let effective_value = effective_value(fee_rate, utxo_weight, utxo_value);

        if let Some(e) = effective_value {
            if let Ok(v) = e.to_unsigned() {
                value += v;

                result.push(w_utxo);

                if value >= threshold {
                    return Some(result.into_iter());
                }
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use core::str::FromStr;

    use bitcoin::{Amount, Weight};
    use rand::rngs::mock::StepRng;

    use super::*;
    use crate::single_random_draw::select_coins_srd;
    use crate::tests::{build_utxo, Utxo};
    use crate::WeightedUtxo;

    const FEE_RATE: FeeRate = FeeRate::from_sat_per_kwu(10);
    const SATISFACTION_WEIGHT: Weight = Weight::from_wu(204);

    #[derive(Debug)]
    pub struct ParamsStr<'a> {
        target: &'a str,
        fee_rate: &'a str,
        weighted_utxos: Vec<&'a str>,
    }

    fn build_pool() -> Vec<Utxo> {
        let amts = vec![Amount::from_str("1 cBTC").unwrap(), Amount::from_str("2 cBTC").unwrap()];

        let mut pool = vec![];

        for a in amts {
            let utxo = build_utxo(a, Weight::ZERO, SATISFACTION_WEIGHT);
            pool.push(utxo);
        }

        pool
    }

    fn get_rng() -> StepRng {
        // [1, 2]
        // let mut vec: Vec<u32> = (1..3).collect();
        // let mut rng = StepRng::new(0, 0);
        //
        // [2, 1]
        // vec.shuffle(&mut rng);

        // shuffle() will always result in the order described above when a constant
        // is used as the rng.  The first is removed from the beginning and added to
        // the end while the remaining elements keep their order.
        StepRng::new(0, 0)
    }

    fn format_utxo_list(i: &[&Utxo]) -> Vec<String> {
        i.iter().map(|u| u.value().to_string()).collect()
    }

    fn format_expected_str_list(e: &[&str]) -> Vec<String> {
        e.iter().map(|s| Amount::from_str(s).unwrap().to_string()).collect()
    }

    fn assert_coin_select_params(p: &ParamsStr, expected_inputs: Option<&[&str]>) {
        let fee_rate = p.fee_rate.parse::<u64>().unwrap(); // would be nice if  FeeRate had
                                                           // from_str like Amount::from_str()
        let target = Amount::from_str(p.target).unwrap();
        let fee_rate = FeeRate::from_sat_per_kwu(fee_rate);

        let w_utxos: Vec<_> = p
            .weighted_utxos
            .iter()
            .map(|s| {
                let v: Vec<_> = s.split("/").collect();
                match v.len() {
                    2 => {
                        let a = Amount::from_str(v[0]).unwrap();
                        let w = Weight::from_wu(v[1].parse().unwrap());
                        (a, w)
                    }
                    1 => {
                        println!("{}", v[0]);
                        let a = Amount::from_str(v[0]).unwrap();
                        (a, Weight::ZERO)
                    }
                    _ => panic!(),
                }
            })
            .map(|(a, w)| build_utxo(a, Weight::ZERO, w))
            .collect();

        let result = select_coins_srd(target, fee_rate, &w_utxos, &mut get_rng());

        if expected_inputs.is_none() {
            assert!(result.is_none());
        } else {
            let inputs: Vec<_> = result.unwrap().collect();
            let expected_str_list: Vec<String> = expected_inputs
                .unwrap()
                .iter()
                .map(|s| Amount::from_str(s).unwrap().to_string())
                .collect();
            let input_str_list: Vec<String> = format_utxo_list(&inputs);
            assert_eq!(input_str_list, expected_str_list);
        }
    }

    fn assert_coin_select(target_str: &str, expected_inputs: &[&str]) {
        let target = Amount::from_str(target_str).unwrap();
        let pool = build_pool();

        let inputs: Vec<&Utxo> = select_coins_srd(target, FEE_RATE, &pool, &mut get_rng())
            .expect("unexpected error")
            .collect();

        let input_str_list: Vec<_> = format_utxo_list(&inputs);
        let expected_str_list: Vec<_> = format_expected_str_list(expected_inputs);
        assert_eq!(input_str_list, expected_str_list);
    }

    #[test]
    fn select_coins_srd_with_solution() { assert_coin_select("1.5 cBTC", &["2 cBTC"]); }

    #[test]
    fn select_coins_srd_all_solution() { assert_coin_select("2.5 cBTC", &["2 cBTC", "1 cBTC"]); }

    #[test]
    fn select_coins_srd_no_solution() {
        let params =
            ParamsStr { target: "4 cBTC", fee_rate: "0", weighted_utxos: vec!["1 cBTC", "2 cBTC"] };

        assert_coin_select_params(&params, None);
    }

    #[test]
    fn select_coins_skip_negative_effective_value() {
        let params = ParamsStr {
            target: "1.95 cBTC", // 2 cBTC - CHANGE_LOWER
            fee_rate: "10",
            weighted_utxos: vec!["1 cBTC", "2 cBTC", "1 sat/204"], // 1 sat @ 204 wu has negative effective_value
        };

        assert_coin_select_params(&params, Some(&["2 cBTC", "1 cBTC"]));
    }

    #[test]
    fn select_coins_srd_fee_rate_error() {
        let params = ParamsStr {
            target: "1 cBTC",
            fee_rate: "18446744073709551615",
            weighted_utxos: vec!["1 cBTC", "2 cBTC"],
        };

        assert_coin_select_params(&params, None);
    }

    #[test]
    fn select_coins_srd_change_output_too_small() {
        let params = ParamsStr {
            target: "3 cBTC",
            fee_rate: "10",
            weighted_utxos: vec!["1 cBTC", "2 cBTC"],
        };

        assert_coin_select_params(&params, None);
    }

    #[test]
    fn select_coins_srd_with_high_fee() {
        let params = ParamsStr {
            target: "1.99999 cBTC",
            fee_rate: "10",
            weighted_utxos: vec!["1 cBTC", "2 cBTC"],
        };

        assert_coin_select_params(&params, Some(&["2 cBTC", "1 cBTC"]));
    }

    #[test]
    fn select_coins_srd_addition_overflow() {
        let params = ParamsStr {
            target: "2 cBTC",
            fee_rate: "10",
            weighted_utxos: vec!["1 cBTC/18446744073709551615"], // weight= u64::MAX
        };

        assert_coin_select_params(&params, None);
    }

    #[test]
    fn select_coins_srd_threshold_overflow() {
        let params = ParamsStr {
            target: "2100000000000000 sats", // Amount::MAX
            fee_rate: "10",
            weighted_utxos: vec!["1 cBTC/18446744073709551615"],
        };

        assert_coin_select_params(&params, None);
    }
}
