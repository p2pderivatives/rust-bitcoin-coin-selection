//! # rust-bitcoin-coin-selection
//! Helper functions to select a set of UTXOs from a given UTXO pool to reach
//! a given target amount.
//!

#[cfg(any(test, feature = "rand"))]
use bitcoin::secp256k1::rand::{seq::SliceRandom, thread_rng};
use bitcoin::{OutPoint, TxOut};
use std::cmp::Reverse;

type Utxo = (TxOut, OutPoint);

/// Select coins first using BnB algorithm similar to what is done in bitcoin
/// core (see: https://github.com/bitcoin/bitcoin/blob/6b254814c076054eedc4311698d16c8971937814/src/wallet/coinselection.cpp#L21),
/// and falls back on a random UTXO selection. Returns none if the target cannot
/// be reached with the given utxo pool.
/// Requires compilation with the "rand" feature.
#[cfg(any(test, feature = "rand"))]
pub fn select_coins(target: u64, cost_of_change: u64, utxo_pool: &mut [Utxo]) -> Option<Vec<Utxo>> {
    match select_coins_bnb(target, cost_of_change, utxo_pool) {
        Some(res) => Some(res),
        None => select_coins_random(target, utxo_pool),
    }
}

/// Randomly select coins for the given target by shuffling the utxo pool and
/// taking UTXOs until the given target is reached, or returns None if the target
/// cannot be reached with the given utxo pool.
/// Requires compilation with the "rand" feature.
#[cfg(any(test, feature = "rand"))]
pub fn select_coins_random(target: u64, utxo_pool: &mut [Utxo]) -> Option<Vec<Utxo>> {
    utxo_pool.shuffle(&mut thread_rng());

    let mut sum = 0;

    let res = utxo_pool
        .iter()
        .take_while(|x| {
            sum += x.0.value;
            return if sum >= target { false } else { true };
        })
        .cloned()
        .collect();

    if sum >= target {
        return Some(res);
    }

    None
}

/// Select coins using BnB algorithm similar to what is done in bitcoin
/// core (see: https://github.com/bitcoin/bitcoin/blob/6b254814c076054eedc4311698d16c8971937814/src/wallet/coinselection.cpp#L21)
/// Returns None if BnB doesn't find a solution.
pub fn select_coins_bnb(
    target: u64,
    cost_of_change: u64,
    utxo_pool: &mut [Utxo],
) -> Option<Vec<Utxo>> {
    let solution = find_solution(target, cost_of_change, utxo_pool)?;
    Some(
        solution
            .into_iter()
            .zip(utxo_pool.iter())
            .filter_map(|(include, utxo)| if include { Some(utxo.clone()) } else { None })
            .collect::<Vec<Utxo>>(),
    )
}

pub fn find_solution(
    target: u64,
    cost_of_change: u64,
    utxo_pool: &mut [Utxo],
) -> Option<Vec<bool>> {
    let utxo_sum = utxo_pool.iter().fold(0u64, |mut s, u| {
        s += u.0.value;
        s
    });

    let utxo_pool_length = utxo_pool.len();
    utxo_pool.sort_by_key(|u| Reverse(u.0.value));

    let mut curr_selection: Vec<bool> = vec![false; utxo_pool_length];
    let mut best_selection = None;
    let mut remainder = utxo_sum;

    let lower_bound = target;
    let upper_bound = cost_of_change + lower_bound;

    if utxo_sum < lower_bound {
        return None;
    }

    for m in 0..utxo_pool_length {
        let mut curr_sum = 0;
        let mut slice_remainder = remainder;

        for n in m..utxo_pool_length {
            if slice_remainder + curr_sum < lower_bound {
                break;
            }

            let utxo_value = utxo_pool[n].0.value;
            curr_sum += utxo_value;
            curr_selection[n] = true;

            if curr_sum == lower_bound {
                return Some(curr_selection);
            }

            if curr_sum > lower_bound {
                if curr_sum < upper_bound {
                    best_selection = Some(curr_selection.clone());
                }

                curr_selection[n] = false;
                curr_sum -= utxo_value;
            }

            slice_remainder -= utxo_value;
        }

        remainder -= utxo_pool[m].0.value;
        curr_selection[m] = false;
    }

    best_selection
}

#[cfg(test)]
mod tests {
    use crate::*;
    use bitcoin::hashes::{sha256d, Hash};

    const ONE_BTC: u64 = 100000000;
    const TWO_BTC: u64 = 2 * 100000000;
    const THREE_BTC: u64 = 3 * 100000000;
    const FOUR_BTC: u64 = 4 * 100000000;

    const COST_OF_CHANGE: u64 = 50000000;

    fn build_utxo_vec() -> Vec<Utxo> {
        let amounts = vec![ONE_BTC, TWO_BTC, THREE_BTC, FOUR_BTC];

        let mut utxo_pool: Vec<Utxo> = Vec::new();

        for amount in &amounts {
            let seed: String = amount.to_string();
            let hash = sha256d::Hash::hash(seed.as_bytes());

            let utxo = (
                TxOut {
                    value: *amount,
                    script_pubkey: bitcoin::Script::new(),
                },
                OutPoint {
                    txid: bitcoin::Txid::from_hash(hash),
                    vout: 0,
                },
            );

            utxo_pool.push(utxo);
        }

        utxo_pool
    }

    #[test]
    fn find_solution_1_btc() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(ONE_BTC, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![false, false, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_2_btc() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(TWO_BTC, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![false, false, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_3_btc() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(THREE_BTC, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![false, true, false, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_4_btc() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(FOUR_BTC, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![true, false, false, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_5_btc() {
        let mut utxo_pool = build_utxo_vec();
        let five_btc = FOUR_BTC + ONE_BTC;
        let utxo_match = find_solution(five_btc, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![true, false, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_6_btc() {
        let mut utxo_pool = build_utxo_vec();
        let six_btc = FOUR_BTC + TWO_BTC;
        let utxo_match = find_solution(six_btc, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![true, false, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_7_btc() {
        let mut utxo_pool = build_utxo_vec();
        let seven_btc = FOUR_BTC + THREE_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![true, true, false, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_8_btc() {
        let mut utxo_pool = build_utxo_vec();
        let seven_btc = FOUR_BTC + THREE_BTC + ONE_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![true, true, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_9_btc() {
        let mut utxo_pool = build_utxo_vec();
        let seven_btc = FOUR_BTC + THREE_BTC + TWO_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![true, true, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_10_btc() {
        let mut utxo_pool = build_utxo_vec();
        let ten_btc = ONE_BTC + TWO_BTC + THREE_BTC + FOUR_BTC;
        let utxo_match = find_solution(ten_btc, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![true, true, true, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_11_btc_not_possible() {
        let mut utxo_pool = build_utxo_vec();
        let ten_btc = ONE_BTC + TWO_BTC + THREE_BTC + FOUR_BTC;
        let utxo_match = find_solution(ten_btc + ONE_BTC, COST_OF_CHANGE, &mut utxo_pool);
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn find_solution_with_large_cost_of_change() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(ONE_BTC * 9 / 10, COST_OF_CHANGE, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![false, false, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_with_no_cost_of_change() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(ONE_BTC * 9 / 10, 0, &mut utxo_pool);
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn find_solution_with_not_input_fee() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(ONE_BTC + 1, COST_OF_CHANGE, &mut utxo_pool);
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn select_coins_bnb_with_match() {
        let mut utxo_pool = build_utxo_vec();
        select_coins_bnb(ONE_BTC, COST_OF_CHANGE, &mut utxo_pool).unwrap();
    }

    #[test]
    fn select_coins_bnb_with_no_match() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = select_coins_bnb(1, COST_OF_CHANGE, &mut utxo_pool);
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn select_coins_random_draw_with_solution() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = select_coins_random(ONE_BTC, &mut utxo_pool);
        utxo_match.expect("Did not properly randomly select coins");
    }

    #[test]
    fn select_coins_random_draw_no_solution() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = select_coins_random(11 * ONE_BTC, &mut utxo_pool);
        assert!(utxo_match.is_none());
    }

    #[test]
    fn select_coins_bnb_match_with_random() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = select_coins(1, COST_OF_CHANGE, &mut utxo_pool);
        utxo_match.expect("Did not use random selection");
    }
}
