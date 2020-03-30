use std::cmp::Reverse;
use serde::{Deserialize, Serialize};
use bitcoin::hashes::sha256d::Hash as Sha256dHash;

#[derive(Serialize, Deserialize, Debug, Hash, Clone)]
pub struct TransactionStatus {
    pub confirmed: bool,
    pub block_height: Option<usize>,
    pub block_hash: Option<Sha256dHash>,
    pub block_time: Option<u32>,
}

#[derive(Serialize, Deserialize, Debug, Hash, Clone)]
pub struct UtxoValue {
    pub txid: Sha256dHash,
    pub vout: u32,
    pub status: TransactionStatus,
    pub value: u64,
}

impl Eq for UtxoValue {}

impl PartialEq for UtxoValue {
    fn eq(&self, other: &Self) -> bool {
        self.txid == other.txid
    }
}

pub fn select_coins_bnb(target: u64,
                        cost_of_change: u64, 
                        not_input_fees: u64, 
                        utxo_pool: &mut Vec<UtxoValue>) 
                        -> Option<Vec<UtxoValue>> {
    let solution = find_solution(target, cost_of_change, not_input_fees, utxo_pool);
    match solution {
        Some(s) => { let result = s
            .iter()
            .zip(utxo_pool.iter())
            .filter( |(include, _)| **include )
            .fold(Vec::new(), |mut r, (_, u)| { r.push((*u).clone()); r});
            let solution_sum =
                result.iter().fold(0u64, |mut s, u| { s += u.value; s });
            assert!(solution_sum == target);
            return Some(result);
        },
        None => None,
    }
}

pub fn find_solution(target: u64, 
                     cost_of_change: u64,
                     not_input_fees: u64,
                     utxo_pool: &mut Vec<UtxoValue>)
                     -> Option<Vec<bool>> {
    let utxo_sum = utxo_pool.iter().fold(0u64, |mut s, u| { s += u.value; s});

    let utxo_pool_length = utxo_pool.len();
    utxo_pool.sort_by_key(|u| Reverse(u.value));

    let mut curr_selection: Vec<bool> = vec![false; utxo_pool_length];
    let mut best_selection = None;
    let mut remainder = utxo_sum;

    let lower_bound = target + not_input_fees;
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

            let utxo_value = utxo_pool[n].value;
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

        remainder -= utxo_pool[m].value;
        curr_selection[m] = false;
    }

    best_selection
}

#[cfg(test)]
mod tests {
    use bitcoin::hashes::{sha256d, Hash};
    use crate::*;

    const ONE_BTC: u64 = 100000000;
    const TWO_BTC: u64 = 2 * 100000000;
    const THREE_BTC: u64 = 3 * 100000000;
    const FOUR_BTC: u64 = 4 * 100000000;

    const COST_OF_CHANGE: u64 = 50000000;

    fn build_utxo_vec() -> Vec<UtxoValue> {
        let amounts = vec![ONE_BTC, TWO_BTC, THREE_BTC, FOUR_BTC];

        let mut utxo_pool: Vec<UtxoValue> = Vec::new();

        for amount in &amounts {
            let seed: String = amount.to_string();
            let hash = sha256d::Hash::hash(seed.as_bytes());

            let transaction_status = TransactionStatus {
                confirmed: true,
                block_height: None,
                block_hash: None,
                block_time: None,
            };

            let utxo = UtxoValue {
                status: transaction_status,
                txid: hash,
                value: *amount,
                vout: 0,
            };

            utxo_pool.push(utxo);
        };

       utxo_pool 
    }

    #[test]
    fn find_solution_1_btc() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(ONE_BTC, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![false, false, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_2_btc() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(TWO_BTC, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![false, false, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_3_btc() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(THREE_BTC, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![false, true, false, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_4_btc() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(FOUR_BTC, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![true, false, false, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_5_btc() {
        let mut utxo_pool = build_utxo_vec();
        let five_btc = FOUR_BTC + ONE_BTC;
        let utxo_match = find_solution(five_btc, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![true, false, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_6_btc() {
        let mut utxo_pool = build_utxo_vec();
        let six_btc = FOUR_BTC + TWO_BTC;
        let utxo_match = find_solution(six_btc, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![true, false, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_7_btc() {
        let mut utxo_pool = build_utxo_vec();
        let seven_btc = FOUR_BTC + THREE_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![true, true, false, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_8_btc() {
        let mut utxo_pool = build_utxo_vec();
        let seven_btc = FOUR_BTC + THREE_BTC + ONE_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![true, true, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_9_btc() {
        let mut utxo_pool = build_utxo_vec();
        let seven_btc = FOUR_BTC + THREE_BTC + TWO_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![true, true, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_10_btc() {
        let mut utxo_pool = build_utxo_vec();
        let ten_btc = ONE_BTC + TWO_BTC + THREE_BTC + FOUR_BTC;
        let utxo_match = find_solution(
            ten_btc, COST_OF_CHANGE, 0, &mut utxo_pool).unwrap();
        let expected_bool_vec = vec![true, true, true, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_11_btc_not_possible() {
        let mut utxo_pool = build_utxo_vec();
        let ten_btc = ONE_BTC + TWO_BTC + THREE_BTC + FOUR_BTC;
        let utxo_match = find_solution(
            ten_btc + ONE_BTC, COST_OF_CHANGE, 0, &mut utxo_pool);
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn find_solution_with_large_cost_of_change() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(ONE_BTC * 9/10, COST_OF_CHANGE, 0, &mut utxo_pool)
            .unwrap();
        let expected_bool_vec = vec![false, false, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_with_no_cost_of_change() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(ONE_BTC * 9/10, 0, 0, &mut utxo_pool);
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn find_solution_with_not_input_fee() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = find_solution(ONE_BTC, COST_OF_CHANGE, 1, &mut utxo_pool);
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn select_coins_bnb_with_match() {
        let mut utxo_pool = build_utxo_vec();
        select_coins_bnb(ONE_BTC, COST_OF_CHANGE, 0, &mut utxo_pool).unwrap();
    }

    #[test]
    fn select_coins_bnb_with_no_match() {
        let mut utxo_pool = build_utxo_vec();
        let utxo_match = select_coins_bnb(1, COST_OF_CHANGE, 0, &mut utxo_pool);
        assert_eq!(None, utxo_match);
    }
}

