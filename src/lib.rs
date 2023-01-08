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

use combinations::Combinations;
#[cfg(any(test, feature = "rand"))]
use rand::{seq::SliceRandom, thread_rng};

/// Trait that a UTXO struct must implement to be used as part of the coin selection
/// algorithm.
pub trait Utxo: Clone {
    /// Return the value of the UTXO.
    fn get_value(&self) -> u64;
}

/// Select coins first using BnB algorithm similar to what is done in bitcoin
/// core see: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>,
/// and falls back on a random UTXO selection. Returns none if the target cannot
/// be reached with the given utxo pool.
/// Requires compilation with the "rand" feature.
#[cfg(any(test, feature = "rand"))]
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins<T: Utxo>(
    target: u64,
    cost_of_change: u64,
    utxo_pool: &mut [T],
) -> Option<Vec<T>> {
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
#[cfg_attr(docsrs, doc(cfg(feature = "rand")))]
pub fn select_coins_random<T: Utxo>(target: u64, utxo_pool: &mut [T]) -> Option<Vec<T>> {
    utxo_pool.shuffle(&mut thread_rng());

    let mut sum = 0;

    let res = utxo_pool
        .iter()
        .take_while(|x| {
            if sum >= target {
                return false;
            }
            sum += x.get_value();
            true
        })
        .cloned()
        .collect();

    if sum >= target {
        return Some(res);
    }

    None
}

/// Select coins using BnB algorithm similar to what is done in bitcoin
/// core see: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>
/// Returns None if BnB doesn't find a solution.
pub fn select_coins_bnb<T: Utxo>(
    target: u64,
    cost_of_change: u64,
    utxo_pool: &mut [T],
) -> Option<Vec<T>> {
    let solution: Option<Vec<u64>> = find_solution(target, cost_of_change, utxo_pool);

    match solution {
        Some(solution_set) => {
            println!("{:?}", solution_set);
            let mut utxo_solution_set: Vec<T> = Vec::new();

            for i in solution_set.iter() {
                let u = utxo_pool.iter().find(|&x| x.get_value() == *i).unwrap();
                utxo_solution_set.push(u.clone());
            }

            Some(utxo_solution_set)
        }
        None => None,
    }
}

fn find_solution<T: Utxo>(
    target: u64,
    cost_of_change: u64,
    utxo_pool: &[T],
) -> Option<Vec<u64>> {
    let utxo_sum = utxo_pool.iter().fold(0u64, |mut s, u| {
        s += u.get_value();
        s
    });

    let utxo_values: Vec<u64> = utxo_pool.iter().map(|x| x.get_value()).collect();

    let lower_bound = target;
    let upper_bound = cost_of_change + lower_bound;

    let mut best_sum = utxo_sum;
    let mut best_set = None;

    if utxo_sum < lower_bound {
        return None;
    }

    let set_size = utxo_pool.len();

    // If all utxo's in the pool create a match
    // then record that as a solution.  Note that this
    // needs to be done since the Combinations interface
    // won't allow selecting a set that is the same size
    // as the input set. (n choose k) where n can't be the
    // same size as k.
    if utxo_sum >= lower_bound && utxo_sum <= upper_bound {
        let mut v = Vec::with_capacity(utxo_pool.len());
        for u in utxo_pool {
            v.push(u.get_value());
        }
        best_set = Some(v);
    }

    // Start with set size of 1 and then increment
    // the set size by one until all possible combination
    // sizes are exhausted.
    for i in 1..set_size {
        let candidate_sets: Vec<_> = Combinations::new(utxo_values.clone(), i).collect();

        for s in candidate_sets {
            let sum: u64 = s.iter().sum();

            if sum < lower_bound || sum > upper_bound {
                continue;
            }

            if sum < best_sum {
                best_sum = sum;
                best_set = Some(s)
            }
        }
    }

    best_set
}

#[cfg(test)]
mod tests {
    use crate::*;

    const ONE_BTC: u64 = 100000000;
    const TWO_BTC: u64 = 2 * 100000000;
    const THREE_BTC: u64 = 3 * 100000000;
    const FOUR_BTC: u64 = 4 * 100000000;

    const UTXO_POOL: [MinimalUtxo; 4] = [
        MinimalUtxo { value: ONE_BTC },
        MinimalUtxo { value: TWO_BTC },
        MinimalUtxo { value: THREE_BTC },
        MinimalUtxo { value: FOUR_BTC },
    ];

    const COST_OF_CHANGE: u64 = 50000000;

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct MinimalUtxo {
        value: u64,
    }

    impl Utxo for MinimalUtxo {
        fn get_value(&self) -> u64 {
            self.value
        }
    }

    #[test]
    fn find_solution_1_btc() {
        let utxo_match = select_coins_bnb(ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        assert_eq!(1, utxo_match.len());
        assert_eq!(ONE_BTC, utxo_match[0].get_value());
    }

    #[test]
    fn find_solution_2_btc() {
        let utxo_match = select_coins_bnb(TWO_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(1, utxo_match.len());
        assert_eq!(TWO_BTC, utxo_match[0].get_value());
    }

    #[test]
    fn find_solution_3_btc() {
        let utxo_match =
            select_coins_bnb(THREE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(1, utxo_match.len());
        assert_eq!(THREE_BTC, utxo_match[0].get_value());
    }

    #[test]
    fn find_solution_4_btc() {
        let utxo_match =
            select_coins_bnb(FOUR_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(1, utxo_match.len());
        assert_eq!(FOUR_BTC, utxo_match[0].get_value());
    }

    #[test]
    fn find_solution_5_btc() {
        let utxo_match =
            select_coins_bnb(5 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(2, utxo_match.len());
        assert_eq!(ONE_BTC, utxo_match[0].get_value());
        assert_eq!(FOUR_BTC, utxo_match[1].get_value());
    }

    #[test]
    fn find_solution_6_btc() {
        let utxo_match =
            select_coins_bnb(6 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(2, utxo_match.len());
        assert_eq!(TWO_BTC, utxo_match[0].get_value());
        assert_eq!(FOUR_BTC, utxo_match[1].get_value());
    }

    #[test]
    fn find_solution_7_btc() {
        let utxo_match =
            select_coins_bnb(7 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(2, utxo_match.len());
        assert_eq!(THREE_BTC, utxo_match[0].get_value());
        assert_eq!(FOUR_BTC, utxo_match[1].get_value());
    }

    #[test]
    fn find_solution_8_btc() {
        let utxo_match =
            select_coins_bnb(8 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(3, utxo_match.len());

        assert_eq!(ONE_BTC, utxo_match[0].get_value());
        assert_eq!(THREE_BTC, utxo_match[1].get_value());
        assert_eq!(FOUR_BTC, utxo_match[2].get_value());
    }

    #[test]
    fn find_solution_9_btc() {
        let utxo_match =
            select_coins_bnb(9 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(3, utxo_match.len());
        assert_eq!(TWO_BTC, utxo_match[0].get_value());
        assert_eq!(THREE_BTC, utxo_match[1].get_value());
        assert_eq!(FOUR_BTC, utxo_match[2].get_value());
    }

    #[test]
    fn find_solution_10_btc() {
        let utxo_match =
            select_coins_bnb(10 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(4, utxo_match.len());
        assert_eq!(ONE_BTC, utxo_match[0].get_value());
        assert_eq!(TWO_BTC, utxo_match[1].get_value());
        assert_eq!(THREE_BTC, utxo_match[2].get_value());
        assert_eq!(FOUR_BTC, utxo_match[3].get_value());
    }

    #[test]
    fn find_solution_11_btc_not_possible() {
        let utxo_match = select_coins_bnb(11 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn find_solution_with_large_cost_of_change() {
        let utxo_match =
            select_coins_bnb(ONE_BTC * 9 / 10, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(1, utxo_match.len());
        assert_eq!(ONE_BTC, utxo_match[0].get_value());
    }

    #[test]
    fn select_coins_no_cost_of_change_and_no_match() {
        let utxo_match = select_coins_bnb(ONE_BTC * 9 / 10, 0, &mut UTXO_POOL.clone());
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn select_coins_with_no_match_too_large() {
        let utxo_match = select_coins_bnb(ONE_BTC + 1, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn select_coins_with_no_match_too_small() {
        let utxo_match = select_coins_bnb(1, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn select_coins_random_draw_with_solution() {
        let utxo_match = select_coins_random(ONE_BTC, &mut UTXO_POOL.clone());
        utxo_match.expect("Did not properly randomly select coins");
    }

    #[test]
    fn select_coins_random_draw_no_solution() {
        let utxo_match = select_coins_random(11 * ONE_BTC, &mut UTXO_POOL.clone());
        assert!(utxo_match.is_none());
    }

    #[test]
    fn select_coins_bnb_match_with_random() {
        let utxo_match = select_coins(1, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        utxo_match.expect("Did not use random selection");
    }

    #[test]
    fn select_coins_random_test() {
        let mut test_utxo_pool = vec![MinimalUtxo { value: 5_000_000_000 }];

        let utxo_match =
            select_coins(100_000_358, 20, &mut test_utxo_pool).expect("Did not find match");

        assert_eq!(1, utxo_match.len());
    }

    #[test]
    fn select_coins_random_fail_test() {
        let mut test_utxo_pool = vec![MinimalUtxo { value: 5_000_000_000 }];

        let utxo_match = select_coins(5_000_000_358, 20, &mut test_utxo_pool);

        assert!(utxo_match.is_none());
    }

    #[test]
    fn find_solution_with_fractional_size_utxo() {
        let utxo_pool = vec![
            MinimalUtxo { value: ONE_BTC },
            MinimalUtxo { value: TWO_BTC },
            MinimalUtxo { value: 2 * ONE_BTC + 50000000 },
            MinimalUtxo { value: FOUR_BTC },
        ];

        let utxo_match = find_solution(7 * ONE_BTC, 1, &utxo_pool).unwrap();

        assert_eq!(3, utxo_match.len());
        assert_eq!(ONE_BTC, utxo_match[0]);
        assert_eq!(TWO_BTC, utxo_match[1]);
        assert_eq!(FOUR_BTC, utxo_match[2]);
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
            assert_eq!(1000 * COIN, result[1].value);
            assert_eq!(3 * COIN, result[0].value);
        });
    }
}
