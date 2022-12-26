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

use std::cmp::Reverse;

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
    //let solution = find_solution(target, cost_of_change, utxo_pool)?;
    //Some(
        //solution
            //.into_iter()
            //.zip(utxo_pool.iter())
            //.filter_map(|(include, utxo)| if include { Some(utxo.clone()) } else { None })
            //.collect::<Vec<T>>(),
    //)
    //
	let mut coin_selection = Vec::new();
	find_solution(target, cost_of_change, utxo_pool, &mut coin_selection);

    if coin_selection.len() == 0 {
        None
    } else {
        Some(coin_selection)
    }
}

fn find_solution<T: Utxo>(
    target: u64,
    cost_of_change: u64,
    utxo_pool: &mut [T],
    coin_selection: &mut Vec<T>
) {
    let utxo_sum = utxo_pool.iter().fold(0u64, |mut s, u| {
        s += u.get_value();
        s
    });

    let utxo_pool_length = utxo_pool.len();
    utxo_pool.sort_by_key(|u| Reverse(u.get_value()));

    //let mut curr_selection: Vec<bool> = vec![false; utxo_pool_length];
    //let mut best_selection = None;
	let mut remainder = utxo_sum;

    let lower_bound = target;
    let upper_bound = cost_of_change + lower_bound;

    if utxo_sum < lower_bound {
        return;
    }

    for m in 0..utxo_pool_length {
        let mut curr_sum = 0;
        let slice_remainder = remainder;

        for n in m..utxo_pool_length {

			// Can't possibly reach the target value with what's left in the pool.
            if slice_remainder + curr_sum < lower_bound {
                break;
            }

            let utxo = &utxo_pool[n];
            curr_sum += utxo.get_value();
            coin_selection.push(utxo.clone());

			// If we exceeded the target amount, we remove the last one we added.
			// We sorted in decending order, so the next round will add a smaller value.
            if curr_sum > upper_bound {
				coin_selection.pop();
				curr_sum -= utxo.get_value();
			}

			// Subtract the utxo value that was just tested and remove
			// it from the total that's left in the pool.
			remainder -= utxo.get_value();
		}
	}

    //for m in 0..utxo_pool_length {
        //let mut curr_sum = 0;
        //let mut slice_remainder = remainder;

        //for n in m..utxo_pool_length {
            //if slice_remainder + curr_sum < lower_bound {
                //break;
            //}

            //let utxo_value = utxo_pool[n].get_value();
            //curr_sum += utxo_value;
            //curr_selection[n] = true;

            //if curr_sum >= lower_bound {
                //if curr_sum <= upper_bound {
                    //best_selection = Some(curr_selection.clone());
                //}

                //curr_selection[n] = false;
                //curr_sum -= utxo_value;
            //}

            //slice_remainder -= utxo_value;
        //}

        //remainder -= utxo_pool[m].get_value();
        //curr_selection[m] = false;
    //}

    //best_selection
}

#[cfg(test)]
mod tests {
    use crate::*;

	//https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/test/util/setup_common.h#L80
	const CENT: u64 = 1_000_000;

    const UTXO_POOL: [MinimalUtxo; 4] = [
        MinimalUtxo { value: CENT },
        MinimalUtxo { value: 2 * CENT },
        MinimalUtxo { value: 3 * CENT },
        MinimalUtxo { value: 4 * CENT },
    ];

    const COST_OF_CHANGE: u64 = 500_000;

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
        let utxo_match = select_coins_bnb(CENT, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        assert_eq!(1, utxo_match.len());
        assert_eq!(CENT, utxo_match[0].get_value());
	}

	#[test]
	fn find_solution_2_btc() {
		let utxo_match = select_coins_bnb(2 * CENT, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

		assert_eq!(1, utxo_match.len());
		assert_eq!(2 * CENT, utxo_match[0].get_value());
	}

	//#[test]
	//fn find_solution_3_btc() {
        //let utxo_match =
            //select_coins_bnb(THREE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        //assert_eq!(1, utxo_match.len());
        //assert_eq!(THREE_BTC, utxo_match[0].get_value());
	//}

	//#[test]
	//fn find_solution_4_btc() {
        //let utxo_match =
            //select_coins_bnb(FOUR_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        //assert_eq!(1, utxo_match.len());
        //assert_eq!(FOUR_BTC, utxo_match[0].get_value());
	//}

    //#[test]
    //fn find_solution_5_btc() {
        //let utxo_match =
            //select_coins_bnb(5 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        //assert_eq!(2, utxo_match.len());
        //assert_eq!(FOUR_BTC, utxo_match[0].get_value());
        //assert_eq!(ONE_BTC, utxo_match[1].get_value());
    //}

    //#[test]
    //fn find_solution_6_btc() {
        //let utxo_match =
            //select_coins_bnb(6 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        //assert_eq!(2, utxo_match.len());
        //assert_eq!(FOUR_BTC, utxo_match[0].get_value());
        //assert_eq!(TWO_BTC, utxo_match[1].get_value());
    //}

    //#[test]
    //fn find_solution_7_btc() {
        //let utxo_match =
            //select_coins_bnb(7 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        //assert_eq!(2, utxo_match.len());
        //assert_eq!(FOUR_BTC, utxo_match[0].get_value());
        //assert_eq!(THREE_BTC, utxo_match[1].get_value());
    //}

    //#[test]
    //fn find_solution_8_btc() {
        //let utxo_match =
            //select_coins_bnb(8 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        //assert_eq!(3, utxo_match.len());

        //assert_eq!(FOUR_BTC, utxo_match[0].get_value());
        //assert_eq!(THREE_BTC, utxo_match[1].get_value());
        //assert_eq!(ONE_BTC, utxo_match[2].get_value());
    //}

    //#[test]
    //fn find_solution_9_btc() {
        //let utxo_match =
            //select_coins_bnb(9 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        //assert_eq!(3, utxo_match.len());
        //assert_eq!(FOUR_BTC, utxo_match[0].get_value());
        //assert_eq!(THREE_BTC, utxo_match[1].get_value());
        //assert_eq!(TWO_BTC, utxo_match[2].get_value());
    //}

    //#[test]
    //fn find_solution_10_btc() {
        //let utxo_match =
            //select_coins_bnb(10 * ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

        //assert_eq!(4, utxo_match.len());
        //assert_eq!(FOUR_BTC, utxo_match[0].get_value());
        //assert_eq!(THREE_BTC, utxo_match[1].get_value());
        //assert_eq!(TWO_BTC, utxo_match[2].get_value());
        //assert_eq!(ONE_BTC, utxo_match[3].get_value());
    //}

	#[test]
	fn find_solution_11_btc_not_possible() {
		let utxo_match = select_coins_bnb(11 * CENT, COST_OF_CHANGE, &mut UTXO_POOL.clone());
		assert_eq!(None, utxo_match);
	}

	#[test]
	fn find_solution_with_large_cost_of_change() {
		let utxo_match =
			select_coins_bnb(CENT * 9 / 10, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();

		assert_eq!(1, utxo_match.len());
		assert_eq!(CENT, utxo_match[0].get_value());
	}

	#[test]
	fn select_coins_no_cost_of_change_and_no_match() {
		let utxo_match = select_coins_bnb(CENT * 9 / 10, 0, &mut UTXO_POOL.clone());
		assert_eq!(None, utxo_match);
	}

	#[test]
	fn select_coins_not_possible() {
		let utxo_match = select_coins_bnb(CENT * 1 / 4, COST_OF_CHANGE, &mut UTXO_POOL.clone());
		assert_eq!(None, utxo_match);
	}

    //#[test]
    //fn select_coins_with_no_match_too_large() {
        //let utxo_match = select_coins_bnb(ONE_BTC + 1 + COST_OF_CHANGE, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        //assert_eq!(None, utxo_match);
    //}

    //#[test]
    //fn select_coins_with_no_match_too_small() {
        //let utxo_match = select_coins_bnb(1, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        //assert_eq!(None, utxo_match);
    //}

    //#[test]
    //fn select_coins_random_draw_with_solution() {
        //let utxo_match = select_coins_random(ONE_BTC, &mut UTXO_POOL.clone());
        //utxo_match.expect("Did not properly randomly select coins");
    //}

    //#[test]
    //fn select_coins_random_draw_no_solution() {
        //let utxo_match = select_coins_random(11 * ONE_BTC, &mut UTXO_POOL.clone());
        //assert!(utxo_match.is_none());
    //}

    //#[test]
    //fn select_coins_bnb_match_with_random() {
        //let utxo_match = select_coins(1, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        //utxo_match.expect("Did not use random selection");
    //}

    //#[test]
    //fn select_coins_from_large_utxo_pool() {
        //let utxo_range = ONE_BTC..ONE_BTC + 100_000;
        //let mut utxo_pool: Vec<_> = utxo_range.map(|v| MinimalUtxo { value: v }).collect();
        //let utxo_match = select_coins_bnb(ONE_BTC + 1, 20, &mut utxo_pool).unwrap();
        //assert_eq!(1, utxo_match.len());
    //}

    //#[test]
    //fn select_coins_random_test() {
        //let mut test_utxo_pool = vec![MinimalUtxo {
            //value: 5_000_000_000,
        //}];

        //let utxo_match =
            //select_coins(100_000_358, 20, &mut test_utxo_pool).expect("Did not find match");

        //assert_eq!(1, utxo_match.len());
    //}

    //#[test]
    //fn select_coins_random_fail_test() {
        //let mut test_utxo_pool = vec![MinimalUtxo {
            //value: 5_000_000_000,
        //}];

        //let utxo_match = select_coins(5_000_000_358, 20, &mut test_utxo_pool);

        //assert!(utxo_match.is_none());
    //}
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
