use crate::Utxo;
use std::cmp::Reverse;

/// Select coins using BnB algorithm similar to what is done in bitcoin
/// core see: <https://github.com/bitcoin/bitcoin/blob/f3bc1a72825fe2b51f4bc20e004cef464f05b965/src/wallet/coinselection.cpp>
/// Returns None if BnB doesn't find a solution.
pub fn select_coins_bnb<T: Utxo>(
    target: u64,
    cost_of_change: u64,
    utxo_pool: &mut [T],
) -> Option<Vec<T>> {
    let solution = find_solution(target, cost_of_change, utxo_pool)?;
    Some(
        solution
            .into_iter()
            .zip(utxo_pool.iter())
            .filter_map(|(include, utxo)| if include { Some(utxo.clone()) } else { None })
            .collect::<Vec<T>>(),
    )
}

fn find_solution<T: Utxo>(
    target: u64,
    cost_of_change: u64,
    utxo_pool: &mut [T],
) -> Option<Vec<bool>> {
    let utxo_sum = utxo_pool.iter().fold(0u64, |mut s, u| {
        s += u.get_value();
        s
    });

    let utxo_pool_length = utxo_pool.len();
    utxo_pool.sort_by_key(|u| Reverse(u.get_value()));

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

            let utxo_value = utxo_pool[n].get_value();
            curr_sum += utxo_value;
            curr_selection[n] = true;

            if curr_sum >= lower_bound {
                if curr_sum <= upper_bound {
                    best_selection = Some(curr_selection.clone());
                }

                curr_selection[n] = false;
                curr_sum -= utxo_value;
            }

            slice_remainder -= utxo_value;
        }

        remainder -= utxo_pool[m].get_value();
        curr_selection[m] = false;
    }

    best_selection
}

#[cfg(test)]
mod tests {
    use crate::*;
    use crate::branch_and_bound::find_solution;

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
        let utxo_match = find_solution(ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![false, false, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_2_btc() {
        let utxo_match = find_solution(TWO_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![false, false, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_3_btc() {
        let utxo_match = find_solution(THREE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![false, false, true, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_4_btc() {
        let utxo_match = find_solution(FOUR_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![false, true, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_5_btc() {
        let five_btc = FOUR_BTC + ONE_BTC;
        let utxo_match = find_solution(five_btc, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![false, true, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_6_btc() {
        let six_btc = FOUR_BTC + TWO_BTC;
        let utxo_match = find_solution(six_btc, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![false, true, true, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_7_btc() {
        let seven_btc = FOUR_BTC + THREE_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![true, false, true, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_8_btc() {
        let seven_btc = FOUR_BTC + THREE_BTC + ONE_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![true, true, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_9_btc() {
        let seven_btc = FOUR_BTC + THREE_BTC + TWO_BTC;
        let utxo_match = find_solution(seven_btc, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![true, true, true, false];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_10_btc() {
        let ten_btc = ONE_BTC + TWO_BTC + THREE_BTC + FOUR_BTC;
        let utxo_match = find_solution(ten_btc, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![true, true, true, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_11_btc_not_possible() {
        let ten_btc = ONE_BTC + TWO_BTC + THREE_BTC + FOUR_BTC;
        let utxo_match = find_solution(ten_btc + ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn find_solution_with_large_cost_of_change() {
        let utxo_match =
            find_solution(ONE_BTC * 9 / 10, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
        let expected_bool_vec = vec![false, false, false, true];
        assert_eq!(expected_bool_vec, utxo_match);
    }

    #[test]
    fn find_solution_with_no_cost_of_change() {
        let utxo_match = find_solution(ONE_BTC * 9 / 10, 0, &mut UTXO_POOL.clone());
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn find_solution_with_not_input_fee() {
        let utxo_match = find_solution(ONE_BTC + 1, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        assert_eq!(None, utxo_match);
    }

    #[test]
    fn select_coins_bnb_with_match() {
        select_coins_bnb(ONE_BTC, COST_OF_CHANGE, &mut UTXO_POOL.clone()).unwrap();
    }

    #[test]
    fn select_coins_bnb_with_no_match() {
        let utxo_match = select_coins_bnb(1, COST_OF_CHANGE, &mut UTXO_POOL.clone());
        assert_eq!(None, utxo_match);
    }
}

#[cfg(bench)]
#[cfg(test)]
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
