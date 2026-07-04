use std::collections::HashSet;

use bitcoin::{Amount, FeeRate, Weight};
use bitcoin_coin_selection::{branch_and_bound, select_coins, single_random_draw, WeightedUtxo};

#[derive(Debug, Eq, Hash, PartialEq)]
struct Utxo {
    value: Amount,
}

impl WeightedUtxo for Utxo {
    fn satisfaction_weight(&self) -> Weight { Weight::from_wu(66) }
    fn value(&self) -> Amount { self.value }
}

fn main() {
    let target = Amount::from_sat(112_358);
    let cost_of_change = Amount::from_sat(768);
    let fee_rate = FeeRate::from_sat_per_vb(10).unwrap();
    let long_term_fee_rate = FeeRate::from_sat_per_vb(10).unwrap();

    let amts = [271_828, 314_159];
    let utxos: Vec<_> = amts.iter().map(|&x| Utxo { value: Amount::from_sat(x) }).collect();

    let select_coins =
        select_coins(target, cost_of_change, fee_rate, long_term_fee_rate, &utxos).unwrap();

    let bnb_selection =
        branch_and_bound(target, cost_of_change, fee_rate, long_term_fee_rate, &utxos);
    let srd_selection = single_random_draw(target, fee_rate, &utxos).unwrap();

    if let Some(selection) = bnb_selection {
        assert_eq!(selection, select_coins);
    } else {
        let srd_set: HashSet<_> = srd_selection.1.into_iter().collect();
        let select_set: HashSet<_> = select_coins.1.into_iter().collect();
        // since these are randomized results, compare only the set such
        // that result order does not matter.
        assert_eq!(srd_set, select_set);
    }
}
