use bitcoin::{Amount, FeeRate, Weight};
use bitcoin_coin_selection::{branch_and_bound, select_coins, single_random_draw, single_random_draw_with_rng, WeightedUtxo};
use rand::thread_rng;

#[derive(Debug, Eq, PartialEq)]
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

    let bnb_selection =
        branch_and_bound(target, cost_of_change, fee_rate, long_term_fee_rate, &utxos);
    assert!(bnb_selection.is_none());

    let srd_selection = single_random_draw(target, fee_rate, &utxos);
    if let Some((i, selection)) = srd_selection {
        println!("found selection {:?} found in {:?} iterations", selection, i);
    } else {
        panic!("expected selection found");
    }

    let srd_selection = single_random_draw_with_rng(target, fee_rate, &utxos, &mut thread_rng());
    if let Some((i, selection)) = srd_selection {
        println!("found selection {:?} found in {:?} iterations", selection, i);
    } else {
        panic!("expected selection found");
    }

    let coins_selection =
        select_coins(target, cost_of_change, fee_rate, long_term_fee_rate, &utxos);
    if let Some((i, selection)) = coins_selection {
        println!("found selection {:?} found in {:?} iterations", selection, i);
    } else {
        panic!("expected selection found");
    }
}
