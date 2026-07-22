use bitcoin_coin_selection::errors::SelectionError::*;
use bitcoin_coin_selection::{
    branch_and_bound, coin_grinder, select_coins, single_random_draw, Spendable,
};
use bitcoin_units::{Amount, FeeRate, Weight};
use rand::thread_rng;

#[derive(Debug, Eq, PartialEq)]
struct Utxo {
    value: Amount,
}

impl Spendable for Utxo {
    fn total_weight(&self) -> Weight { Weight::from_wu(66) }
    fn value(&self) -> Amount { self.value }
}

fn main() {
    let target = Amount::from_sat_u32(112_358);
    let cost_of_change = Amount::from_sat_u32(768);
    let fee_rate = FeeRate::from_sat_per_vb(10);
    let long_term_fee_rate = FeeRate::from_sat_per_vb(10);

    let amts = [271_828, 314_159];
    let utxos: Vec<_> = amts.iter().map(|&x| Utxo { value: Amount::from_sat_u32(x) }).collect();

    let bnb_selection =
        branch_and_bound(target, cost_of_change, Weight::MAX, fee_rate, long_term_fee_rate, &utxos);
    match bnb_selection {
        Err(SolutionNotFound) => println!("BnB found no solution as expected"),
        _ => panic!("expected no solution found"),
    }

    let srd_selection =
        single_random_draw(target, Weight::MAX, fee_rate, &mut thread_rng(), &utxos);
    match srd_selection {
        Ok((i, utxos)) => println!("SRD solution found: {:?} in {} iterations", utxos, i),
        _ => panic!("expected SRD solution to be found"),
    }

    let cg = coin_grinder(target, Amount::ZERO, Weight::MAX, fee_rate, &utxos);
    match cg {
        Ok((i, utxos)) => println!("CG solution found: {:?} in {} iterations", utxos, i),
        _ => panic!("expected CG solution to be found"),
    }

    let coins =
        select_coins(target, Amount::ZERO, Weight::MAX, fee_rate, long_term_fee_rate, &utxos);

    match coins {
        Ok((i, utxos)) => println!("solution found: {:?} in {} iterations", utxos, i),
        Err(InsufficentFunds) => println!("insufficent funds"),
        Err(IterationLimitReached) => {},
        Err(Overflow(_)) => println!("addition overflow"),
        Err(ProgramError) => println!("un-expected result"),
        Err(SolutionNotFound) => println!("solution not found"),
        Err(MaxWeightExceeded) => println!("max weight exceeded"),
    }
}
