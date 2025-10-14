# Bitcoin Coin-Selection

<p>
    <a href="https://crates.io/crates/bitcoin_coin_selection"><img alt="Crate Info" src="https://img.shields.io/crates/v/bitcoin_coin_selection.svg"/></a>
    <a href="https://github.com/p2pderivatives/rust-bitcoin-coin-selection/blob/master/LICENSE"><img alt="CC0 1.0 Universal Licensed" src="https://img.shields.io/badge/license-CC0--1.0-blue.svg"/></a>
    <a href="https://github.com/p2pderivatives/rust-bitcoin-coin-selection/actions?query=workflow%3AContinuous%20integration"><img alt="CI Status" src="https://github.com/p2pderivatives/rust-bitcoin-coin-selection/workflows/Continuous%20integration/badge.svg"></a>
    <a href="https://docs.rs/bitcoin-coin-selection"><img alt="API Docs" src="https://img.shields.io/docsrs/bitcoin-coin-selection"/></a>
    <a href="https://blog.rust-lang.org/2022/08/11/Rust-1.63.0"><img alt="Rustc Version 1.63.0+" src="https://img.shields.io/badge/rustc-1.63.0%2B-lightgrey.svg"/></a>
</p>


This library provides efficient algorithms to compose a set of unspent transaction outputs (UTXOs).  That is, this crate provides methods for automatic coin-selection for use with Bitcoin wallet development in Rust.

For more details on how automatic coin-selection works:
* [An Evaluation of Coin Selection Stratagies](https://murch.one/wp-content/uploads/2016/11/erhardt2016coinselection.pdf)
* [What is the Waste Metric?](https://murch.one/posts/waste-metric/)

## Why Bother

This project provides a rust clone of the excellent [Bitcoin Core coin-selection algorithms](https://github.com/bitcoin/bitcoin/blob/7502d4e94038eb9dbe079c19bdde57f29e3ea297/src/wallet/coinselection.cpp) in combination with [Rust Bitcoin](https://github.com/rust-bitcoin/rust-bitcoin) types.  Special care is taken to make this Rust implementations highly performant (see [benchmarks](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/blob/6d21811440493ae8880e77f97307a58f4e07e11b/README.md#benchmarks)) and correct with numerous unit tests (cargo test), [property tests](https://github.com/p2pderivatives/rust-bitcoin-coin-selection?tab=readme-ov-file#property-tests) and [fuzz tests](https://github.com/p2pderivatives/rust-bitcoin-coin-selection?tab=readme-ov-file#fuzz-tests).

Bitcoin and Rust Bitcoin are closely followed providing timely updates such that the newest changes are ported and utilized by this project.  Also, bugs and improvements are submitted back to these upstream projects.

## Example
```rust
use bitcoin_units::{FeeRate, Amount, Weight};
use bitcoin_coin_selection::{WeightedUtxo, select_coins, errors::SelectionError::*};

fn main() {
    let utxo_amt = Amount::from_sat_u32(314);
    let utxo = WeightedUtxo::new(utxo_amt, Weight::ZERO, FeeRate::ZERO, FeeRate::ZERO).unwrap();
    let pool = vec![utxo];

    let target = utxo_amt;
    let coins = select_coins(target, Amount::ZERO, Weight::ZERO, &pool);

    match coins {
        Ok((i, utxos)) => println!("solution found: {:?} in {} iterations", utxos, i),
        Err(InsufficentFunds) => println!("insufficent funds"),
        Err(IterationLimitReached) => {},
        Err(Overflow(_)) => println!("addition overflow"),
        Err(ProgramError) => println!("un-expected result"),
        Err(SolutionNotFound) => println!("solution not found"),
        Err(MaxWeightExceeded) => println!("max weight exceeded"),
    }
```

## Supported Algorithms
The current implemented selection algorithms available are:

* select_coins - combines two search routines, `branch_and_bound` and `single_random_draw`.
* single_random_draw - randomly select a set of UTXOs.  Creates a change output.
* branch_and_bound - deterministically attempt to find an exact match.  Attempts to find a changeless solution.
* coin_grinder - deterministically attempt to find a solution with the lowest weight.  Creates a change output.

`select_coins` is the default algorithm one should use.  It attempts to find a changeless solution (not requiring a change output) using `branch_and_bound` using `single_random_draw` as a fallback.  It follows that branch_and_bound may find a solution while single_random_draw always finds a solution unless an error occurs.  Please see the links about for more details on producing a changeless solution.

Detailed algorithm API documentation can be found [here](https://docs.rs/bitcoin-coin-selection/latest/bitcoin_coin_selection/).

## Fuzz tests

To run fuzz tests, install [cargo fuzz](https://crates.io/crates/cargo-fuzz).

The following fuzz tests can then be run:
```
> cargo fuzz run single_random_draw 
> cargo fuzz run branch_and_bound 
> cargo fuzz run coin_grinder 
> cargo fuzz run select_coins
```

## Property tests

This project has a number of property tests created using [arbtest](https://github.com/matklad/arbtest).  The property tests build a random pool of UTXOs and random selection parameters and then assert the results are correct.  To continuously run only the property tests, a simple shell script runs them in a loop.

To continuously run the property tests:
```
> run_proptests.sh
```

## Benchmarks

Benchmarks for the `Branch and Bound Selection` algorithm are written using [Criterion]( https://github.com/bheisler/criterion.rs).

To run the benchmarks use: 
```
> cargo bench
```

Note: criterion requires rustc version 1.65 to run the benchmarks.

### performance comparison

A basic performance comparison between implementations using commodity hardware (My rather old laptop).

|implementation|pool size|ns/iter|
|-------------:|---------|-------|
|      Rust SRD|    1,000| 22,446|
|      Rust BnB|    1,000|552,120|
|  C++ Core BnB|    1,000|816,374|

Note: The measurements where recorded using rustc 1.90 stable.  Expect worse performance with MSRV.

## Minimum Supported Rust Version (MSRV)

This library should always compile with any combination of features on **Rust 1.63.0**.

## Release Notes

- [CHANGELOG](CHANGELOG.md)
