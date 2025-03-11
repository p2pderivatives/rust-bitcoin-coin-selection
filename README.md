# Bitcoin Coin-Selection

This library provides efficient algorithms to compose a set of unspent transaction outputs (UTXOs).  When a Bitcoin wallet creates a transaction, there is a diverse set of trade-offs to decide which UTXOs to choose.  The trade-offs for deciding which set of UTXOs to use are described in depth here: [An Evaluation of Coin Selection Stratagies](https://murch.one/wp-content/uploads/2016/11/erhardt2016coinselection.pdf) as well as here: [What is the Waste Metric?](https://murch.one/posts/waste-metric/).

## Usage

The current interface is provided via `select_coins()` function.  The required parameters are:

`target` - *The desired transaction amount.*  
`cost_of_change` - *How expensive it is to create a new output (UTXO).*  
`fee_rate` - *The current fee_rate.*  
`long_term_fee_rate` - *The long_term_fee_rate which helps determine if fee_rate is expensive or cheap.*  
`weighted_utxos` - *The set of possible weighted UTXOs to choose from.*


As discussed in the literature above, we want to find a "changeless" solution.  A changeless solution is one that exceeds the `target` however is less than `target` + `cost_of_change`.  If no changeless solution can be found, then creating a change output by splitting a UTXO is the next best outcome.  To that end, `select_coins()` initially attempts a Branch and Bound selection algorithm to find a changeless solution.  If no changeless solution is found, then `select_coins()` falls back to a Single Random Draw selection strategy.

## Fuzz tests

To run fuzz tests, install [cargo fuzz](https://crates.io/crates/cargo-fuzz).

The following fuzz tests can then be run:
```
> cargo fuzz run select_coins_srd
> cargo fuzz run select_coins_bnb
> cargo fuzz run select_coins
```

## Property tests

This project has a number of property tests created using [arbtest](https://github.com/matklad/arbtest).  The property tests build a random pool of UTXOs and random selection parameters and then assert the results are correct.  To continuously run only the property tests, a simple shell script runs them in a loop.

To continuously run the property tests:
```
> run_proptests.sh
```

## Benchmarks

To run the benchmarks use: 
```
> cargo bench
```

Note: criterion requires rustc version 1.65 to run the benchmarks.

### performance comparison

A basic performance comparison between this Rust BnB implementation and [Bitcoin Core](https://github.com/bitcoin/bitcoin/blob/4b1196a9855dcd188a24f393aa2fa21e2d61f061/src/wallet/coinselection.cpp#L76) using commodity hardware (My rather old laptop).

|implementation|pool size|ns/iter|
|-------------:|---------|-------|
|      Rust BnB|    1,000|897,810|
|  C++ Core BnB|    1,000|816,374|

Note: The measurements where recorded using rustc 1.75.  Expect worse performance with MSRV.

## Minimum Supported Rust Version (MSRV)

This library should always compile with any combination of features on **Rust 1.63.0**.

## Release Notes

- [CHANGELOG](CHANGELOG.md)
