# Coin Selection

This library provides efficient algorithms to compose a set of unspent transaction outputs (UTXOs).  When a Bitcoin wallet creates a transaction, there is a diverse set of trade-offs to decide which UTXOs to choose.  The trade-offs for deciding which set of UTXOs to use are described in depth here: [An Evaluation of Coin Selection Stratagies](https://murch.one/wp-content/uploads/2016/11/erhardt2016coinselection.pdf) as well as here: [What is the Waste Metric?](https://murch.one/posts/waste-metric/).

## TLDR 

The goal of coin selection is to minimize the amount of waste in a selection.  The waste for a given selection is calculated as `input_weight × (feerate - longterm_feerate) + cost_of_change + excess`.

## Usage

The current interface is provided via `select_coins()` function.  The required parameters are:

`target` - *The desired transaction amount.*  
`cost_of_change` - *How expensive it is to create a new output (UTXO).*  
`utxo_pool` - *The set of possible UTXOs to choose from.*  


As discussed in the literature above, ideally we want to choose a selection from the existing UTXO set available to the wallet.  However, if there is no combination that efficiently matches the target spend amount, then creating a change output by splitting a UTXO is the next best option.  Therefore, the algorithm takes into account the current cost of creating a new output (cost_of_change).

## Benchmarks

To run the benchmarks use: `cargo bench`.

### performance comparison

A basic performance comparison between this current [Rust BnB](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/28/files#diff-9098d62be93e83524a8371395c973d761a95000d1c295f600a8c808e917c16d9R122) implementation and the [Bitcoin Core](https://github.com/bitcoin/bitcoin/blob/4b1196a9855dcd188a24f393aa2fa21e2d61f061/src/wallet/coinselection.cpp#L76) version using commodity hardware (My rather old laptop).

|implementation|pool size|ns/iter|
|-------------:|---------|-------|
|      Rust BnB|    1,000|819,320|
|  C++ Core BnB|    1,000|816,374|

## Minimum Supported Rust Version (MSRV)

This library should always compile with any combination of features on **Rust 1.48**.
