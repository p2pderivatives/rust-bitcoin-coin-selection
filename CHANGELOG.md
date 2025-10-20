# 0.8.4 - 2025-10-20

- Bump MSRV to 1.74.0 [#206](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/206)

# 0.8.4 - 2025-10-19

- Remove dependency of CheckedSum trait of bitcoin-units [#198](https://github.com/bitcoin/bitcoin/issues/33419)

# 0.8.3 - 2025-10-13

- Add Coin Grinder [#75](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/75)

# 0.8.2 - 2025-09-29

- Expose errors module [#177](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/177) 
- Make interface more generic [#83](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/83)

# 0.8.1 - 2025-09-26

- Feature gate rand crate [#170](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/170)

# 0.8.0 - 2025-09-17

- Use Weight metric instead of Satisfaction Weight [#96](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/96)
- Add max_weight parameter to selection algorithms [#108](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/108)
- Upgrade to Rust Bitcoin Units 1.0 RC dependency [#104](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/110)
- Change return type to Result [#110](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/114)
- Use concrete type instead of generic type for WeightedUtxo interface [#128](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/128)
- Extend WeightedUtxo fields [#131](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/131)
- Move array of WeightedUtxos to last positional argument for SRD [#164](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/164)
- Rename algorithm function calls [#166](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/164)

# 0.7.2 - 2025-10-01

- Backport: Feature gate rand crate [#170](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/170)

# 0.7.1 - 2025-08-23

- Backport: Find optimal waste score in less iterations for BnB search algorithm [#146](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/146).

# 0.7.0 - 2025-04-22

- Update MSRV to 1.63.0 [#68](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/68)
- ITERATION_LIMIT const now uses a u32 data type. [#76](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/76)
- Both SRD and BNB now return the iteration count. [#76](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/76)
- Add UTXO exclusion shortcut performance optimization. [#67](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/67)
- Change algorithm return types to vector instead of iterator. [#80](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/80)

# 0.6.1 - 2024-10-21

- Fix how a target Amount of zero is handled. [#66](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/66)

# 0.6.0 - 2024-10-08

- Add Libfuzzer and fuzz targets. [#61](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/61)
- Fix early return bug in SRD if a UTXO value exceeds i64::MAX. [#64](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/64)

# 0.5.0 - 2024-07-19

- Add WeightedUtxo trait replacing WeightedUtxo struct. [#58](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/58)
- Add check for overflow to SRD. [#58](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/58)

# 0.4.1 - 2024-07-12

- Mark select_coins_srd as public. [#57](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/57)

# 0.4.0 - 2024-07-05

- Remove Utxo trait and trait bound from `select_coins`. [#51](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/51)

# 0.3.2 - 2024-07-01

- Minor updates to the documentation. [#50](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/50)

# 0.3.1 - 2024-06-29

- Update to rust-bitcoin 0.32.2. [#49](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/49)
- Publish to crates.io. [#48](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/48)

# 0.3.0 - 2024-02-07

- Move existing branch and bound to a new module. [#30](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/30)
- Re-implement branch and bound optimizing for waste score and performance. [#30](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/30)
- Change the return type of SRD to Iterator. [#30](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/30)
- Use Criterion instead of Cargo Bench for benchmarking. [#30](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/30)
- Bump MSRV to 1.56.1 [#30](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/30)

# 0.2.0 - 2023-06-03

- Add Single Random Draw module and a basic error type. [#23](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/23)

# 0.1.0 - 2022-12-17

- Bump rand version. [#7](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/7)
- Fix Single Random Draw. [#4](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/4)
- Add Single Random Draw. [#3](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/3)
- Add coin selection first draft. [#1](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/1)
