# 0.1.0 - 2022-12-17

* Initial release.

# 0.2.0 - 2023-06-03

- Add Single Random Draw module and a basic error type.

# 0.3.0 - 2024-02-07

- Move existing branch and bound to a new module.
- Re-implement branch and bound optimizing for waste score and performance.
- Change the return type of SRD to Iterator.
- Use Criterion instead of Cargo Bench for benchmarking.
- Bump MSRV to 1.56.1

# 0.3.1 - 2024-06-29

- Publish to crates.io
- Update to rust-bitcoin 0.32.2 

# 0.3.2 - 2024-07-01

- Minor updates to the documentation

# 0.4.0 - 2024-07-05

- Remove Utxo trait and trait bound from `select_coins`
- Minor updates to the documentation

# 0.4.1 - 2024-07-12

- Update rustfmt version and source code format.
- Mark select_coins_srd as public.
- Minor code refactor and update to documentation.

# 0.5.0 - 2024-07-19

- Add WeightedUtxo trait replacing WeightedUtxo struct. 
- Add check for overflow to SRD.
- Correction to README parameter definitions.

# 0.6.0 - 2024-10-08

- Add Libfuzzer and fuzz targets
- Refactor SRD, BnB test modules
- Minor refactor to SRD selection
- Fix early return bug in SRD if a UTXO value exceeds i64::MAX.

# 0.6.1 - 2024-10-21

- Fix how a target Amount of zero is handled
- Add unit tests to lib module and share common behavior between test modules
- Minor refactor to BnB algorithm to improve readability
- Revise doc comments for both SRD and BnB

# 0.7.0 - 2025-04-22

- Update MSRV to 1.63.0
- ITERATION_LIMIT const now uses a u32 data type.
- Both SRD and BNB now return the iteration count.
- Add UTXO exclusion shortcut performance optimization.
- Change algorithm return types to vector instead of iterator.

# 0.7.1 - 2025-08-23

- Backport: Find optimal waste score in less iterations for BnB search algorithm [#146](https://github.com/p2pderivatives/rust-bitcoin-coin-selection/pull/146).
