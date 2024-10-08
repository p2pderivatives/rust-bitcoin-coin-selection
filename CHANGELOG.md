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
