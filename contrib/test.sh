#!/bin/sh
#
# CI script for the `coin selection` crate.

set -ex

FEATURES="rand"

# Sanity checks.
cargo --version
rustc --version

cargo build --all-features
cargo test --all-features

if [ "$DO_FEATURE_MATRIX" = true ]; then
    # No features.
    cargo build --no-default-features
    cargo test --no-default-features

    # Single features.
    for feature in ${FEATURES}
    do
        cargo build --no-default-features --features="$feature"
        cargo test --no-default-features --features="$feature"
    done
fi

if [ "$DO_LINT" = true ]
then
    rustup component add clippy
    cargo clippy --all-features --all-targets -- -D warnings
fi

# Build the docs if told to (this only works with the nightly toolchain)
if [ "$DO_DOCS" = true ]; then
    RUSTDOCFLAGS="--cfg docsrs" cargo +nightly rustdoc --all-features -- -D rustdoc::broken-intra-doc-links -D warnings || exit 1
fi

# Bench if told to, only works with non-stable toolchain (nightly, beta).
if [ "$DO_BENCH" = true ]; then
    RUSTFLAGS='--cfg=bench' cargo bench
fi
