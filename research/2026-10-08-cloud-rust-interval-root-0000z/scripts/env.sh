#!/bin/sh
# Source this file; no network or installation. Override only with an approved cache.
: "${TOOLCHAIN_BASE:?Set TOOLCHAIN_BASE to an approved existing Rust toolchain and cache}"
export RUSTUP_HOME="$TOOLCHAIN_BASE/rustup"
export CARGO_HOME="$TOOLCHAIN_BASE/cargo"
export PATH="$CARGO_HOME/bin:$PATH"
export RUSTUP_TOOLCHAIN=1.90.0
