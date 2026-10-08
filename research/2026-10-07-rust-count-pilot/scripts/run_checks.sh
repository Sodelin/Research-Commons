#!/bin/sh
# Uses a preinstalled project-local toolchain; never downloads or installs.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
if [ -x "$PWD/.toolchain/cargo/bin/cargo" ]; then
    export RUSTUP_HOME="$PWD/.toolchain/rustup"
    export CARGO_HOME="$PWD/.toolchain/cargo"
    export PATH="$CARGO_HOME/bin:$PATH"
fi
python3 scripts/check.py --build
python3 scripts/benchmark.py
