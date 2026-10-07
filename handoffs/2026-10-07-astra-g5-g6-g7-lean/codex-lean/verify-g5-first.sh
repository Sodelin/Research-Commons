#!/usr/bin/env bash
set -euo pipefail

export PATH="${RUNNER_TEMP:?}/g567-lean-4.33.1/lean-4.33.1-linux/bin:$PATH"
source_repo="${RUNNER_TEMP}/research-commons"
proof_dir="${RUNNER_TEMP}/g5-first-verification"
mkdir -p "$proof_dir"

frozen_commit='2c08a6b72316c3699e4e2d354bdab1befd739d0c'
source_path='research/2026-10-07-astra-g5-m3-7e3b/sources/G5FrozenTriplePolynomialKernel.lean'
expected_blob='2140fea9686852657dff17f17c979cd1e752eaba'
git -C "$source_repo" fetch --no-tags --depth=1 origin "$frozen_commit"
git -C "$source_repo" show "$frozen_commit:$source_path" > "$proof_dir/G5FrozenTriplePolynomialKernel.lean"
test "$(git hash-object "$proof_dir/G5FrozenTriplePolynomialKernel.lean")" = "$expected_blob"
sha256sum "$proof_dir/G5FrozenTriplePolynomialKernel.lean"

cd "$proof_dir"
cat > lakefile.toml <<'LAKE'
name = "g5FirstVerification"
version = "0.1.0"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "0df444a360eaa60ab8c11dca51a86af692955474"
LAKE
printf '%s\n' 'leanprover/lean4:v4.33.1' > lean-toolchain
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = '0df444a360eaa60ab8c11dca51a86af692955474'
test "$(cat .lake/packages/mathlib/lean-toolchain)" = 'leanprover/lean4:v4.33.1'
cat lake-manifest.json

lake exe cache get \
  Mathlib.Analysis.SpecialFunctions.Exp \
  Mathlib.Tactic.FinCases \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.FunProp \
  Mathlib.Tactic.Positivity \
  Mathlib.Tactic.Ring

lake env lean --trust=0 -j1 -M4096 G5FrozenTriplePolynomialKernel.lean 2>&1 | tee g5-compiler.log
printf 'G5_COMPONENT_COMPILED source_commit=%s blob=%s\n' "$frozen_commit" "$expected_blob"
