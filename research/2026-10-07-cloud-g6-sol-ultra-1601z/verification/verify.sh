#!/usr/bin/env bash
set -euo pipefail
export PATH="${RUNNER_TEMP:?}/g567-lean-4.33.1/lean-4.33.1-linux/bin:$PATH"
export LEAN_NUM_THREADS=1
g6_repo="${RUNNER_TEMP}/research-commons"
g6_packet="$g6_repo/research/2026-10-07-cloud-g6-sol-ultra-1601z"
g6_build="${RUNNER_TEMP}/g6-cloud-build"
mkdir -p "$g6_build"
cp -a "$g6_repo/research/2026-10-04-dot-verified-lean-825-0203z/package/baseline/." "$g6_build/"
cp -a "$g6_packet/sources/." "$g6_build/"
cp "$g6_repo/research/2026-10-07-cloud-g3-1619z/G3ApproximateMomentBarrier.lean" "$g6_build/G3ApproximateMomentBarrier.lean"
cp "$g6_repo/research/2026-10-07-codex-g5-lean/sources/G5FrozenTriplePolynomialKernel.lean" "$g6_build/G5FrozenTriplePolynomialKernel.lean"
cp "$g6_repo/research/2026-10-07-cloud-g5-sol-ultra-1557z/sources/G5FrozenTripleAnalyticSupport.lean" "$g6_build/G5FrozenTripleAnalyticSupport.lean"
mkdir -p "$g6_build/deps"
git init --quiet "$g6_build/deps/mathlib"
git -C "$g6_build/deps/mathlib" remote add origin https://github.com/leanprover-community/mathlib4.git
timeout 180 git -C "$g6_build/deps/mathlib" fetch --quiet --no-tags --depth=1 origin 0df444a360eaa60ab8c11dca51a86af692955474
git -C "$g6_build/deps/mathlib" checkout --quiet --detach FETCH_HEAD
test "$(git -C "$g6_build/deps/mathlib" rev-parse HEAD)" = '0df444a360eaa60ab8c11dca51a86af692955474'
test "$(cat "$g6_build/deps/mathlib/lean-toolchain")" = 'leanprover/lean4:v4.33.1'
cd "$g6_build"
MATHLIB_NO_CACHE_ON_UPDATE=1 timeout 180 lake update
cat lake-manifest.json
python "$g6_packet/verification/run.py" "$g6_build" "$g6_packet/verification/targets.txt" "${GITHUB_SHA:?}"
