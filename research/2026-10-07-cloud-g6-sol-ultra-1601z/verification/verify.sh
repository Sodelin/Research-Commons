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
mkdir -p "$g6_build/deps"
timeout 180 git clone --quiet https://github.com/leanprover-community/mathlib4.git "$g6_build/deps/mathlib"
git -C "$g6_build/deps/mathlib" checkout --quiet 0df444a360eaa60ab8c11dca51a86af692955474
test "$(cat "$g6_build/deps/mathlib/lean-toolchain")" = 'leanprover/lean4:v4.33.1'
cd "$g6_build"
MATHLIB_NO_CACHE_ON_UPDATE=1 timeout 180 lake update
cat lake-manifest.json
python "$g6_packet/verification/run.py" "$g6_build" "$g6_packet/verification/targets.txt" "${GITHUB_SHA:?}"
