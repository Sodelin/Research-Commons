#!/usr/bin/env bash
set -euo pipefail

source_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
task_runtime_dir="${RUNNER_TEMP:?GitHub runner temp directory required}/g567-lean-4.33.1"
mkdir -p "$task_runtime_dir"
cd "$task_runtime_dir"

archive_url='https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst'
archive_sha='890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235'
curl --fail --location --retry 2 --connect-timeout 20 --max-time 240 "$archive_url" --output lean.tar.zst
printf '%s  %s\n' "$archive_sha" lean.tar.zst | sha256sum --check --strict
tar --zstd --extract --file lean.tar.zst

lean_bin="$task_runtime_dir/lean-4.33.1-linux/bin/lean"
"$lean_bin" --version | tee lean-version.txt
grep -F 'version 4.33.1' lean-version.txt
grep -F '819816b2e0a3' lean-version.txt
sha256sum "$lean_bin"
sha256sum "$source_dir/RuntimeSmoke.lean"

"$lean_bin" --trust=0 "$source_dir/RuntimeSmoke.lean" 2>&1 | tee runtime-smoke.log
printf 'RUNTIME_SMOKE_PASSED source_commit=%s\n' "${GITHUB_SHA:?Frozen source commit required}"
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  {
    printf 'Pinned Lean runtime smoke passed for source commit `%s`.\n\n' "$GITHUB_SHA"
    printf 'Archive SHA256: `%s`.\n\n' "$archive_sha"
    printf 'This verifies the compiler route only. Mathlib and G5/G6/G7 proofs have not been built.\n'
  } >> "$GITHUB_STEP_SUMMARY"
fi
