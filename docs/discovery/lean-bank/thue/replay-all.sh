#!/usr/bin/env bash
set -euo pipefail
ROOT=$(realpath "$(dirname "$0")")
L=$(realpath "${1:?supply pinned Lean 4.33.1}")
PROVIDER=$(realpath "${2:?supply directory containing SamuelAlexanderResearch sources}")
"$L" --version | grep -F 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
d=$(mktemp -d)
trap 'rm -rf -- "$d"' EXIT
cd "$d"
export LEAN_PATH="$d"
mkdir SamuelAlexanderResearch
while read -r path blob sha; do
  [[ "$path" == \#* ]] && continue
  cp "$PROVIDER/$path" "$path"
  test "$(git hash-object "$path")" = "$blob"
  printf '%s  %s\n' "$sha" "$path" | sha256sum -c -
  "$L" -DwarningAsError=true -o "${path%.lean}.olean" "$path"
done < "$ROOT/PROVIDER-MANIFEST.tsv"
for name in Reuse PrefixCount ThueMorsePhaseAliasing; do
  cp "$ROOT/$name.lean" .
  "$L" -DwarningAsError=true -o "$name.olean" "$name.lean"
done
cp "$ROOT/CheckThue.lean" .
"$L" -DwarningAsError=true CheckThue.lean
