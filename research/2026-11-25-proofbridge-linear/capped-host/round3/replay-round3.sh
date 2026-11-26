#!/usr/bin/env bash
set -euo pipefail
L=$(realpath "${1:?supply Lean 4.33.1}")
cd "$(dirname "$0")"
export LEAN_PATH="$PWD"
bash replay.sh "$L"
"$L" -DwarningAsError=true -o TwoLiftTriangle.olean TwoLiftTriangle.lean
for name in FiniteBallDiagonal TerminalExtension TwoLiftLanguage FiniteVersusInfinite ObservationEmbeddingControl ObservationGridBridge; do
  "$L" -DwarningAsError=true "$name.lean"
done
