#!/usr/bin/env bash
set -euo pipefail
L=$(realpath "${1:?supply the path to Lean 4.33.1}")
cd "$(dirname "$0")"
export LEAN_PATH="$PWD"
"$L" --version | grep -F 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
for m in SamuelAlexanderResearch/BinaryAvoidance SamuelAlexanderResearch/PopulationCounting SamuelAlexanderResearch/InfiniteConservation CappedActualBags CappedConnectedBags CappedGridWalks CappedHostIntervals CappedGridCross CappedGridObstruction; do
  "$L" -o "$m.olean" "$m.lean"
done
"$L" GridObstructionConsumer.lean
