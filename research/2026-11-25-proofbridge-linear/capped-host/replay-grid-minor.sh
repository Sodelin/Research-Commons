#!/usr/bin/env bash
set -euo pipefail
L=$(realpath "${1:?supply Lean 4.33.1}")
cd "$(dirname "$0")"
export LEAN_PATH="$PWD"
"$L" --version | grep -F 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
while read -r hash module; do
  f="$module.lean"
  test "$(git hash-object "$f")" = "$hash"
done < grid-minor-baseline.tsv
for m in SamuelAlexanderResearch/BinaryAvoidance SamuelAlexanderResearch/PopulationCounting SamuelAlexanderResearch/InfiniteConservation CappedActualBags CappedConnectedBags CappedHostIntervals CappedGridCross BranchBagProjection CappedMinorBranchCross; do
  "$L" -o "$m.olean" "$m.lean"
done
for m in GridMinorCross CommonConnectedCut GridMinorAssembly SeparateCrossCoordinates GridMinorObstruction EfficiencyBranchWidth EfficiencyGridMinorEnd GridMinorControl SingletonGridBranch; do
  "$L" -o "$m.olean" "$m.lean"
done
for m in GridMinorRouteParity GridBranchUnionConsumer ScopeCheck SingletonGridRegression EfficiencySingletonRegression; do
  "$L" "$m.lean"
done
