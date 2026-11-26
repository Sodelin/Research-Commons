#!/usr/bin/env bash
set -euo pipefail
L=$(realpath "${1:?supply Lean 4.33.1}")
cd "$(dirname "$0")"
export LEAN_PATH="$PWD"
"$L" --version | grep -F 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
sha256sum -c SHA256SUMS
while read -r hash module; do
 f="SamuelAlexanderResearch/$module.lean"
 test "$(git hash-object "$f")" = "$hash"
 "$L" -o "${f%.lean}.olean" "$f"
done < pinned-git-blobs.tsv
for m in CappedActualBags CappedConnectedBags CappedGridWalks CappedHostIntervals CappedGridCross CappedGridObstruction CappedPaddingLanguage CappedLabeledGrid FixedGender CappedPresentedPadding CappedConcretePad PresentedCappedHost ChronologicalEncoding ChronologyFixture Alexander001 UnboundedPadding CappedGridGlue PaddingObstructionConsumer; do
 "$L" -o "$m.olean" "$m.lean"
done
for m in GridObstructionConsumer PresentedCappedGridConsumer JamConsumer UnboundedPaddingConsumer CappedGridGlueConsumer FixedGenderObstruction; do
 "$L" "$m.lean"
done
