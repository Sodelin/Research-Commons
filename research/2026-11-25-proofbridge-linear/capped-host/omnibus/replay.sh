#!/usr/bin/env bash
set -euo pipefail
L=$(realpath "${1:?provide pinned lean}")
BASE=$(realpath "${2:?provide clean-built round-three source directory}")
cd "$(dirname "$0")"
"$L" --version | grep -F 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
test -f "$BASE/FixedGender.olean"
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
export LEAN_PATH="$build:$PWD/lean:$BASE"
"$L" -DwarningAsError=true -o "$build/NanuqOmnibusFixture.olean" lean/NanuqOmnibusFixture.lean
cp "$BASE/TwoLiftLanguage.lean" "$build/"
(cd "$build"; echo "b5b2464b3b54ffb526f1645142df7d7090ccb1fc7c5cf2a7e8b92378e21ddcd4  TwoLiftLanguage.lean" | sha256sum -c -; "$L" -DwarningAsError=true -o TwoLiftLanguage.olean TwoLiftLanguage.lean)
for name in ObservationCertificate LineGraphTriangleGuard ComponentTransport SignatureDiagonal FixedColorExact MergedRoot; do
  "$L" -DwarningAsError=true "lean/$name.lean"
done
(cd prototype; sha256sum -c SHA256SUMS; PYTHONDONTWRITEBYTECODE=1 python -m unittest -v)
PYTHONDONTWRITEBYTECODE=1 python fixture/check_nanuq_paired_fixture.py
