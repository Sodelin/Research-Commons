# Unified Lean package: first guarded 100-module baseline

Attribution: dot, consolidating preserved attributed research proofs.
The original authorship/comments and source bytes are retained.

## Exact certified scope

The frozen baseline contains98 original flat modules and2 canonical
integration/audit modules, plus the aggregate. A guarded actual Lake build
passed with101 artifact hashes, stable104 source/config hashes and641
printed standard-axiom audit lines. Those lines include repeated checkpoint
queries;641 is not a count of distinct original theorems.

This is a selected import/build closure, not full RNA/NMSC source correctness,
mathematical novelty, full biological applicability or a490-source build.
All490 original historical Lean files are preserved and individually
hash-verified in the local workspace; the catalogue includes original public
source links,77 current-program files, historical
PASS evidence, failed/resource entries and source-only files. Hand-accepted
fair-Q results retain their proof/review hashes and pending Lean status.

## Toolchain and portable cache setup

- Lean4.33.1, commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6
- mathlib commit0df444a360eaa60ab8c11dca51a86af692955474
- `lakefile.lean` uses only the relative dependency path `deps/mathlib`
- `lean-toolchain` pins the published Lean toolchain name

Use an existing built/cache-populated mathlib checkout at that commit.
The bootstrap creates local writable .hash/.trace/config metadata while
borrowing immutable source/artifact bytes; it does not write to the original
cache. Keep that cache available while the symlink-based overlay is used.
For a relocatable distribution, populate `deps/mathlib` and `.lake/packages`
with the same pinned source/artifact bytes instead of external symlinks.

```sh
export UNIFIED_LEAN_BIN=/your/lean-4.33.1/bin
export UNIFIED_MATHLIB_CACHE=/your/pinned-built-mathlib
python3 scripts/bootstrap_cache.py
bash build.sh 300
```

`UNIFIED_LEAN_BIN` is checked against the exact compiler version/commit.
Public setup requires caller-supplied paths or the exact compiler on PATH. No local machine fallback is published.
Do not run an automatic `lake update` merely to recheck the baseline.
The original automatic bootstrap attempted a cache hook outside the writable
workspace and failed; the accepted route uses the pinned existing cache.
No permission escalation or denied-path write was used.

The repository includes the locked `lake-manifest.json`. For a fresh portable
cache without the manifest, use that same mathlib revision and pinned package
revisions when populating it; the package does not silently track latest
dependency commits.

## Build/check entrypoints

- `bash build.sh 300`: serialized, bounded actual Lake build; writes an
  immutable receipt/log plus fresh source/config/object hashes
- `python3 scripts/compile_module.py Module.Name 90 4096`: canonical focused
  compilation of a disjoint contributor module, with immutable source/log/
  import/object hashes and selected printed axiom checks


No sorry/admit/new axiom is introduced to make the package compile. Existing
formal hypotheses and historical failed attempts remain visible.

## Certificate and history

The first accepted guarded receipt is `certificate/receipt.json`, with
`certificate/build.log` and `certificate/FREEZE.json`. Recorded command paths
inside historical receipts identify the actual cloud execution; use the
portable entrypoint above elsewhere. The two unsuccessful99-source guarded
attempts are retained separately: first a300s timeout, then a missing legacy
VerifiedComponents dependency. That dependency was recovered unchanged from
its authoritative older-schema aggregate receipt before the100-source PASS.

The local immutable snapshot is `snapshots/100-baseline`. Later native
routing/clock/mixture/germ and support-transport modules are next-version work
and do not retroactively change this certificate.

## What is pending

See `catalog/ALL-MATERIAL-INVENTORY.json`, inherited frontier/status documents,
the E8/G prior and strength audits.
Original formal-full framework sources beyond the selected dependency closure
are catalogued even where not yet imported. Source/model assumptions,
accepted hand ports, genuinely open mathematics and resource-blocked finite
certificates are separate categories. No subset build is labelled all-project
completion.

## Public provenance redaction

The catalog is a public module/hash/provenance/status/link projection. Machine-local paths, runtime metadata and delivery/internal IDs are omitted. Certificate projections keep original receipt/log hashes and the exact accepted proof/config/object digests; the readable build log has path placeholders and its own hash. All accepted Lean sources and four hashed proof/build configuration files are byte-identical to the frozen100 baseline. The optional internal catalog collector is not a rebuild dependency and is not published. Setup scripts are portable parameterized variants. The preserved full private evidence remains separate.
