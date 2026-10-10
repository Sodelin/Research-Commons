# Lean executable and modular proof package

`lake build` builds the exact-rational `gparity` executable. `lake build formal`
checks the available public G1–G7 source union in a separate proof context. The
native program accepts the ASCII `RC1 AFFINE`, `RC1 COUNT`, `RC1 CHART`, and `RC1 LAW`
contracts in the adjacent `design/` directory.

The executable uses one shared vector for every affine row. It produces an
independently checked rational witness or nonnegative original-row contradiction
weights. Projection-cap exhaustion returns `UNKNOWN`. `CHART` prints its literal
original-ID shared bank and compiled matrix; its source-admission gate remains
`SOURCE_ADMISSION_NOT_ESTABLISHED`. `COUNT` evaluates the inherited conditional
arithmetic and retains `UNKNOWN_SOURCE_PROVIDER`.

`LAW` compiles the full joint terminal genealogy distribution through the
original edge frontier, including shared COMMON or current-lineage INDEPENDENT
hybrid routing and infinite ancestral completion. It emits every expanded
rooted polynomial and the complete unrooted split pushforward. It checks the
formal sums equal one and applies exact history/state/term/output budgets.
The source-admission and natural physical-image correspondences remain explicit
obligations; this terminal genealogy table does not replace a full tagged-bin law.

## Reproduce

Use Lean 4.33.1, compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. The compiler executable SHA256 must be
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.

```sh
export CONNECTED_LEAN_BIN=/absolute/path/to/lean-4.33.1-linux/bin
export CONNECTED_MATHLIB=/absolute/path/to/mathlib4
export PATH="$CONNECTED_LEAN_BIN:$PATH"
lake build
python3 scripts/build_native.py
python3 scripts/check_core.py
python3 scripts/build_prerequisites.py
lake build formal
python3 scripts/build_connected.py all
```

`build_prerequisites.py` uses the selected existing Mathlib checkout and logs
every attempt. `build_connected.py all` checks this additive inventory's 52
contexts, including isolated historical variants. The newly published
[`2026-10-10-dot-connected-modular-lake-0855z`](../../2026-10-10-dot-connected-modular-lake-0855z/README.md)
package now supplies the frozen 53 required profiles and 25 provisional profiles;
the earlier publication hold is superseded. `PUBLIC-DELIVERY-REVIEW.json` pins
the source/context comparison and the separate qualified reproduction plan.
`scripts/assemble_public.py` can regenerate the additive public graph
and content-addressed source store; the checked-in source store supports offline
proof replay once the pinned external dependencies are available.

## Source and proof boundaries

`DEPENDENCY-GRAPH.json` describes 1,340 compatible public project modules and
1,342 source versions across its 52 contexts. The later frozen public delivery
contains 1,440 source versions across 78 isolated profiles, including the exact
compatible 1,124-module and canonical 1,411-module aggregate contexts. These
inventories remain distinct; the 22 later source versions in this additive
union were not inserted into the publisher's frozen release. `SOURCE-MANIFEST.json`
pins their exact bytes and provenance. These are source inventories, not build
receipts. The complete original theorem bodies are retained. Historical
certificates apply only to their historical source and import identities.

The formal runner compiles owned modules serially at trust level zero with
kernel checking enabled, pins import companion bundles and native loader
identities, and audits every owned declaration. It preserves failed attempts
and refuses automatic retries of the same failed component key. Exact-context
cache admissions are counted separately from fresh current-run compilations.
Ordinary components use 180 seconds and 4 GiB; the existing exact-source
`ThetaCertificate5` exception uses 600 seconds and 6 GiB. Compatible union import
and audit limits are 300 seconds and 6 GiB.

The new constructive proofs in `../reuse/sources/` are checked separately by
`scripts/check_reuse.py`. Its derived `StrictAffineElimination` provider changes
only a broad tactic import to explicit imports, preserving theorem body bytes.
That context has its own hashes and receipts. The current wire witness and
contradiction checkers have compiled refinement proofs. This does not yet prove
the entire native solver, every chart compiler input, or the Rust binary correct.

`scripts/check_typed_reuse.py` checks the original typed bank and concrete native
compiler fixtures against exact fresh public provider objects. The recovered
G7 executable coefficient chain is staged separately by
`scripts/prepare_coefficient_recovery.py`; its prior failed full-epoch source and
unrun code-generation smoke are preserved. A prepared derivative receives no
pass until its own bounded check and full audit succeed.

`CORE-CERTIFICATE.json` and `REUSE-CERTIFICATE.json` identify actual accepted
attempts. Their evidence directories preserve source snapshots, diagnostics,
import bindings, and audit results. The original affine/count sources and binary
identity remain under `evidence/history/affine-v1`; the accepted chart baseline is
also preserved under `evidence/history/chart-v1`. Full-union progress is recorded
in `.build/LATEST-RUN.json` once that runner starts; no full-union pass is claimed
by the source inventory alone.
