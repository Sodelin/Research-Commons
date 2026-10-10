# Lean executable and modular proof package

`lake build` builds the exact-rational `gparity` executable. `lake build formal`
checks the available public G1–G7 source union in a separate proof context. The
native program accepts the ASCII `RC1 AFFINE`, `RC1 COUNT`, and `RC1 CHART`
contracts in the adjacent `design/` directory.

The executable uses one shared vector for every affine row. It produces an
independently checked rational witness or nonnegative original-row contradiction
weights. Projection-cap exhaustion returns `UNKNOWN`. `CHART` prints its literal
original-ID shared bank and compiled matrix; its source-admission gate remains
`SOURCE_ADMISSION_NOT_ESTABLISHED`. `COUNT` evaluates the inherited conditional
arithmetic and retains `UNKNOWN_SOURCE_PROVIDER`.

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
every attempt. `build_connected.py all` checks all 52 available public contexts,
including isolated historical variants. It does not reconstruct the held
53-profile release. `scripts/assemble_public.py` can regenerate the public graph
and content-addressed source store; the checked-in source store supports offline
proof replay once the pinned external dependencies are available.

## Source and proof boundaries

`DEPENDENCY-GRAPH.json` describes 1,340 compatible public project modules and
1,342 source versions across the available contexts. `SOURCE-MANIFEST.json`
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

`CORE-CERTIFICATE.json` and `REUSE-CERTIFICATE.json` identify actual accepted
attempts. Their evidence directories preserve source snapshots, diagnostics,
import bindings, and audit results. The original affine/count sources and binary
identity remain under `evidence/history/affine-v1`. Full-union progress is recorded
in `.build/LATEST-RUN.json` once that runner starts; no full-union pass is claimed
by the source inventory alone.
