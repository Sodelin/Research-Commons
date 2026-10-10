# Lean executable and modular proof package

`lake build` builds the exact-rational `gparity` executable. `lake build formal`
checks the earlier 1,340-module public G1–G7 union; `lake build latestFormal`
checks the latest compatible 1,433-module composition in a separate context. The
native program accepts the ASCII `RC1 AFFINE`, `RC1 COUNT`, `RC1 CHART`, and `RC1 LAW`
contracts in the adjacent `design/` directory.

The current 1,340-module public union has completed a fresh source build and
complete owned-declaration audit: **97,493 declarations, including 89,658
theorems**, with no owned or nonstandard axioms. Every component was compiled
in that run; no component cache was reused. The exact sources, import closure,
kernel receipts and losslessly compressed full audit are bound by
[`CURRENT-CONNECTED-CERTIFICATE.json`](CURRENT-CONNECTED-CERTIFICATE.json).
This source compilation retains each theorem's original scientific premises.

The latest compatible public composition also passed its fresh combined import
and complete ownership audit: **1,433 modules, 98,330 declarations and 90,253
theorems**, with no owned or nonstandard axioms. That run authenticated 1,433
exact component contexts from earlier accepted compilations and performed a
fresh aggregate and audit. It adds 93 published canonical modules and retains
22 later current modules outside the publisher's frozen canonical context.
[`LATEST-PUBLIC-UNION-CERTIFICATE.json`](LATEST-PUBLIC-UNION-CERTIFICATE.json)
binds every exact source body, its import closure and original context, and the
losslessly compressed full audit. The original 1,340 fresh-run certificate and
all historical profiles remain separate.

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
lake build latestFormal
python3 scripts/build_connected.py all
```

`build_prerequisites.py` uses the selected existing Mathlib checkout and logs
every attempt. `build_connected.py all` checks this additive inventory's 52
contexts, including isolated historical variants. The newly published
[`2026-10-10-dot-connected-modular-lake-0855z`](../../2026-10-10-dot-connected-modular-lake-0855z/README.md)
package now supplies the frozen 53 required profiles and 25 provisional profiles;
the earlier publication hold is superseded. `PUBLIC-DELIVERY-REVIEW.json` pins
the source/context comparison and the separate qualified reproduction plan.
Its byte-identical `lake build connectedQualified` replay completed **52 of 53
required profiles**, including the 1,124-module compatible and 1,411-module
canonical full audits. The original 4 GiB audit failure in the historical
337-module `825/base` context remains recorded in
`PUBLISHED53-PORTABLE-CERTIFICATE.json`. A separately attributed retry of that
same context passed at 6 GiB and 180 seconds, with 12,052 owned declarations and
8,775 theorems; `BASE-RESOURCE-EXCEPTION-CERTIFICATE.json` preserves that audit.
This retry does not rewrite the original frozen reproduction's status.
`latestFormal` reconstructs an isolated context from the portable exact source
manifest, invokes the frozen accepted builder and authenticates each available
component cache before use. Its aggregate and complete audit are always new;
its separate `LATEST-PUBLIC-REPLAY-RESULT.json` reports actual fresh/reuse counts.
`python3 scripts/replay_latest_union.py --prepare-only` verifies and stages that
source context without starting a compiler.
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

`TYPED-REUSE-CERTIFICATE.json` accepts the full original typed bank and two
concrete native chart compiler fixtures over 52 modules. It checks the actual
calendar, shared inverse-rate and hybrid-coin bank, and exact finite-set equality
between the native 9/17 emitted rows and the original compiler. General raw
source admission and all chart inputs remain separate obligations.

`scripts/check_typed_reuse.py` checks the original typed bank and concrete native
compiler fixtures against exact fresh public provider objects. The recovered
G7 executable coefficient chain is staged separately by
`scripts/prepare_coefficient_recovery.py`; its prior failed full-epoch source and
all failed smoke attempts are preserved. `COEFFICIENT-RECOVERY-CERTIFICATE.json`
accepts the repaired full-epoch root over its exact 118-module context, retaining
all original executable definitions and theorem statements at the default
heartbeat limit. The original enumeration provider's native runtime has linked
from its exact generated C and 670 dependency modules. Its unchanged broad
coefficient smoke reached the 180-second limit; no complete smoke pass is
assigned. `NATIVE-SYMBOL-CLOSURE-RESULT.json` and
`FINENUM-SMOKE-RUNTIME-RESULT.json` preserve the distinct link and execution
results. The support-based original epoch evaluator is checked separately.

`POPULATION-FIXTURE-CERTIFICATE.json` binds the 108-module original population
kernel audit and actual compiled-evaluator executions. All eight complete literal
tables and unordered fibres agree with Rust and an independent spectral oracle,
including the 193 supported four-copy outputs. This evaluator is distinct from
the standalone `gparity` executable, and these fixtures do not establish a
universal Rust quotient or whole-epoch refinement.

`SUPPORT-JOIN-CERTIFICATE.json` accepts three separate new proof roots: admitted
panel joining, exact support-only population polynomial readout, and executable
panel joining. Their 117/120/120-module audits overlap; counts must not be added.
The generic support readout avoids enumerating the full raw Code carrier while
proving equality to the unchanged inherited rational polynomial.

`FULL-EPOCH-SUPPORT-CERTIFICATE.json` accepts the generic finite support and
literal-join whole-epoch compiler over 124 modules. Its complete audit checks
3,398 declarations and 2,161 theorems, including equality of the entire rational
multivariate polynomial to the unchanged inherited `fullCoefficients` and the
original physical epoch corollary. Actual mixed-epoch evaluator fixtures have
separately attributed evidence below; universal Rust refinement remains open.

The original mixed-epoch evaluator has now executed all nine fixed contexts:
the eight ordinary fixtures and the separately admitted parallel-occurrence
fixture. Every complete literal selected view, witness and rational coefficient
table agrees with Rust and the independent single mixed-generator oracle.
`ORIGINAL-EPOCH-FIXTURE-CERTIFICATE.json` and
`ORIGINAL-PARALLEL-EPOCH-FIXTURE-CERTIFICATE.json` bind their complete kernel
audits. `ORIGINAL-EPOCH-NATIVE-EXECUTION-RESULT.json` and
`ORIGINAL-PARALLEL-EPOCH-NATIVE-EXECUTION-RESULT.json` bind the separate actual
executions, including the exact generated native enumeration provider. These
are compiled Lean evaluator results; a general Rust refinement and standalone
original-source ELF remain separate obligations.

`EFFECTIVE-BOUNDARY-CERTIFICATE.json` accepts the sparse original pulse and
deterministic boundary compiler over 133 modules, including exact equality to
the inherited polynomial and actual source kernel. The separately checked
`ORIGINAL-BOUNDARY-FIXTURE-CERTIFICATE.json` binds 157/158-module complete audits;
`ORIGINAL-BOUNDARY-NATIVE-EXECUTION-RESULT.json` records **12/12** exact evaluator
comparisons with Rust and the independent finite-action oracle. These preserve
the actual entering register, current live owners and original parallel IDs.
The generic Lean equality and finite execution tests do not establish a
universal Rust refinement or raw source-admission theorem.

`CORE-CERTIFICATE.json` and `REUSE-CERTIFICATE.json` identify actual accepted
attempts. Their evidence directories preserve source snapshots, diagnostics,
import bindings, and audit results. The original affine/count sources and binary
identity remain under `evidence/history/affine-v1`; the accepted chart baseline is
also preserved under `evidence/history/chart-v1`. Kernel acceptance and actual
execution evidence are recorded separately; source inventories alone assign no
pass. The full 109,658,348-byte union audit is distributed as a 7,210,461-byte gzip
with its raw SHA256 and restoration manifest. Verify it with
`scripts/restore_distributed_evidence.py`; archived scratch loader diagnostics
can be verified or restored with `scripts/restore_loader_logs.py`. Neither
compression nor diagnostic reclamation changes original receipts or objects.
The portable published-profile projection retains all original certificate
bytes and a reversible mapping for every snapshot file. Verify the complete
original snapshot identities with `scripts/restore_evidence_projection.py` and
its `RESTORE-MANIFEST.json`; the bulky original snapshot remains local evidence.
