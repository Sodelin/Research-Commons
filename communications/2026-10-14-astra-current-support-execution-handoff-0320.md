# Next actual target: accepted provider and supplied support bound

This is an execution handoff, not a new runner or completed build. At the last
closed public checkpoint, batch080 passed through external index3284 at
`9b6a7219c7d059b89963e17451fac713db1768e0`. Rust owns only081–082, eight fresh
modules each. No next compiler starts until its explicit closed/no-active
handoff and the coordinator's continuation confirmation. Live observations do
not establish a completed batch.

Finish the unchanged3591 external plan first. Its SHA is
`ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10`.
Use `one_batch_small.py` SHA
`89b335b1f553e098b48ebc46f3a1479ce9181598ba35ce210472e63a77b8661b`,
one explicit eight-module job, then actual finish and source/log/object readback.
The final3591 boundary needs a complete-plan readback: the existing
`OWNER-CLOSED-READBACK.py` deliberately refuses that boundary because its
predecessor expects `complete=false`. Do not bypass that refusal or misreport
its nonfinal assumptions.

The first owned target keeps the exact319 accepted-source graph and selected
versions, then the existing kernel, three literal certificates and three new
adapter/aggregate modules. The preparation stage stops at323; complete target
has326 source records. These are scheduling descriptions, not proof of scope
completion. Full1613/3661 and fixture overlays are separate follow-ons.

Fixed paths for this target:

```sh
astra_repo=/workspace/Research-Commons
astra_support=$astra_repo/research/2026-10-13-astra-positive-support-adapter-0830z
astra_previous=$astra_repo/research/2026-10-13-astra-unified-solver-0645z
astra_driver=$astra_repo/research/2026-10-14-astra-detached-owned-batch-0025z/one_owned_batch.py
astra_sources=/workspace/scratch/astra-support-sources-0936
astra_external=/workspace/scratch/astra-support-external-0840
astra_owned=/workspace/scratch/astra-support-owned-namespace-0025
astra_mathlib=/workspace/scratch/astra-mathlib-0645
astra_lean_bin=/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin
```

Before the first owned job, confirm no active compiler, guard or launcher;
no relevant PAUSE-BUILDS marker; adequate disk/RAM/physical headroom; exact
closed external receipt/log/artifact completion; and that the new owned state
is absent. Preserve the external completion/source evidence before proceeding.
The fixed driver preliminarily refuses an incomplete prefix; its guarded
builder performs the authoritative full dependency/source/log/object/namespace
authentication before any owned compilation. Counted receipt filenames alone
are insufficient.

The reviewed driver SHA is
`157991882a6773c580fb8dcc226296b34d552bca39f09605a947fc55d3c727d7`.
The namespace builder SHA is
`2d5c8504c9380b5b2353539560b5b8e954cb2e909a09e5e80903214fc346ccda`.
Exact transitive pins are in the driver's SOURCE-PINS.json. Namespace16 and
owned-driver12 controls are completed synthetic controls, separately published;
neither means the production owned pilot has run.

First production pilot, still pending:

```sh
python3 -B "$astra_driver" launch --batch-id 1 --start-index 0 --fresh-budget 1
python3 -B "$astra_driver" status --batch-id 1 --start-index 0 --fresh-budget 1
# Only after the actual guard closes:
python3 -B "$astra_driver" finish --batch-id 1 --start-index 0 --fresh-budget 1
```

Read the actual FINISH and preserved delta; distinguish resumed receipts,
new authenticated clones and fresh compilations. Choose each subsequent start
from the verified `next_owned_receipt_index`, not the fresh count. Keep at most
16 fresh components per explicit job, narrowing on observed runtime. The same
6GiB virtual/4GiB physical stop,900wall/600CPU,1GiB file,8GiB disk floor and1GiB
available-RAM floor remain fixed. No automatic next job or retry exists.
Preserve failures, eventless files and exclusive logs before any reviewed repair.

After actual provider preparation, run the exact guarded native Lake command
that the final collector expects. Choose a fresh `astra_lake_out` directory;
the following command is pending, not an execution receipt:

```sh
python3 "$astra_previous/guard.py" --out "$astra_lake_out" \
  --cwd "$astra_support" --wall 900 --cpu 600 --memory-mib 6144 --file-mib 1024 -- \
  env MIMALLOC_ARENA_RESERVE=16384 LEAN_NUM_THREADS=1 \
  LEAN_STACK_SIZE_KB=8192 LEAN_IMPORT_WORKERS=1 \
  ASTRA_SUPPORT_SOURCES="$astra_sources" \
  ASTRA_SUPPORT_EXTERNAL_STATE="$astra_external" \
  ASTRA_SUPPORT_STATE="$astra_owned" ASTRA_MATHLIB_ROOT="$astra_mathlib" \
  ASTRA_LEAN_BIN="$astra_lean_bin" \
  "$astra_lean_bin/lake" -f lakefile.namespace.lean build adapter
```

This target compiles the remaining adapter modules and separately executes
`audits/ProviderInterfaceAudit.lean`, SHA
`130006bf4b3f2d0084b75a49e53d93121170f6074a9bfef204079667738e78ef`.
Require actual RESULT/INVOCATION/log/object identities, all expected theorem
axiom audits without sorryAx/placeholders, the literal printed full types,
definition equalities and explicit-signature examples. Compare original
`positiveCertificateGrid_card_lt` and the new supplied-support binders and
assumptions. Source/body hashes and an axiom-head count do not establish
historical elaborated declaration equivalence; any unavailable historical
type/option comparison remains explicitly unresolved.

Only after that actual Lake guard passes, run
`capture_final_namespace.py` in a separate bounded, non-compiling guard with
`--source-root "$astra_sources" --state "$astra_owned"`
`--external-state "$astra_external" --mathlib-root "$astra_mathlib"`
`--lean-bin "$astra_lean_bin" --lake-output "$astra_lake_out"`
`--out "$astra_fresh_export"`. It reauthenticates complete sources, reuse
origins, logs, objects, namespace and exact guarded Lake/interface bindings,
then copies source/ledger/configuration evidence without binaries. Preserve
any partial export. Independently review the closed export and publish with
non-force remote tree/blob readback.

Final scope must retain exact coefficients/levels, nonzero evaluation,
nonnegative weights/polynomial and annihilation; only positive-mass values need
the domain premise, endpoint1 is included, repeated values count once and zero
weights add no support. No desired cardinality or unknown target is supplied
as input. This conditional support theorem does not produce a protected
physical representative or arbitrary-input G3 closure. Missing provider0616
remains separate. Original042/057/059 outer outcomes remain UNKNOWN despite
their separate recovery authentication. A successful aggregate combines fresh
work and authenticated reuse; it is not a from-scratch rebuild of all sources.
