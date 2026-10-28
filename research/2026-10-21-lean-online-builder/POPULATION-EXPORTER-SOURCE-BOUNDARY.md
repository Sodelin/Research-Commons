# Population exporter source boundary

The retained Rust exporter has one confirmed Lean proof-target error. It emits
`taxa_exact : N.leaf = (fun i => ...)`, while the original `RootedBinary.leaf`
has embedding type. The corrected target coerces that embedding to its original
taxon function: `(N.leaf : Fin nt → Fin nv) = (fun i => ...)`. No taxon order,
edge occurrence, source class or array value changes.

The [source correction proposal](proposals/PopulationExporterTaxaCoercion.patch)
is bound to original exporter SHA256
19967b34c4ba2a4b55cb4c93745ed7efd573d2e10edebb67274603d01f78404c,
unchanged at retained successor4ac6aa8565ec8aa2bac1d5dc4b3d31af64e86859.
Applying only that patch gives proposed source SHA256
2ceaff7ac28d712d173e10aaa5632b8f8a6956d3b96d503686631415e94490cf.
The original Rust source was not edited, compiled or executed.

The corrected110,940-byte [source-boundary document](lean/scoped-context/PopulationExporterSourceBoundary.lean)
passed all eight complete selected type/axiom audits, with zero errors and
three retained benign warnings. Source SHA256 is
8d0b7e50dccb9f627e7158753498a519c65d83a1ec9652b75e682a87a288ea0a;
exact submitted SHA256 is
309480f47c38491d919aaaeaecbf36beea607a3575a711ccc4ab19a6eb209f71.
Normal exit0, unchanged source inventories and hosted Lean4.35/mathlib56a005
version metadata, and verified encrypted recovery are recorded in the
[complete verification](POPULATION-EXPORTER-SOURCE-BOUNDARY-VERIFICATION.json).
All eight axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`.

This reuses the original arbitrary-finite `decideReach` and
`sourceValidDecidable`, the old admitted two-tip source and its old input
constructor for arbitrary copy count/population/register. It adds no source
factory, validity oracle, fixture engine or population kernel. The checked
99,274-byte physical certificate is an unchanged literal prefix. Original
fixture producers and IO are excluded by exact source boundaries.
The [prior-solution preflight](CAPTURED-INPUT-PREFLIGHT.json) and
[command map](POPULATION-EXPORTER-SOURCE-BOUNDARY-SOURCE-MAP.json) identify the
complete retained predecessors, later exporter and exact selected commands.

The initial111,123-byte document remains **REJECTED**. It contains the real
embedding/function mismatch and an unrelated projection error: an unused
`noHybrid` declaration referenced a namespace omitted from this projection.
The corrected document excludes that unused command. This does not accuse the
original source of a missing import. All diagnostics, exact source/preparer/map
and eight clean partial audits remain in the
[revision record](POPULATION-EXPORTER-SOURCE-BOUNDARY-REVISIONS.json); those
partials never passed the rejected document.

This is source compatibility verification. No native table was captured,
rendered or checked; no particular `coefficient_table_checked` theorem or
native proof/result-origin binding follows. `Prepared` already supplies the
borrowed input/table/document association and remains the intended exporter.
Actual captured arrays, admitted literal snapshots and complete table check,
then the existing sparse-row/word/completion/observer bindings remain necessary.
The native778 source selection is unchanged. Pinned imports/objects and actual
native execution remain held before the original-owner controller and
transitive encrypted writers are bound.

The existing public driver exposes this exact case:

```sh
python3 -B check_online_context.py --case population-exporter-source-boundary \
  --record-codec /absolute/existing/featurectl --codec-sha256 VERIFIED_SHA256
```

It uses the unchanged full-context client and capture helper. Reproduction is
a fresh proof check, not a replay of a prior receipt. The source preparer
requires the pinned original source-store, retained fixture inputs and exact
exporter source identified in its map; its review inventory is not a parser
or proof checker. A hosted document pass is separate from installed imports
and Rust/compiler-controller acceptance.
