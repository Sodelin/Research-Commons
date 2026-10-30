# Arbitrary-size NANUQ ordered-tree restriction — Lean provider

**Cleanly kernel-checked at ordered-tree syntax scope. Not the full raw-network NANUQ theorem.**

This packet closes the previously missing arbitrary-size restriction step between an adjacent-copy ordered tree and the frozen 3–6-label finite provider. It does not assume a restriction, transport, plane order, or positive-coefficient certificate.

## Exact scope

For every finite ordered full-binary `Tree`, every original label count `n ≥ 3`, and every adjacent duplication mask with the required tip count, the actual inherited anchor definition has:

- nonnegative circular boundary coefficients for all valid anchors and two distinct ordered gaps;
- zero coefficients when a nonadjacent boundary quartet is absent;
- exact uniform **distinct-resolution** rational means, with codes restricted to 1, 4 or 5;
- the boundary-anchor positivity equivalence and pendant-anchor value 2.

There is no original-size, depth, duplication-count or reticulation-level bound in these ordered-tree theorems. No switching-multiplicity weighted metric substitutes for original NANUQ's local score.

## Provider chain

1. `Pruning`: delete **all occurrences** of every excluded label; recursively suppress empty/unary nodes. Prove exact retained leaf order and iff preservation of all retained quartet cut witnesses, with explicit outside contexts.
2. `RootRotation`, `Reroot`: expose the first retained tip by rotations **at the whole root only**. Complementary child cuts make those rotations split-preserving. Internal associativity is not asserted. One resulting tree preserves all retained queries simultaneously.
3. `AdjacentBlocks`, `Relabel`, `CanonicalRestriction`: retained label blocks remain adjacent; order-rank relabeling gives an actual finite mask with a proved bound.
4. `CyclicGaps`, `RankOrder`, `SixLabels`: prove cyclic wraparound and modular-successor preservation, strict rank order, and that retaining both boundary endpoints and both anchors gives 3–6 labels. Shared-label singleton boundaries are included.
5. `IntervalBridge`, `FiniteEdgeBridge`, `Decorate`: connect labeled subtree-cut semantics to the **unchanged finite provider's** actual `Tree`, interval and `edgeWitness` definitions. Pendant cuts are removed only after proving they cannot witness two distinct labels on each side.
6. `QuartetLookup`, `QueryExists`, `QuartetRelabel`, `CodeBridge`, `QueryTransport`: prove actual increasing-quartet lookup, exact three-bit family transport, and relabeled side predicates. Lookup is proved for arbitrary original `n`, not sampled.
7. `ConstructTransport`: construct the restricted mask/tree and its complete edge transport; do not accept transport as a hypothesis at the final endpoint.
8. `AnchorTransport`, `CoefficientTransport`, `AllSizeCodes`, `ZeroTransport`, `RestrictionEndpoints`: preserve the inherited original anchor, exact distinct mean and queried coefficient, then consume the frozen finite theorem.

The two trees used by a transport are the original tree and its one constructed restriction. No quartet-dependent source replacement or independent choice of receiver is used.

## Exact proof and trust receipts

- `RestrictionEndpoints.lean` exports ten audited endpoints.
- `SOURCE-MANIFEST.json` binds the 24 new local modules and their import order.
- `BUILD-EVENTS.jsonl` records all 24 clean exits, source/object hashes and timings.
- `BUILD-ACCEPTANCE.json` records the compiler and full endpoint transitive axiom output.
- Only `propext`, `Classical.choice`, and `Quot.sound` occur. No `sorry`, `admit`, source axiom or `native_decide` appears in the selected source closure.
- `INHERITED-FINITE-RECEIPT.json` binds the already accepted finite packet. Its 1,211 source/object pairs were checked **read-only**; none was modified or rebuilt by this task.

Existing pinned Lean/Mathlib dependency objects were reused. This is ordinary Lean kernel/import trust, not an independently rebuilt compiler or all-Mathlib audit. Internal review is not external expert verification.

## Remaining original-theorem gates

1. Derive the required outer contour and adjacent-copy order from the **actual** faithful continuous raw-network drawing, preserving original outer-label incidence and parallel-edge bigons.
2. Supply the actual graph-to-ordered-tree syntax/witness identification. This packet's syntax decoration bridge is not a proof that a raw multigraph has the required contour.
3. Finish original marked-galled admission, where still missing, and compose the actual source local score, capped-blob/global metric identity, circular split reconstruction, and exact global displayed-split support.

The faithful source-to-supplier drawing candidate remains separately pending the sole cloud compiler. This packet does not qualify that candidate or import the third-party geometry supplier. The original-network/full-Theorem-A/Zenodo gate remains open.

## Portable replay

`python3 replay.py FINITE_OBJECT_ROOT LEAN_BINARY NEW_OUTPUT DEP_OLEAN_DIR...` checks the pinned compiler, both source manifests and all inherited source/object receipt hashes before building only these 24 modules in a new output directory. Supply already accepted inherited objects and cached dependency directories. The inherited public source archive alone does not contain those objects. No downloads, installations or inherited rebuilds are performed. Lean is 4.33.1; Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`. The replay wrapper was syntax-checked; the recorded acceptance is the completed isolated clean build, not a second wrapper run.
