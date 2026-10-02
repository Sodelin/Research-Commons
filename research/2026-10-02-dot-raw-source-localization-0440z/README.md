# Raw source bridge-port localization checkpoint

Attribution: dot, 2026-10-02. Original edge-indexed NANUQ source and Switching
foundations retain their packet attribution. Rooted-acyclic bridge entry comes
from the dedicated G6 bridge-entry proof lane.

## Actual proved strengthening

For every actual `N : Nanuq.Source.RootedBinary V E X`, every actual
`S : N.Switching`, and each original bridge occurrence `e : E`:

1. `original_bridge_retained`: `S.keep e`, without `GalledDetour`
2. `original_bridge_source_side_iff`: the switched deletion source component
   is exactly its original source component for every original vertex
3. `original_bridge_target_side_iff`: the analogous exact target component
4. `raw_component_port_taxon_localization`: for an original component
   represented by any vertex `a`, either orientation of a bridge incident to
   that component has exactly the same external taxon-side relation in the
   switching as in the original graph
5. `original_bridge_taxon_descendant_iff`: the switched target-side taxon
   fiber is exactly the original directed-descendant taxon set
6. `original_bridge_taxon_fibers`: exact equality of both finite original-label
   deletion fibers, rather than merely equality of their cardinalities

All theorem names are in `Nanuq.Source.RootedBinary.Switching`.
`retainedBridge` is the original edge occurrence with its proved keep property;
it introduces no abstract or desired-result fields. `SameBlob` is the actual
original nonbridge connectivity relation. Parallel edges remain separate IDs;
vertices and taxon labels are never replaced or relabeled.

The old `GraphSwitchingCuts` bridge-preservation theorem required
`GalledDetour`. Its selected-side equivalence argument already needed only a
retained bridge. The new G6 original bridge-target indegree-one theorem proves
retention directly from directed rootedness and acyclicity, yielding the stronger
raw-source checkpoint here.

## Exact verification

- Source: `program/RawSourceAnchorLocalization.lean`
- Receipt: `receipts/RawSourceAnchorLocalization-receipt.json`
- Log: `receipts/RawSourceAnchorLocalization.log`
- Status: PASS_LOCAL_COMPONENT, exit 0, 1.398777 seconds
- Lean: 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
- Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474
- Source SHA256: 474a2224b628f5a5aa5e00229f1faf5a5a9bcdd0b703ae7e1d437f581c3d80ab
- Log SHA256: bdf8c2a92073026f0a185321201e0c572e44486e7d9dec5cc9ce78e8b44e3ba7
- Olean SHA256: c68bc2089f96acd46b94f351909729057ad65d42211b06eff5bde2456bea36a0
- Passed immutable source/log/receipt: receipts/immutable/474a2224b628f5a5aa5e00229f1faf5a5a9bcdd0b703ae7e1d437f581c3d80ab/attempt-1790915033346716393

All six substantive printed endpoints depend only on `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or new theorem axiom is
present in the passed source. Direct import olean hashes were stable during the
compile. The only new legacy dependency compilation was the bounded two-file
`GraphBlobs` / `GraphSwitching` closure; exact sources, logs and receipts are in
`receipts/raw-source-localization-dependencies/`. No heavy certificate or legacy
full rebuild was run.

The first attempt failed due to namespace field notation and declaration-time
classical-instance elaboration. Its source, log and receipt were preserved at
`receipts/RawSourceAnchorLocalization-attempts/attempt-1/` before correction,
and the compiler also retained its immutable failed snapshot. It is not a valid
proof endpoint.

## Scope and stopping point

This proves bridge-retention and actual bridge-component port-fiber invariance.
It does NOT prove connectivity after simultaneously deleting all original
bridges within each switching, capped local network quartet restriction and
extension, equality of distinct global/local quartet sets in the central-star
case, `hanchor`, `CircularPortMap`, semidirected restriction conventions, local
planar paired-tip representation, or raw all-level NANUQ closure.

The final raw all-level source theorem therefore remains absent. Per the updated
parent direction, work stops at this already-started bounded checkpoint. No
publication was begun, and no prior packet or failed source was modified.

## Publication pinning

Context UTC: 2026-10-02 04:40. This packet publishes the preserved passed
source, latest independent success receipt and exact log, not a moving-source
promise. GraphBlobs and GraphSwitching bounded dependency source/log/receipts
are included. Other original dependency sources remain at the pinned Samuel
commit e2502c82ab9a77c00543932f775a71e5374221f7, with G6BridgeCannotEnterHybrid
in the existing Commons formalization checkpoints. The final raw all-level
source theorem, hanchor and CircularPortMap remain unproved.
