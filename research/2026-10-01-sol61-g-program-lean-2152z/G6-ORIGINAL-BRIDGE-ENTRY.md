# G6 original bridge-entry and distinct-port graph fact

Dedicated Sol6.1 Lean contribution, 2026-10-02. Samuel's original edge-indexed
source definitions and foundational proofs retain their exact baseline and
attribution. This verifies the graph obligation requested by the current
nonplanar source review. It does not formalize that review's whole kernel or
finite-certification theorem.

[Lean source](program/G6BridgeCannotEnterHybrid.lean),
[exact theorem signatures/axioms](receipts/VerifiedBridgeEntry.log),
[successful hash/compiler/resource receipt](receipts/G6BridgeCannotEnterHybrid-receipt.json).

## Minimal verified interface

For an EdgeGraph G, assume only directed acyclicity and directed reachability
from one root to every vertex. If original edge e is an underlying bridge,
Lean proves that every edge f with target(f)=target(e) must be e itself.

The second incoming edge, if distinct, remains present after deleting e. Its
source is therefore connected to the downstream target component of e. The
already compiled bridge/descendant theorem makes it a directed descendant of
target(e); traversing f back into that target creates a directed cycle.

This proves uniqueness of incoming edge OCCURRENCES, not merely parent
vertices. Distinct parallel edges with the same source/target cannot individually
be bridges. The generic uniqueness theorem needs no finite vertex or edge
bound, binary degrees, LSA, child-cut, galledness or planar embedding.

With finite original edge IDs and decidable vertex equality, the target's actual
indegree is exactly1. Hence an actual RootedBinary hybrid, whose indegree is2,
cannot be entered by a bridge. Both original parent edges of the compiled G2
OriginalHybridParents record are nonbridges.

Lean also proves the downstream target map on original bridge edge occurrences
is injective. This supplies the distinct child-cut target/port consequence;
the child-cut premise itself remains separately supplied when those children
are designated bridges.

## Actual receipt and theory boundary

The final source compiles in1.185249 seconds, one thread, 2 GiB cap,
peak child RSS1,675,804 KiB (1.60 GiB), exit0. Source SHA256:
`60befd0f3660e56b46ca80f17a0c11f8ecd415833d0d52fad5ecafef7df6389e`.
All six printed proof dependency lists contain exactly propext, Classical.choice
and Quot.sound; no custom unproved axiom or placeholder is used.

This structural fact supports source-faithful nonplanar reductions. The
all-size decorated-core bounds, contextual forest/register kernel replacement,
source realizability, finite-copy certification and stochastic observation
transfer still require their separate complete source proofs. No compressed
original-ID actuator catalogue or whole G6 completion is inferred from it.
