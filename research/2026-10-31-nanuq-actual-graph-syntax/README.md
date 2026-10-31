# Actual graph → binary syntax → exact quartet cuts

Author: dot. 2026-10-31. **Accepted scoped component, not full NANUQ.**

## What is proved

For the unchanged original `Nanuq.Source.EdgeGraph`, assume finite vertices/edges, directed acyclicity, injectivity of the original target map (unique incoming edge), outdegree zero or two, and a root reaching every vertex. `actual_graph_syntax_provider` constructs ONE annotated binary syntax, proves every original vertex occurs exactly once, and proves the ORIGINAL `SourceQuartetRelation.HasQuartet` iff its subtree-cut predicate for ALL four queried vertices simultaneously.

The source and target components of deleting each original edge ID are exactly the complement and descendant-subtree node set. Conversely every proper syntax subtree cut comes from an actual original edge. The bridge guard in HasQuartet is derived, not dropped. Edges are not quotiented by endpoints. Acyclicity plus finiteness derives well-founded unfolding; neither syntax existence nor cut correspondence is an input certificate.

`edge_frontier_partition` gives the same exact cut statements at actual terminal occurrences. `frontier_iff_reachable_sink` says the syntax tips are exactly reachable vertices of outdegree zero. No taxon-label injectivity premise is introduced: these are occurrence-vertex statements, to be composed later with the actual label map.

## Actual-source binding and remaining joins

Six inherited source modules are copied byte-for-byte from Commons PR head `14be42189b8a72fcaced51ceda4e86445dc09e90`. In particular SourceNetwork is pinned `0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7`; SourceQuartetRelation is pinned `defffabb0a8147a0c857889d3c6be386f79399b6c0e4b45b6aa22dff7794a91e`.

Existing NanuqActualOpenedHybridTree/OpenedBinaryDegrees/OpenedRootedAdmission already derive the graph premises for the literal opened cap. `candidates/NanuqOpenedGraphSyntax.lean` is an **uncompiled** application to those exact APIs, retaining their child-is-taxon interface. The generic theorem is accepted; that named application is not yet qualified. No new raw network assumption is silently substituted for source admission.

Crucially the chosen child order is arbitrary. This theorem does NOT derive the geometric contour order, adjacent duplicate taxa, or compatibility with an externally required cyclic order. It also does not yet erase/relabel this syntax into the frozen adjacent-mask finite receiver. That composition needs exact occurrence-label/order compatibility. The raw-network contour/gall-admission and global NANUQ composition/support gates remain OPEN. No whole-Theorem-A or Zenodo acceptance follows.

## Verification

15 modules accepted (9 new, 6 unchanged retained source); pinned Lean 4.33.1 and existing Mathlib objects. Exact clean-source events bind every source/object hash. All printed transitive axioms are among propext, Classical.choice and Quot.sound; no sorry/admit/native_decide/source axiom. No inherited 1,211-module finite packet was modified or rebuilt; no external geometry code or duplicate cloud build was executed.

Earlier working SourceNetwork differed from the pin by one trailing blank line. That copy and its preliminary receipts are retained, but the selected exact-source replay uses the byte-exact pin. Exploratory failures fixed a minimal-import missing Fintype→Finite instance, DReach unfolding/coercion elaboration and list nodup/frontier proof obligations. Failed logs are not acceptance evidence. The final frontier module was checked against the completed exact 14-module closure and added as module15; no claim that a second whole closure rebuild occurred.

Prior-work check used the existing discovery query CLI and current PR source manifest/bodies. Dated CLI corpus337 is explicitly not complete history. This result constructs the missing syntactic witness provider rather than reasserting existing opened-tree admission. Novelty beyond this formal completion is not claimed.

## Replay

`python3 replay.py LEAN_BINARY NEW_OUTPUT DEP_OLEAN_DIR...` validates compiler and all source pins before a clean 15-module replay using supplied cached dependencies. Candidate specialization is intentionally excluded. Wrapper syntax checked; original acceptance is from the recorded exact-source build, not a second wrapper run.
