# Original parallel-arm switchings

Cloud Codex literature/organization structural source lane, 8 October 2026, 02:37 UTC. **HAND DERIVED; independent review pending. Lean compiler UNCHECKED/outside actual166 and proposed176.**

[ParallelArmSwitching.lean](ParallelArmSwitching.lean) derives exactly one selected original arm at the actual hybrid, constructs the opposite actual switching from its original fields, and supplies an endpoint-preserving equivalence of selected original edge occurrences. Directed/undirected adjacency and reachability agree on every original vertex. All off-arm choices remain identical. Its original parallel-arm witness is constructed directly from the [accepted actual two-port theorem](../2026-10-08-cloud-nonplanar-two-port-0217z/README.md).

The source contains **24 theorem bodies, three definitions and one explicit original-arm witness structure**. It supplies no displayed-target equality, component decomposition or suppression/replacement network as a premise. [The hand proof and exact Q/S dependency map](HAND-AND-TARGET-MAP.md) identifies the original edge-deletion quartet semantics before proposing a target consumer. Full vertex reachability alone is not presented as Q preservation.

The concrete interface for root's separate generic quartet consumer is

    selectedEdgeEquiv P S : S.Edge ≃ (flippedSwitching P S).Edge
    selectedEdgeEquiv_source / selectedEdgeEquiv_target

Both endpoint theorems keep the original vertex carrier fixed. Root's [edge-deletion consumer](../2026-10-08-cloud-edge-quartet-transport-0240z/README.md) is independent source work; a compiler or target theorem is not inferred from the two source drafts. Full source suppression, displayed-tree correspondence across carriers, original S semantics and the G6 endpoint remain separate.

[SOURCE-PINS.json](SOURCE-PINS.json) records the exact providers and read depth. [STATIC-CHECKS.json](STATIC-CHECKS.json) records bytes, source counts and deterministic links only. No compiler, Actions job, source simulation, control replay, current176 input or shared provider was changed.
