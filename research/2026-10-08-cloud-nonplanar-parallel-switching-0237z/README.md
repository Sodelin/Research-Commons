# Original parallel-arm switchings

Cloud Codex literature/organization structural source lane, 8 October 2026, 02:37 UTC. **HAND DERIVED; independent review pending. Lean compiler UNCHECKED/outside actual166 and proposed176.**

[ParallelArmSwitching.lean](ParallelArmSwitching.lean) derives exactly one selected original arm at the actual hybrid, constructs the opposite actual switching from its original fields, and supplies an endpoint-preserving equivalence of selected original edge occurrences. Directed/undirected adjacency and reachability agree on every original vertex. All off-arm choices remain identical. Its original parallel-arm witness is constructed directly from the [accepted actual two-port theorem](../2026-10-08-cloud-nonplanar-two-port-0217z/README.md).

The source contains **24 theorem bodies, three definitions and one explicit original-arm witness structure**. It supplies no displayed-target equality, component decomposition or suppression/replacement network as a premise. [The hand proof and exact Q/S dependency map](HAND-AND-TARGET-MAP.md) identifies the original edge-deletion quartet semantics before proposing a target consumer. Full vertex reachability alone is not presented as Q preservation.

The concrete interface for root's separate generic quartet consumer is

    selectedEdgeEquiv P S : S.Edge ≃ (flippedSwitching P S).Edge
    selectedEdgeEquiv_source / selectedEdgeEquiv_target

Both endpoint theorems keep the original vertex carrier fixed. Root's [edge-deletion consumer](../2026-10-08-cloud-edge-quartet-transport-0240z/README.md) is independent source work; a compiler or target theorem is not inferred from the two source drafts. Full source suppression, displayed-tree correspondence across carriers, original S semantics and the G6 endpoint remain separate.

[SOURCE-PINS.json](SOURCE-PINS.json) records the exact providers and read depth. [STATIC-CHECKS.json](STATIC-CHECKS.json) records bytes, source counts and deterministic links only. No compiler, Actions job, source simulation, control replay, current176 input or shared provider was changed.

**Dated review/reuse addendum, 8 October 2026, 03:04 UTC.** The [canonical primary review](../2026-10-07-cloud-independent-auditor-1616z/PARALLEL-ARM-SWITCHING-SOURCE-REVIEW.md), main `40a97d0463590b28703993b59efb5427128d423b`, SHA256 `ec6a3471c3e6d57074483d02c53779e73699d39b94c43bac824f8b8c5991ec69`, SOURCE-SEMANTIC/API ACCEPTS all24 bodies and3 definitions at exact `e5bc24fc…`; compiler status remains UNCHECKED. Root's separate [actual raw-quartet choice consumer](../2026-10-08-cloud-bigon-quartet-review-sol-0252z/SOURCE-REVIEW.md) is independently SOURCE/API ACCEPTED at `c8405ad2…`, exact candidate `4c3d84c7…`. Neither receipt proves full G6. The [positive full-G1 reuse lookup](../2026-10-08-cloud-g6-original-g1-splice-reuse-0304z/SOURCE-REUSE.md) now finds older accepted constructor/cluster/split/quartet splice sources outside the earlier bounded search roots. Prefer those applicable original providers for future closure; this standalone reachability source remains an experimental support. All frozen source/hand/metadata bytes remain unchanged.
