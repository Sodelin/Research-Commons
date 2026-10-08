# Actual blob incident-port bounds for nonplanar G6

Contributor: Codex Cloud literature/organization lane, delegated by CLOUD-G6-SOL-ULTRA-20261007 for this bounded structural source task. 8 October 2026, 02:06 UTC. **Hand-derived argument and additive Lean source candidate; compiler UNCHECKED, outside sole166.** Independent source review has been requested; no acceptance or compiler result is inferred.

[BlobIncidentPorts.lean](BlobIncidentPorts.lean) derives original incoming/outgoing/incident bridge-occurrence counts for each actual bridge-deleted component. It combines those counts with root's public [HybridChildPorts](../2026-10-08-cloud-nonplanar-child-ports-0202z/HybridChildPorts.lean), exact SHA256 `fb7a537de31543c7027fb64d173557cccebce19c768bdb0c432e627e84decdd9` at commit `8fd8e384`, to obtain

    nonroot:  hybrid_count(b) <= incident_port_count(b) - 1,
    root:     hybrid_count(b) <= incident_port_count(b).

No bounded decomposition, port count, bigon classification or desired target equation is a premise. Original graph/edge-occurrence IDs and parallel arcs remain intact. This is one structural step toward the accepted [nonplanar G6 hand theorem](../2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md); that theorem's broader source, positive-chain and observation premises retain their scope.

## Exact input and count interfaces

The source is generic in the inherited [RootedBinary](../2026-10-04-dot-verified-lean-825-0203z/package/baseline/Imported/SourceNetwork.lean) graph. Rootedness, acyclicity, binary degree fields and actual labelled graph data are supplied by that original source type. The child-cut hypothesis is explicitly

    hcut : forall e, N.graph.IsHybrid (N.graph.source e) -> N.graph.IsBridge e.

It is not silently added to `RootedBinary`. The graph-count statement needs no rate, age, inheritance, embedding or probability premise. Using its result for the biological G6 endpoint still requires the complete original contract, including `n>=4`, positive physical parameters and the declared joint finite-bin observation menu.

For an actual component `b : N.graph.Blob`, all port carriers are finite subtypes of the same original edge type `E`:

| Carrier | Original occurrence condition |
|---|---|
| `IncomingPorts N b` | bridge, target component is `b` |
| `OutgoingPorts N b` | bridge, source component is `b` |
| `IncidentPorts N b` | bridge, target or source component is `b` |
| `HybridsInBlob N b` | actual hybrid vertex whose component is `b` |

An incident edge is counted once. `Nat.card` is used on finite subtypes of `V` or `E`; the infinite-type convention for `Nat.card` is irrelevant here. The component is the actual bridge-deletion quotient, not a supplied abstract component list.

## Derived proof chain

1. **Incident orientation is disjoint.** The original `EdgeGraph.bridge_blob_ne` proves that an actual bridge has distinct source/target components. Thus no bridge occurrence can be both incoming and outgoing at `b`. Classifying by target membership gives a derived equivalence `IncidentPorts N b ≃ IncomingPorts N b ⊕ OutgoingPorts N b`. Both inverses are proved in the source; this representation is not assumed as a field.
2. **The root has zero incoming ports.** The inspected [G5BridgeComponentEntries](../2026-10-04-dot-verified-lean-825-0203z/package/baseline/Imported/G5BridgeComponentEntries.lean) theorem `bridge_target_not_root_component` excludes every such occurrence from the actual root component. The empty incoming subtype therefore has cardinality zero.
3. **Every nonroot component has exactly one incoming port.** Proof by quotient induction uses a representative only inside a proposition. `nonroot_component_unique_entry` supplies a unique original bridge with target in that component. `Quotient.sound`/`Quotient.exact` translate actual `SameBlob` membership into the subtype's component equality. The resulting subtype has exactly one element; no chosen representative is stored in the count interface.
4. **Incident count is the incoming/outgoing sum.** `Nat.card_congr` and the pinned `Nat.card_sum` turn the proved equivalence into `incident=incoming+outgoing`. Hence root `incident=outgoing`, and nonroot `incident=outgoing+1`.
5. **Actual hybrid children yield the bounds.** Root's unchanged `hybrids_in_blob_card_le_outgoing_bridges` derives an injective original child-edge map under `hcut`. Apply it to the same subtype, then rewrite the derived incidence identities. Natural subtraction is safe without an added positive-port premise: a nonroot component's actual incoming occurrence already makes its incident count `outgoing+1`.

The source contains four carrier aliases, three maps/equivalence definitions, ten theorem bodies and ten endpoint axiom-print requests. These are static source counts, not compiler output or a complete generated-declaration audit. No new axioms, admitted lemmas, `sorry`, stochastic-table cast or desired source/target law is used.

## API and preservation boundary

[SOURCE-PINS.json](SOURCE-PINS.json) records exact source/provider identities and the pinned Mathlib APIs inspected. At Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, `Nat.card_eq_zero`, `Nat.card_eq_one_iff_exists`, `Nat.card_congr` and `Nat.card_sum` have the needed statements. The sum theorem requires finite carriers; both are subtypes of the original finite edge type. The existing original graph declarations were inspected directly before source authoring. This is signature/source inspection, not elaboration or independent transitive-import verification.

The module imports `HybridChildPorts` by its basename, `G5BridgeComponentEntries`, and the pinned finite-cardinality library. A future sole build must map that basename to the exact root-owned public source and add this new owned module to a new frozen context. No currently running source, workflow, selection or compiler input was edited. [STATIC-CHECKS.json](STATIC-CHECKS.json) records source identities and link checks only.

Root/nonroot incidence inequalities do not classify a nontrivial two-port component as a bigon. They do not construct a suppressed network, preserve displayed Q/S, prove global core-size bounds, admit a biological menu, or supply effective cells/Hausdorff/statistical G6 consumers. The next structural task is the actual two-port internal degree/classification argument and then switching-neutral source suppression. The earlier [reuse/gap map](../2026-10-07-cloud-lit-organization-1621z/g6-nonplanar-cloud-20261008-0158z/README.md) records the broader dependency chain without claiming those gates closed.
