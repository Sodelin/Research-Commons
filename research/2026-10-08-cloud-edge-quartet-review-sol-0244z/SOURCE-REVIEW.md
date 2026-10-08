# EdgeOccurrenceQuartetTransport independent source/API review

Reviewer: `/root/source_backend_review_sol`, Cloud Sol team, 2026-10-08. Root authored the source prototype. **SOURCE/API ACCEPT** for immutable candidate `bbd51e0a5062f282aac3d1f32c8c6a818cdf36f7`, file SHA `166137f6b361991a46797ca6377e5788669bbd535aaddc12d5d6c45540b1f402`, 4,116 bytes. No blocking semantic or definite static API defect was found. Compiler elaboration, inferred types and transitive axioms remain UNCHECKED.

All ten theorem bodies, `OccurrenceEquiv`, and the two endpoint proofs in `OccurrenceEquiv.symm` were read. The exact four provider SHA/size/blob identities match frozen `3d944883c04c69989345b3aa6a64c88b49f5c105`, immutable candidate objects and local bytes. Actual definitions were compared in `SourceNetwork`, `SourceQuartetRelation`, `GraphBridgeSplits` and `QuartetSemantics`; relevant relation constructors/proof patterns were read in pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. This is not a new full audit of every transitive historical theorem.

## Primitive graph contract

`OccurrenceEquiv G H` supplies only `E ≃ F` and preservation of source and target vertices for each mapped edge ID, with the vertex carrier fixed. It does not supply reachability, bridge, quartet or output-law equality. It is a genuine directed incidence correspondence, stronger than an arbitrary vertex reachability agreement. It distinguishes all parallel IDs. No finiteness, tree, loop exclusion, planarity, source-clock or probability hypothesis is needed by these generic graph lemmas.

The reverse field proofs apply each forward endpoint equation at `edge.symm f`, reverse its equality, then use `Equiv.apply_symm_apply`. Their direction is correct: the new reverse graph's endpoint at the inverse ID equals the original endpoint at f.

## Every intended theorem and API direction

| Body | Checked implication |
| --- | --- |
| `inc_iff` | Actual `Inc` is the disjunction of the two endpoint orientations of the same edge. Rewriting H's endpoints gives G's exact incidence. Its stated direction is H incidence iff G incidence. |
| `ustep_map` | The witness edge is mapped; `hkeep` transports its keep property, and `inc_iff.mpr` transports G incidence to H. No adjacency quotient is substituted. |
| `ureach_map` | The actual `UReach` is `Relation.ReflTransGen` of those steps. The `refl`/`tail` induction and `.tail` method match the provider's existing `ureach_mono` pattern and pinned relation constructors. |
| `reachWithout_map` | The keep predicates are precisely `f≠e` and `f≠edge e`. Equality of mapped IDs would imply original-ID equality by injectivity, contradicting `hf`. This deletes one occurrence only. |
| `reachWithout_iff` | The forward map and inverse map give both directions. The inverse deletes `edge.symm (edge e)`, reducing to e by `Equiv.symm_apply_apply`. |
| `isBridge_iff` | The actual bridge predicate is negated avoidance reachability between the deleted edge's source and target. Endpoint rewrites and `not_congr` preserve the intended iff orientation. |
| `orientedQuartet_iff` | After endpoint rewrites, the four right-associated conjuncts are exactly source-to-a, source-to-b, target-to-c and target-to-d paths avoiding this edge. Each uses `reachWithout_iff`; the nested `and_congr` matches the actual definition. |
| `hasQuartet_map` | The actual existential bridge witness is mapped, then either its oriented four-path branch or its reversed quartet-side branch is transported. Both branches use the same mapped occurrence. |
| `hasQuartet_iff` | Forward `hasQuartet_map` and the reverse equivalence's same map supply G-to-H and H-to-G with the same four vertices. |
| `resolves_iff` | The actual three-constructor `Resolution` cases reduce to the corresponding `HasQuartet` predicates. The requested iff follows in each case with the original label ordering. |

These are derived graph-target statements. The argument never assumes a target quartet equality. It also never conflates deletion of one parallel ID with deletion of all edges sharing its endpoints. Loops or nonbridges cause no exception to the transport: their actual bridge predicates are still carried by the same path equivalence.

## Source and scientific limits

This module preserves the original raw edge-cut `OrientedQuartet`, `HasQuartet` and `Resolves` predicates on fixed vertices. It does not construct a switching graph, prove a selected-edge equivalence, or supply a resolved quartet for every switching. The structural lane must construct the actual selected-edge bijection and prove both endpoint equations from the original parallel-arm switching data. Supplying merely vertex directed reachability, a desired resolution equality, or a replacement graph with different vertex carrier does not discharge this input contract.

No graph suppression, source replacement, root/LSA/labels admission, cross-network switching correspondence, distinguished S/cluster interpretation, distinct-resolution set/average transport, stochastic or chronological source law, bounded representative or complete RAW NONPLANAR/G6 endpoint is proved here. In particular, `QuartetSemantics` distinguishes the uniform mean over distinct displayed resolutions from the switching average. The present raw-predicate iff alone is not an equality of either whole switching family or either average.

The prototype remains compiler UNCHECKED and outside the active176 input. Reading a familiar Lean proof pattern does not verify its elaboration or inferred axioms. No Lean/compiler, Actions dispatch, numerical/solver control, API/SDK, credentials/private-product work, child agent or provider/workflow mutation was performed. Only source reads, byte/hash/Git identity checks, own review notes and authorized nonforce preservation were performed. The sole compiler owner retains current build/integration control.
