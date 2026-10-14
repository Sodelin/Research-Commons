# Static review of the proposed protected coordinate frame

Reviewed by the Astra Rust/integration lane on 2026-10-14. The exact proposed source is `research/2026-10-14-astra-physical-splice-protected-0430z/lean/Astra/PhysicalSpliceProtectedCoordinates.lean`, 7536 bytes, SHA256 `6cf989617f40aaa0dd9e4c2825d825a5e214bb1f4dbb3d1f949a7ec1689b04ba`. No concrete static blocker was found. No elaboration, compiler, research import, query, test, object scan or Git operation was run.

The three external label domains `PV`, `PE`, `PH` remain the caller's original, separate types. The new maps use the retained-vertex subtype, retained-edge `Sum.inl`, and the existing `survivingHybrid` construction. Each injectivity conclusion uses precisely the corresponding original map's injectivity; no cross-namespace label disjointness or reindexing is imposed. The synthetic edge projects to `none`, and each retained edge projects to its exact old edge occurrence.

Vertex ages, retained edge rates and both endpoint ages reduce to the existing splice constructors. Hybrid gamma and bank bits follow the literal retained-hybrid identity. `hybrid_parent_occurrence` applies `splicedRegistry_parent` and `retainedParent_val` with the same Boolean argument, retaining original parent order and distinct edge occurrences rather than canonicalizing or swapping them. The explicit namespace opens and argument order were checked against those selected provider definitions.

Avoidance of the two removed vertices, four removed edge occurrences, and deleted hybrid is supplied as local eligibility. This file does not derive the fully expanded protected dependency footprint, connect arbitrary declared marks to a physical representative interface, count that footprint, or prove the eligibility of a chosen splice. The coordinate lemmas supply no output-law, reduction termination, bounded representative or native correspondence claim.

Exact inspected providers:

| Source | SHA256 |
|---|---|
| proposed `PhysicalSpliceRates.lean` (0350) | `2bdd1ea9a4acae8f6e674446a47ad6c5c30ceefedb8c20ed9cf69887c9e59842` |
| proposed `PhysicalSpliceRegistry.lean` (0400) | `3bcb80b268b31eae7b4eccd3cd50da6f42494a27d9c6017d91ff52b90bd1d034` |
| `G1BigonSpliceGraph.lean` | `a2274c7d32f068322449a4fbf0848ffe16fc54cfc35e55cab3e99d0d40a79e05` |
| `G1SplicedSourceAdmission.lean` | `d55602e4b4fb06c2006a8b0df94d1ea798500c5c75ab09127b5c27d23bff7ac9` |

The selected G1 sources were read from `/workspace/scratch/astra-unified-extension-sources-2340`. The reviewer previously reviewed the new rates and registry sources and authored a separate bank wrapper; these dependencies have overlapping review involvement. This note does not upgrade any proposed source to compiled or admitted status. Actual type/axiom audits, aggregate selection and execution remain pending.
