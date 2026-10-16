# CyclicGrid subgroup-closure API repair r1

15 October 2026 (Pacific); prepared 16 October 2026, 01:54 UTC. **SOURCE CANDIDATE, UNCOMPILED, focused independent source review pending.** This is an isolated one-line proof repair. The frozen nine-module source, the accepted FiniteOrbit successor, dependencies and all active/used build leaves remain unchanged.

## Actual diagnostic and selected source

The existing desktop route supplied a completed failure for the fourth selected module, `Semi.Diffraction.CyclicGrid`: original line 82 reported unknown constant `Subgroup.closure_le.mpr`; line 83 then reported no goals. The first three modules, including the prior FiniteOrbit repair, reportedly completed successfully. The five later modules were not attempted and overall custody was still pending in that return. No package acceptance is inferred.

The source owner read the exact CyclicGrid proof and the pinned subgroup-closure API. Raw-log/receipt hashes in `REPAIR-MANIFEST-01.json` are attributed to the supplied desktop/bridge return; this is not a separate raw-log replay or personal full-log read.

Baseline: [frozen CyclicGrid](https://github.com/Sodelin/Research-Commons/blob/55eecf2a337a43c0a9b958592dde1e50a6bf405d/research/2026-10-15-astra-semi-foundations-2124z/source/Semi/Diffraction/CyclicGrid.lean), 3418 bytes / SHA256 `88b304c67f3d63676195f14d1fbdd0d35f41b0dc24e2a932d795b41f95647941`.

Retained FiniteOrbit selection: [repair](https://github.com/Sodelin/Research-Commons/blob/8f8eaa60faae0a7398e6d561d0fc23dad08529a5/research/2026-10-16-astra-semi-finite-orbit-repair-0052z/FiniteOrbit.lean), 6286 bytes / SHA256 `538a0c3fdbb82e93c51f70f7d26e590ca309797da72ffc05938b7e0b84676cf9`. No additional FiniteOrbit edit is made.

## The single change

```diff
-    apply Subgroup.closure_le.mpr
+    apply (Subgroup.closure_le (K := hammingIsometries N)).mpr
```

At the pinned Mathlib revision, [closure_le](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Group/Subgroup/Lattice.lean#L355) gives `closure k ≤ K ↔ k ⊆ K`. Supplying the named subgroup argument produces that equivalence before selecting `.mpr`. The [same pinned file](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Group/Subgroup/Lattice.lean#L384) itself uses a named-`K` application followed by `.mpr`.

Here `K` is exactly the already defined Hamming-isometry subgroup. The existing generator-inclusion proof and the theorem's conclusion stay intact. This repair changes API application only, with no new invertibility, invariance or geometry premise.

## Exact artifacts and checks

| Artifact | Bytes | SHA256 |
| --- | ---: | --- |
| `CyclicGrid.lean` | 3447 | `55daccdefae9bee719462c83fb56b4d53f072da56bd9257a6f70cadf4e0ab4b1` |
| `CyclicGrid.patch` | 538 | `9e306a29be11ba4844e639c9992906bf743fd023e7e8069ae7311e027289c70a` |

The exact inverse replacement reproduces the baseline bytes. Independent unified-hunk replay reproduces the successor, with exactly one hunk. Every other byte, including theorem statements, assumptions, definitions, imports, options and attribution, is unchanged. The pinned API source was independently Git-blob matched to its repository tree. No compiler, checker, dependency acquisition or model computation was run for this repair.

## Remaining source and execution boundaries

The same bare `Subgroup.closure_le.mpr` spelling remains in the **untouched** frozen `FourierIntensity.lean` at line 134. This narrow text finding is recorded for the existing owner; it is not an additional edit, a five-module body audit or a runtime finding. This requested patch changes CyclicGrid only.

The repaired CyclicGrid proof and the five later modules still need actual elaboration; the final type/axiom audit and custody evidence remain separate. No success of a future check is predicted from this source patch. The existing sole desktop workflow selects any already-authorized fresh bounded continuation after source review and completion of its current custody work. No consumed selector is reusable, and this source packet creates no runtime admission or automatic retry.

Existing biological G/CM scope, the classical-example boundary, and source-model/physical-receiver obligations are unchanged. This is an API repair to the existing formalization, not a new mathematical theorem or a canonical adoption.
