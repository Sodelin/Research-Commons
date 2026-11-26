# Alexander §6 follow-on: observation-fibre certificates

This route asks what can be transferred to finite observation solvers, not what changes the answer to an infinite universality question. It imports the actual round-one embedding theorem, not a replacement mock.

## Checked interface

[ObservationGridBridge.lean](ObservationGridBridge.lean), `no_candidate_of_grid_lift`, is a generic negative-certificate consumer. Fix one host with an established forbidden grid. For **each** candidate satisfying admission and matching the observations, certify (1) that the candidate graph contains the grid and (2) that its graph injects into that host preserving undirected adjacency. Transport the grid along that map and contradict the host bound. The premises must cover the entire matching fibre, not only a representative, and the same actual host must satisfy the bound. This is a kernel-checked implication, not a proof that the premises hold in G3, G4, G5, or NANUQ.

Two checked controls:
- [FiniteVersusInfinite.lean](FiniteVersusInfinite.lean): unbounded disjoint finite chains and one ray realize the same prefixes at every length, but only the ray realizes the infinite word. The starting point may vary with prefix length, so this does not contradict the usual finitely branching tree theorem with a fixed start (or a finite covering set of starts).
- [ObservationEmbeddingControl.lean](ObservationEmbeddingControl.lean): a ray and that ray padded by a disjoint directed three-star have the same entire infinite-word language; only the plain ray embeds into the ray host. These are pure abstract graph controls. Neither padding fixture is asserted to be an admitted balanced population or a biological-solver input.

## What existing code really preserves

| Pinned code | What it gives | What would still be needed |
|---|---|---|
| [NANUQ capped quartet readout](https://github.com/Sodelin/Research-Commons/blob/4e8ea9f05a9716ccdabf2b2197e8699ad6e4bf4f/research/2026-10-05-dot-nanuq-actual-curve-geometry-0806z/package/guards/NanuqActualCappedQuartetReadout.lean), `Nanuq.Source.RootedBinary.Switching.capped_oriented_quartet_iff_original` | Transports an oriented finite quartet at a selected original internal blob edge across the capped projection. | A full-graph injective map and a forced grid in **every** matching source. The finite quartet iff supplies neither. |
| [G4 finite equations](https://github.com/Sodelin/Research-Commons/blob/73c84c99f46e7a977f99efefde174871d2d4f7f8/packages/research/lean/ResearchCommons/G4/AlgebraicProfile.lean), `ResearchCommons.G4.AlgebraicProfile.finite_response_equations` ([scope receipt](https://github.com/Sodelin/Research-Commons/blob/8940f035a0bbf2f7855a8247517fc3033ab59c7c/packages/research/integration/g4-algebraic-profile-component-verification.json)) | Selects finitely many original equations in a fixed finite polynomial context. | An actual global bound or an all-source argument; finiteness of the equations does not bound hidden rival network size. |
| [G5 timed three-panel source](https://github.com/Sodelin/Research-Commons/blob/81ff60aa0ffe6c39e15546b09105f3c3fafbd1ed/research/2026-10-10-dot-g5-full-binary-m3-0209z/sources/G5M3NormalizedClusterSplitIdentification.lean), `GProgram.G5.M3NormalizedClusterSplitIdentification.m3_identifies_documented_full_cluster_split_unions` ([package receipt](https://github.com/Sodelin/Research-Commons/blob/81ff60aa0ffe6c39e15546b09105f3c3fafbd1ed/research/2026-10-10-dot-g5-full-binary-m3-0209z/README.md)) | Full timed panel laws identify documented unions in scope. | Recovering joint co-occurrence or whole-graph incidence, which does not follow from union equality. |

The reusable part is a **typed all-candidate certificate**, not a reduction of phylogenetic inference to Alexander's theorem. Next test: start with one existing fixed-size, exact quartet fixture and ask whether its claimed graph property is actually forced. If not, save two admitted matching graphs with distinct property values. If so, port that forced invariant before generalizing beyond the fixture. Do not infer an infinite path or exact source graph from projection equality.
