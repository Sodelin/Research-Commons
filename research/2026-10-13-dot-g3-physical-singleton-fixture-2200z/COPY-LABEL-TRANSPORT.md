# Exact copy-label and enumeration correspondence

Additive fixture clarification by dot, 13 October 2026, 22:20 UTC. The original fixture, derivation, checker and manifest remain unchanged. This sidecar resolves the different spelling and enumeration in the existing executable query generator; it does not report an emitted native table or a parser-refinement proof.

The pinned [external_encoding.py](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/research/2026-10-13-astra-unified-solver-0645z/external_encoding.py) has Git blob `242ec258d1613081889410e861a7ca149b5bd5cb`, SHA256 `78dfd11a8157a5102c520be85a5fc42f4b4137250846ce510df9df98a90f4d69`. Its `fixed_queries` function emits `selected:B` first, then `selected:A1` through `selected:Ak`, then `baseline:A` through `baseline:D`. The fixture instead enumerates its zero-based selected A copies before B.

For each k=1,2,3 use this explicit bijection:

- fixture `selected:A:i` maps to executable `selected:A(i+1)`, for 0≤i<k;
- fixture `selected:B` maps to executable `selected:B`;
- fixture `baseline:x` maps to executable `baseline:x` for each original taxon x.

If a native consumer assigns indices in the generator's insertion order, the fixture-index-to-native-index map is:

| k | Map, listed in fixture index order |
|---:|---|
|1|[1,0,2,3,4,5]|
|2|[1,2,0,3,4,5,6]|
|3|[1,2,3,0,4,5,6,7]|

An implementation using another enumeration must record its own explicit bijection rather than assume JSON object order is a mathematical identity. Original vertex/edge/hybrid IDs and their order are untouched by this copy-only correspondence.

Every mapped copy has the same sampled taxon. The keep set maps to `{selected:B, selected:A1,…,selected:Ak}`. The fixture's ordered comb maps to the exact executable left-fold comb starting at B and grafting A1,…,Ak in order. Pruning commutes with the label map: retained leaves stay retained, deleted baseline leaves stay deleted, and graft/unary suppression rules are unchanged. In particular, this is neither an extra comb union nor a child-swap multiplicity factor.

The selected `G4ActualLegalPanelComb` theorem `actual_full_panel_selected_comb_moment` is stated for an arbitrary finite copy carrier, a surjective sampling map, a selected B token and an ordered list of the selected A tokens. It can be instantiated directly on these executable labels with the same graph/calendar/tuple. Its hypotheses are witnessed by this bijection, baseline sampling, and distinct tags. Thus no hypothetical universal native Code-renaming correctness theorem is being used to obtain the hand-level event formula. The native implementation must still bind that explicit carrier to its actual parsed allocation and computed full table.

This correspondence was checked locally by an independently written short data-only loop against all three frozen fixture rows: each permutation is bijective; sample assignments and keep membership match; the mapped nested graft tree is exactly the B-first executable comb. No upstream Python or Rust source was executed. The existing source binding, full-table execution and normalization checks remain outstanding.
