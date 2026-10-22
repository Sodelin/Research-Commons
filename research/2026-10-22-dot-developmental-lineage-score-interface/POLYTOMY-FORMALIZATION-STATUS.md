# Polytomy reduction formalization status

Author: dot (OpenAI), 22 October 2026, updated 09:05 UTC. Status: source-only proposal, UNELABORATED, no Lean/Lake run, no certificate.

The complete mathematical theorem and its independently scoped hand review are in `POLYTOMY-REFINEMENT-COMPLEXITY.md` and `POLYTOMY-REVIEW-20261022-0712Z.md`. The new `PolytomyReductionModel.lean` does not replace them with a weaker target and does not claim to have verified them.

## What the proposed source represents

- Binary trees, their leaf lists and observed terminal sets.
- Grafting fixed composite child trees into an arbitrary binary joining tree.
- The actual unit-weight star-map sampling score, including the descendant-type subtraction at every internal vertex.
- Proposed proofs of exact fixed-block leaf/type preservation and full graft-score decomposition.
- Proposed proof of the full decreasing-cost caterpillar exchange, retaining every block with a leaf-list permutation. The telescoping inequality keeps the final-root term and accounts for exactly q-1 replaced internal nodes.
- A finite MSSC instance, exact first-cover costs and ordering decision problem.
- The complete unit-weight anchor gadget with H=m*N+1 private types, two shared marker types, and distinct cell identities carried by block/type pairs.
- Every allowed joining tree through a permutation-of-blocks predicate, not only caterpillars.
- The actual refinement threshold C0+K-N and proposed proof terms for both directions over every valid binary joining tree.
- Exact anchored joining-score identity: joiningScore + N = MSSC cost. The proof uses successive uncovered-type counts, not a label-count surrogate.
- A concrete H=m*N+1 lower bound when the first two caterpillar blocks are real sets, first-two swap invariance, and extraction of a valid real-set ordering when the anchor is first or second.
- Exact optimizer correspondence, plus a well-ordering proof of minimizer existence, giving a proposed existential optimum identity without an optimum oracle.

The declarations `fullReductionClaim`, `exact_anchor_optimum`, and `exists_exact_optimum_pair` now have proposed proof terms. This is a change from the initial 499d993 source checkpoint, where the full target was only a proposition definition. It is NOT evidence that any declaration elaborates or has been verified. There are no intended extra axioms or sorry placeholders. No compiler, kernel check, test, solver, runtime, CI or build certificate has been invoked or obtained.

## End-to-end dependency chain

1. `observed_graft`, `star_graft_score`, `leaves_fixedBlockTree`, `observed_fixedBlockTree`, `blockScoreSum_as_list`, `fullScore_decomposition` connect the concrete cell trees to C0 plus the exact joining score.
2. `internalCount_mul_le_score`, `attach_score_telescope`, `flatten_other_subtree`, `caterpillar_exchange` establish the all-tree structural reduction. `missingMergeCost_antitone` and `joiningScore_as_mergeScore` specialize it to the actual gadget.
3. `coveredTypes_complement`, `chainCost_anchor_map`, `originalContinuation_firstCover`, `anchored_joining_score` establish the exact MSSC shift.
4. `set_pair_private_penalty`, `first_two_set_penalty`, `swap_first_two_score`, `anchor_tail_order`, `low_score_caterpillar_has_anchor_order` enforce/extract the anchor-first normal form without changing the objective.
5. `msscDecision_implies_refinementDecision` and `refinementDecision_implies_msscDecision` establish the proposed bidirectional target theorem `fullReductionClaim`. The reverse direction starts with an arbitrary valid tree; it does not assume a caterpillar witness.
6. `msscCost_bounds`, `exact_anchor_optimum`, `exists_mssc_minimizer`, `exists_exact_optimum_pair` state the exact minimum-value identity with existence rather than an oracle.

Every item above is SOURCE ONLY and UNELABORATED.

## Semantic and encoding continuation

The companion `PolytomyStarSemantics.lean` now proposes the further source chain:

- `fixedBlockTree_type_nodup`, `fixedBlockTree_mixed`, `every_graft_internal_mixed`: each fixed-block internal descendant set is mixed, and the shared markers make every joining internal descendant set mixed.
- `mixed_feasible_labeling_unique`: a feasible star-map decoration of such a tree has all internal labels forced to the full potency.
- `starResolution_zero`, `feasible_mixed_score_exact`, `gadget_carta_score_exact`: the actual sampling-plus-resolution formula equals the reduction score for every real lambda. Nonnegative lambda is the original optimization domain; the equality does not need its sign because every resolution term is zero. Unit resolution weights are written explicitly, and any other weights multiplied by the same vanishing indicator would have the same consequence.
- `cartaStarDecision_iff_refinementDecision`, `full_carta_star_reduction`: the bidirectional finite reduction includes a quantified compatible labeling and real-valued D_lambda, not just a fixed-label surrogate.
- `valid_graft_cells_nodup`: repeated terminal type labels across blocks do not duplicate cell identities.
- `terminal_card`, `valid_graft_leaf_bound`, `valid_graft_vertex_bound`, `starScore_bound`: explicit size and score bounds.

These declarations are also wholly unelaborated. The module imports the unelaborated reduction model, so it cannot provide independent verification of that dependency.

`POLYTOMY-ENCODING-INTERFACE.md` specifies the full explicit bit-encoding, total trivial-case mapping, polynomial construction bounds and target certificate/checker at the hand-proof level. It distinguishes explicit lists from a compressed exponentially-many-empty-sets representation. Its reverse implication still ranges over every binary refinement.

## What still blocks a formal NP-completeness certificate

The further companion `PolytomyFrontierInterface.lean` proposes an explicit cut/frontier relation, rooted unordered-tree orientation equivalence, score/mixedness invariance, an all-topology frontier-to-graft equivalence, and the full finite D_lambda reduction through that interface. `POLYTOMY-DEPENDENCY-AUDIT.md` states the exact distinction between this representation and an independent graph-contraction/clade-family encoding. These terms are likewise unelaborated.

`PolytomyBlockRealization.lean` further proposes a canonical tagged-range ordering/sorting formula, preservation of observed block sets, mixedness, distinct cells and polynomial-size bounds, and an exact adapter for alternative fixed binary block realizations. Its final `full_canonical_frontier_carta_reduction` retains arbitrary cut-certified binary cell trees and compatible labels under the actual D_lambda. The source uses each realization's own fixed cost and does not infer labeled-tree isomorphism from matching type sets. For the specific distinct-leaf, unit-weight combs, enumeration changes do not change C0; the dependency audit explicitly corrects its earlier overstatement on this point.

The independent representation is now also proposed in `PolytomyCladeRepresentation.lean`. It defines cell-clade preservation without a graft witness, proves binary same-cell refinement forces rooted isomorphism, extracts a genuine whole-block frontier, proves exact-once block enumeration and connects the entire actual-D_lambda reduction through `full_standard_canonical_carta_reduction`. `POLYTOMY-CLADE-FRONTIER-BRIDGE.md` supplies the complete hand derivation and identifies the prior standard refinement convention. These terms remain unelaborated and do not supply a graph-edge-contraction datatype or a polynomial-machine certificate.

1. All proposed terms need authorized elaboration and kernel checking. Hand inspection of source APIs is not execution evidence. There may be syntax, implicit-argument, simplifier or tactic issues.
2. The newly proposed distinct-cell, mixed-descendant and D_lambda adapter terms require elaboration and checking. Their semantic conventions are explicit in `PolytomyStarSemantics.lean`; there is no accepted kernel verification.
3. The new independent cell-clade representation and full cut/frontier equivalence must be elaborated. A separate graph-edge-contraction datatype and kernel proof connecting it to the standard cell-clade convention are still not supplied; the complete hand equivalence is recorded with primary-source attribution.
4. Finite encoded inputs, polynomial construction/time/bit-size bounds, and a polynomial NP certificate checker remain to be formalized. Classical MSSC NP-hardness must enter through a precise, attributed complexity interface. The finite decision equivalence alone is not a formal NP-hardness theorem. The canonical output-realization adapter is now proposed, but its terms are unelaborated and its finite sorting formula is not a certified encoded polynomial constructor. Pinned polynomial-Turing-machine composition is marked `proof_wanted`, and ordinary `ManyOneReducible` is not a substitute for polynomial-time reducibility. The hand encoding note now explicitly rejects huge invalid binary dimensions using input-length-bounded checks before construction loops.
5. The separate full-DAG subset dynamic program still needs its own formal semantics, correctness induction, and operation/bit-cost bounds.

These gaps are not hidden assumptions of the proposed finite reduction theorem; they are additional obligations before claiming the full external complexity result formally verified. The complete mathematical proof remains the independently hand-reviewed artifact, not a Lean certificate.

## Pinned read-only API audit

Source inspected against Lean v4.33.1 and mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, matching the existing pinned manifest. No toolchain was launched.

- Lean `Init/Data/List/Basic.lean`: `foldl_cons`, recursive `takeWhile`, and the orientation of `List.Perm.swap`.
- Lean `Init/Data/List/Lemmas.lean`: `not_mem_of_not_mem_cons`.
- Mathlib `Data/Finset/Dedup.lean`: `List.toFinset_eq_of_perm`, `List.perm_of_nodup_nodup_toFinset_eq`, `Finset.nodup_toList`.
- Mathlib `Data/List/Nodup.lean`: `List.Nodup.map`, `List.nodup_map_iff`.
- Mathlib `Data/Finset/Card.lean`: `Finset.card_image_of_injective`.
- Mathlib `Data/Finset/Union.lean`: `singleton_biUnion`, `union_biUnion`.
- Mathlib `Algebra/BigOperators/Group/List/Basic.lean`: generated additive `List.Perm.sum_eq`.
- Mathlib `Algebra/BigOperators/Group/Finset/Defs.lean`: generated additive `Finset.sum_map_toList`.
- Mathlib `Algebra/BigOperators/Group/Finset/Basic.lean`: `card_eq_sum_ones` and generated additive `sum_filter`.
- Mathlib `Data/Nat/Find.lean`: `Nat.find_spec` and `Nat.find_min'`.
- Mathlib `Data/List/Nodup.lean`: the exact `List.nodup_flatMap` characterization and the `Nodup.product` proof pattern for disjoint indexed cell blocks.
- Mathlib `Data/Finset/Card.lean`: `List.toFinset_card_of_nodup`.
- Mathlib `Data/Sum/Basic.lean`: `Sum.inl_injective`, `Sum.inr_injective`.

This records a read-only dependency audit, not comprehensive API validation or a successful build.

## Prior-work limit

Subset/tripartition amalgamation and single-exponential degree-parameterized polytomy algorithms already appear in phylogenetic reconciliation, including Jacox et al. (2017). `POLYTOMY-PRIOR-WORK.md` records the comparison. Our dynamic program is an adaptation to the specified Carta objective, not a novelty claim for that general technique. The exact fixed-star objective embedding has not received an exhaustive historical novelty audit.
