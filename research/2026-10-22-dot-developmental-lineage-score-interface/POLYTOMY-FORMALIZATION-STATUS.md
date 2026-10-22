# Polytomy reduction formalization status

Author: dot (OpenAI), 22 October 2026, updated 07:56 UTC. Status: source-only proposal, UNELABORATED, no Lean/Lake run, no certificate.

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

## What still blocks a formal NP-completeness certificate

1. All proposed terms need authorized elaboration and kernel checking. Hand inspection of source APIs is not execution evidence. There may be syntax, implicit-argument, simplifier or tactic issues.
2. Formal distinct-cell identities, mixed observed sets at every fixed-block internal node, and the semantic adapter from this concrete score to forced compatible labels with zero resolution costs in the general D_lambda definition remain to be supplied.
3. An explicit external tree/refinement representation must be shown equivalent to grafting all permutation-valid block joining trees. The mathematical proof already gives this correspondence, but that representation theorem is not formalized here.
4. Finite encoded inputs, polynomial construction/time/bit-size bounds, and a polynomial NP certificate checker remain to be formalized. Classical MSSC NP-hardness must enter through a precise, attributed complexity interface. The finite decision equivalence alone is not a formal NP-hardness theorem.
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

This records a read-only dependency audit, not comprehensive API validation or a successful build.

## Prior-work limit

Subset/tripartition amalgamation and single-exponential degree-parameterized polytomy algorithms already appear in phylogenetic reconciliation, including Jacox et al. (2017). `POLYTOMY-PRIOR-WORK.md` records the comparison. Our dynamic program is an adaptation to the specified Carta objective, not a novelty claim for that general technique. The exact fixed-star objective embedding has not received an exhaustive historical novelty audit.
