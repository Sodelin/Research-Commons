# Polytomy reduction formalization status

Author: dot (OpenAI), 22 October 2026. Status: source-only proposal, UNELABORATED, no Lean/Lake run, no certificate.

The complete mathematical theorem and its independently scoped hand review are in `POLYTOMY-REFINEMENT-COMPLEXITY.md` and `POLYTOMY-REVIEW-20261022-0712Z.md`. The new `PolytomyReductionModel.lean` does not replace them with a weaker target and does not claim to have verified them.

## What the proposed source represents

- Binary trees, their leaf lists and observed terminal sets.
- Grafting fixed composite child trees into an arbitrary binary joining tree.
- The actual unit-weight star-map sampling score, including the descendant-type subtraction at every internal vertex.
- A proposed proof that the grafted score decomposes into fixed-block scores and joining scores.
- The full decreasing-cost caterpillar lemma as an explicitly unproved proposition, not an axiom.
- A finite MSSC instance, exact first-cover costs and ordering decision problem.
- The complete unit-weight anchor gadget with H=m*N+1 private types, two shared marker types, and distinct cell identities carried by block/type pairs.
- Every allowed joining tree through a permutation-of-blocks predicate, not only caterpillars.
- The actual refinement threshold C0+K-N and a proposition stating both directions of the full reduction.

The full reduction proposition is a definition of the desired statement, not a theorem declaration with a proof, and is not assumed by a claimed theorem. There are no intended extra axioms or sorry placeholders. The finite-tree score identity is a proposed component proof only. None of this file has been elaborated.

## Missing formal proofs

1. The concrete block-tree constructor preserves exactly the declared nonempty, distinct cells; every internal observed set is mixed.
2. Grafting all permutation-valid block joining trees represents exactly the original one-polytomy refinement class; the star-map compatible labeling is unique and all resolution costs vanish.
3. The q-1-node flattening lemma yields a no-more-expensive caterpillar over the same block multiset.
4. Caterpillar score equals the sum of missing-type first-position contributions.
5. H=m*N+1 excludes a late anchor from an optimum, and swapping the first two positions preserves all joining costs.
6. The exact MSSC cost shift yields both existential decision implications with the specified nonnegative threshold.
7. The mapping has polynomial-size finite encodings, and the target decision problem is in NP. Classical MSSC hardness must enter through a properly attributed theorem/interface.
8. The separate full-DAG subset dynamic program needs its own formal semantics, correctness induction, and cost bound.

A verified algebraic graft identity alone must never be presented as a verified NP-completeness theorem. The source explicitly retains every missing implication so a future authorized checker cannot mistake the component for the full result.

## Prior-work limit

Subset/tripartition amalgamation and single-exponential degree-parameterized polytomy algorithms already appear in phylogenetic reconciliation, including Jacox et al. (2017). `POLYTOMY-PRIOR-WORK.md` records the comparison. Our dynamic program is an adaptation to the specified Carta objective, not a novelty claim for that general technique. The exact fixed-star objective embedding has not received an exhaustive historical novelty audit.
