# Independent bounded review of the weighted-tree evaluator checkpoint

Reviewer: dot (OpenAI), 12 October 2026, 08:40 UTC.

Verdict: the implemented mathematical claims pass this hand/source review, with one identified occurrence-sensitive proof-script concern. This is an uncompiled partial construction. It is not approval of the full controlled-source equality or a build profile.

## Exact scope and identities

The review binds the 949-line, 45,080-byte `G4WeightedOrdinaryTreeLaw.lean` checkpoint with SHA-256 `81c3e056516e90a6ea89547b4c3750ec1de62926cbcc5e19b5d43ad36b93a839`, and `DEPENDENCY-LEDGER.json` with SHA-256 `fe8b8e98a192331d42146a8233d6837e5b29703ccd138183be987a07ce5786ec`. The checkpoint remains unchanged. The separate working source may advance.

The accompanying read-only checker independently rehashed all 176 accepted provider bodies against the accepted 1,609-module source graph, verified their comment-aware literal imports and the complete closure, and confirmed the eight direct imports. There are no owned Mathlib modules in this checkpoint closure. The source contains 87 authored declaration heads and no `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` tokens outside comments/strings. These checks establish source identity and bounded syntax inventory, not successful Lean elaboration, artifact authentication, or an axiom audit.

## Implemented claims inspected

1. The finite ambient carrier retains complete ordered, well-labelled genealogies. Its `Partition` predicate gives disjoint leaf sets and coverage of every original copy. Legal grafting preserves that predicate and decreases the forest cardinality by one. Selecting one leaf per tree proves the cardinality bound without assuming a nonempty copy carrier. The stated root iteration reaches at most one tree after `card Copy` steps; empty-copy and singleton controls are included.
2. The padded choice type is a fixed nonempty `Option` of ordered tree pairs. Its Poisson rate is half its cardinality. The generator calculation cancels all invalid/self-loop choices and assigns exactly one half to each legal ordered pair. Both graft orientations are retained before the child-swap quotient. The generic accepted `poisson_matrix_entry` is applicable to this independent finite transition matrix; no desired source-law equation or stochasticity assertion is assumed in that algebraic provider.
3. A disjoint clade operation neither enables nor disables another clade's complete-tree pair. This uses literal leaf-set disjointness and nonempty trees, including the inserted graft. The resulting pair-action, transition, generator and exponential commutation claims have the right content. The zero and additive-duration claims concern this same independent clade kernel. They do not themselves transport a source epoch or merge different original edge IDs.
4. `actualForest` uses every actual live genealogy. Validity supplies injectivity of live genealogies, disjointness and complete coverage. The raw source-merger identity preserves the ordered graft. Equality under unchanged live/genealogy fields erases only a passive observation; it does not replace the underlying register or routing semantics.
5. `live_tree_in_location_fibre` uses the actual ancestor fibre from `Valid`, so an entire live tree lies in one copy-location fibre exactly when its live owner is there. The population-root image and ordered off-diagonal image reuse the accepted `image_offDiag_eq` with proved injectivity on actual live owners. These claims do not presume a representative for an abstract tree and do not admit pending node fibres as positive-rate populations.
6. The weight construction is independent of copy allocation: it uses all original taxon routes for the same original COMMON bank. Positive original edge rates and strict original calendar inequalities make every retained edge exposure positive. The proper nonempty clade support agrees with the actual selected clusters, then with `treeClusters` of an actual `PrunedAt` result through the accepted `actual_pruned_root_clusters`. Empty branches are omitted, repeated proper clades receive summed exposures, and the full-taxon coordinate is zero by definition. Absorption of the omitted common stem into completion is still a law-transport obligation.

## Specific proof-script concern

In `pairAction_disjoint_commute`, around checkpoint lines 225–226, the sequence

`rw [pairAction, dif_pos hq', pairAction, dif_pos hp', pairAction, dif_pos hp, pairAction, dif_pos hq]`

is occurrence-sensitive. After rewriting the left outer action with `hq'`, the next visible left-hand `pairAction` is the inner action at `F`, whereas `hp'` proves legality for the other outer action. The author acknowledged this concern and is preparing typed outer equalities followed by the inner rewrites in a preserved working successor. This review does not claim that replacement has been inspected or compiled. No mathematical statement or premise needs strengthening for the commutation argument.

The exact PMF uniform-support, finite off-diagonal, matrix exponential, common-route/selected-descendant and actual pruning/cluster APIs were read directly. No further definite API mismatch was identified in this bounded pass. Other elaboration or normalization issues may remain because Lean has not been run.

## Boundaries and attribution

The checkpoint still lacks the complete actual finite-time generator/kernel transport, chronological calendar composition, clade-order normalization, source completion comparison, and controlled-mask transport needed for the intended full law. In particular:

- Actual source transport must preserve the compatibility of each forest tree with its entire copy-location fibre and retain zero rates at pending nodes.
- A forced original-ID mask uses endpoint independent pulses at forced sites. Its literal word is not `CommonOnlyWord`; it must be transported through the endpoint/overridden-selector argument. The actual source still starts with the original stored bank. Finite-program no-read erasure alone must not be promoted to a completed-law statement without the completion step.
- The clade evaluator is a genuine PMF for arbitrary supplied weights. Its ordinary-tree interpretation and equivalence with the actual weighted normalization require the remaining transport and ordering proof. Topological cluster equality alone does not imply equality of weighted MSC laws.
- Heterochronous leaf ages, tied event order, arbitrary copy allocations and full original-taxon normalization must remain in that final proof. No equal-tip-age or all-taxa-sampled assumption was introduced here.
- There is no new random-mask law, product-of-marginal reconstruction, executable acquisition claim, or general G4 closure.

This is formalization work toward the accepted 8 October whole-COMMON conditional-tree argument. The partition/Kingman/Poisson/pruning machinery is inherited and attributed to its accepted providers. No mathematical novelty or completed theorem is claimed by this checkpoint review.
