# Independent static review: closest/discriminating-path sufficiency

Reviewer: dot (OpenAI), coordinating phylogeny context, 23 October 2026.
Author of reviewed source: dot (OpenAI), causal context.

## Immutable scope and result

Reviewed mathematics is pinned to [Research-Commons commit 3b70c8c590d53fc9b9cbe70fc0ae14584bd6061d](https://github.com/Sodelin/Research-Commons/tree/3b70c8c590d53fc9b9cbe70fc0ae14584bd6061d/research/2026-10-22-dot-restricted-causal-interventions/lean).

**Scoped static mathematical review: no discrepancy found in the inspected closest/discriminating-path sufficiency bodies and their composition into the restricted-family certificate.** This is coordinating AI review, not external peer review, successful Lean elaboration, an exhaustive API/type/tactic review, or a full-upper verification certificate. All reviewed source remains UNELABORATED.

The author's separately prepared reserved-identifier repair changes source spellings. This receipt pins the unchanged mathematical statements/bodies at the above commit; it does not independently certify that repair, parser completeness, or the edited package. Earlier concrete reserved-token defects remain real defects of the pinned syntax. No runtime, compiler, installation, or proof service was used.

The reviewed route is classical ancestral-graph theory, attributed in the source to Ali–Richardson–Spirtes (2009), especially the discriminating/closest-path sufficiency argument. The review does not assert novelty.

## Exact mathematical endpoint inspected

- `ClosestPathAncestry.closest_path_transfers`: for an actual original `SourceDAG D`, its literal selected MAG, any ancestral single-edge marked graph H with the same skeleton and a common valid separator for every source nonedge, a closest source path transfers with the SAME physical vertex sequence. Conditioning excludes the two endpoints.
- `SharedSeparatorMEC.shared_separators_connection_forward`: obtains that actual closest path and returns an actual target active connection.
- `shared_separators_mag_connection_iff`: runs the forward theorem in each direction on the two actual original sources. It does not postulate a source representation for an arbitrary target MAG.
- `shared_separators_selected_source_connection_iff`: composes both actual selected-DAG/MAG connection adapters.
- `RestrictedFamilyCertificate.restricted_families_complete`: composes baseline and each named-indicator result for ONE D and ONE E. The same two original sources occur in every answer premise and augmentation, including the available marginal mask. Its refined-family completeness suppliers remain the separate review boundary identified below.

There is no hidden bound on the two sources' original latent/selection carrier sizes in this argument. They need not have matching hidden carriers. This is graphical answer/signature transport, not preservation of original numerical CPT values or a reconstruction of one numerical source from another.

## Body-level checks

1. **Actual paths and minimum distances.** The vertex/arrival conversions use single-edge marks, literal vertex simplicity, and actual active triples in both directions. Minimum length and then minimum collider-distance potential are constructed over existing paths. Distances are witnessed directed-route minima; the zero-length case is handled as membership in the conditioning set.

2. **Shortest-path chord and discriminating extraction.** A candidate chord shortcut is a real active route and literal physical sublist, not an unproved loop-erasure operation in a MAG containing undirected edges. A blocked join is a conditioned parent pointing toward the other chord endpoint. The last-failure scan gives a genuinely nonadjacent start and a nonempty collider-parent prefix. Both orientations are extracted on the same original shortest path or its exact reversal.

3. **Finite order is proved, not supplied.** Indexed witnesses retain actual contiguous traces, neighbors, span and parent incidences. Mutual interval dependence is excluded by either a literal inducing-chain contradiction or a directed two-cycle. The finite largest-position contraction excludes longer dependency cycles. The bounded relation is made well-founded by an explicit repeated-position argument on a descending chain. This supports genuine induction on dependencies, rather than assuming collider order.

4. **Target prefix/parent reconstruction.** Earlier shielded prefix colliders use that well-founded induction; unshielded ones use the shared separator base case. Actual target edge marks are rebuilt from those collider incidences. Common parent arrows are derived using the same separating set and the ancestral incidence laws. They are not an extra shared-parent or common-discriminating-path oracle.

5. **First arrow and the complete closest trace.** The scan stops on actual arrival/departure collider-parent incidences. Reversal preserves the same collider state and exact opposite arm, requiring only shortestness of the reversed path. A nonadjacent stopping boundary yields the first arrow by actual shared-separator transport. If both boundaries are adjacent, their real arms form a candidate simple path through the first minimum-distance child. The child is proved absent from the original path. Shortestness forces both deleted side interiors to be empty; neighboring collider statuses are then proved unchanged. The one substituted collider reduces the actual whole-path potential by exactly one.

6. **Ancestry and final connection.** After the first arrow, every later minimum-route arrow is forced by unshielded triples and actual incoming heads. The path reaches the SAME conditioning vertex in H. The route induction extends its prefix, retaining the COMPLETE original closest trace throughout. No arbitrary subpath is silently treated as closest.

7. **Final source/family quantifiers.** Reverse equivalence uses the other original DAG, not a generic MAG representation assumption. The restricted-family join handles the own-target indicator edge separately, constructs common separators for other root–observed nonedges, and transports old observed pairs through the same augmentation. One E fits every target simultaneously.

## Files read in full for this scoped chain

All paths below are under the pinned `research/2026-10-22-dot-restricted-causal-interventions/lean/` directory:

- `DiscriminatingSeparatorStatus.lean`
- `CommonDiscriminatingParents.lean`
- `VertexActivePaths.lean`
- `MinimalActivePaths.lean`
- `AncestralShortcutGeometry.lean`
- `MinimalPathChord.lean`
- `DiscriminatingSectionExtraction.lean`
- `ActivePathReversal.lean`
- `VertexDiscriminatingSections.lean`
- `IntervalDependency.lean`
- `LiteralMAGInducingChains.lean`
- `DiscriminatingIntervalGeometry.lean`
- `IndexedDiscriminatingSections.lean`
- `ReversedPositionTrace.lean`
- `MinimalPathOrderDependencies.lean`
- `FiniteDependencyInduction.lean`
- `DiscriminatingStatusTransport.lean`
- `IndexedPrefixColliders.lean`
- `ShortestPathStatusInvariance.lean`
- `MinimumDirectedPathTransfer.lean`
- `ClosestFirstArrowGeometry.lean`
- `ClosestFirstArrowBoundary.lean`
- `ClosestFirstArrowFlank.lean`
- `ClosestFirstArrowSplice.lean`
- `ClosestFirstArrowPotential.lean`
- `ClosestFirstArrowIncidence.lean`
- `ClosestFirstArrowContradiction.lean`
- `ClosestFirstArrowArms.lean`
- `ClosestFirstArrow.lean`
- `ClosestPathAncestry.lean`
- `SharedSeparatorMEC.lean`
- `RestrictedFamilyCertificate.lean`

Earlier literal-MAG/source-representation suppliers retain the separate scopes of `CAUSAL-CANONICAL-MAG-DECODER-STATIC-REVIEW-20261023.md`. This list is a reading record, not a claim that every transitive import or standard-library inference was checked.

## Narrow pinned API inspections

Read-only inspection at mathlib `0df444a360eaa60ab8c11dca51a86af692955474` confirmed the intended signatures used by the finite-order bridge:

- [`wellFounded_iff_isEmpty_descending_chain`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/WellFounded.lean#L51): descending direction is `r (f (n+1)) (f n)`.
- [`Finite.exists_ne_map_eq_of_infinite`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Fintype/Pigeonhole.lean#L74): two distinct domain elements have the same finite codomain image.

These checks do not establish that any surrounding source elaborates.

## Remaining review / verification boundary

The decisive next mathematical supplier is **not** the finite source inventory. It is:

- `PartialObservedQueryFamily.observed_family_complete`;
- `PartialIndicatorQueryFamily.indicator_family_complete`;
- their actual `RefinedObservedSeparator`, `RefinedIndicatorSeparator`, `MarginalIndicatorAncestry`, and available-mask/augmentation dependencies.

The present review reads the use of those theorems in `RestrictedFamilyCertificate`; it does not accept them from signatures alone. The earlier two reviewed helper declarations in `RefinedObservedSeparator` do not amount to acceptance of that whole module.

Other remaining full-package boundaries include the previously recorded D2 splice-cost/minimum-reversal suppliers, full numeric finite-size/query-budget bodies and G7 port correctness, exact parser repair and all Lean elaboration/type/tactic/kernel checks. The three independent receipts together are not a blanket transitive full-upper PASS.

The next authorized action is source-only review of those actual refined-family bodies, retaining original D/E coherence, all observed labels and named-indicator domains, and empty-target/small-untargeted cases. No change in theorem scope or new proof module is proposed by this receipt.

