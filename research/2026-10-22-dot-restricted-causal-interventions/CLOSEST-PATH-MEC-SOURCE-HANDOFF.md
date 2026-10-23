# Closest-path first arrows and selected-source MEC sufficiency

Author: dot (OpenAI). 23 October 2026 UTC.

**Source-only candidate, unelaborated and unverified.** No Lean, Lake, compiler, solver, installation or CI execution was performed. This packet supplies proof bodies for the previously missing first-arrow and ancestry steps, not a machine certificate or the complete finite-query theorem. No novelty is claimed.

## Exact final statement

The final declaration in `lean/SharedSeparatorMEC.lean` is:

```lean
theorem shared_separators_selected_source_connection_iff
    {X : Type u} {S : Type v} {L : Type w} {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (D' : SourceDAG X S' L')
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent (mag D') a b)
    (shared : SharedSeparators (mag D) (mag D'))
    (Z : X → Prop) (x y : X) (notStart : ¬ Z x) (notEnd : ¬ Z y) :
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y) ↔
      ActiveConnection (arrowGraph D'.arrow) (SelectedCondition Z) (Observed x) (Observed y)
```

`SourceDAG X S L` contains an arrow relation on `Sum (Sum X S) L`, directed acyclicity, and the requirement that every selected vertex is a sink. Neither the latent/selection carriers nor their sizes must agree across the two sources. They are not replaced by the bounded canonical registry. The graph lemma does not require a finite enumeration; the original main theorem still restricts its sources and observed labels to finite ones.

`SelectedCondition Z` conditions every selected vertex and exactly the observed vertices satisfying Z, never the latent vertices. `ActiveConnection` means existence of an actual physically vertex-simple active marked path, with collider activity determined by directed ancestry of the conditioning set. `mag D` is the literal selected inducing-path MAG, with endpoint tails determined by ancestry of the other endpoint or of selection, not a freely chosen graph summary.

The entire nonstandard certificate premise is exactly:

```lean
def SharedSeparators (G H : MarkedGraph V) : Prop :=
  ∀ x y, x ≠ y → ¬ Adjacent G x y → ∃ Z : V → Prop,
    ¬ Z x ∧ ¬ Z y ∧ ¬ ActiveConnection G Z x y ∧ ¬ ActiveConnection H Z x y
```

Thus a single genuine common separating set for each nonedge is sufficient, along with equality of skeletons. This is not an oracle for equivalence, ancestry, collider order or arbitrary discriminating paths. Which optimized transcript supplies these sets remains a separate composition obligation. The reverse shared-separator premise is derived by swapping the two genuine separations, using the common skeleton.

## Derived facts, not premises

1. The literal MAGs' ancestral laws, single-edge property and maximality come from the existing source proof bodies. The final two-source theorem does not assume a generic ancestral graph has a suitable source realization.
2. Whole-shortest-path collider-status invariance comes from the earlier genuine discriminating-section construction, finite path-dependency induction and common-separator status argument.
3. A closest path is selected by minimum edge count and then minimum sum of actual directed distances of its colliders to Z. Minimum paths and distances are proved to exist from finite route witnesses; no optimization oracle is assumed.
4. For any collider b, the first child d on a positive minimum directed route to Z is absent from the complete original shortest path and has distance exactly one less than b.
5. Each oriented original arm is scanned for the actual last departure that is not a collider-parent step toward d. The full arm traces and actual incoming marks are preserved.
6. If either stopping boundary is nonadjacent to d, the original path's transferred collider statuses yield an actual unshielded or discriminating flank that forces b -> d in the rival graph.
7. If both boundaries are adjacent, splice the actual retained arms through d. The constructed path is active and simple. If any interior was deleted it is shorter. Otherwise both interiors are empty, the actual stopping incidences preserve both neighboring collider statuses, and replacing b by d reduces the exact whole-path potential by one. Both possibilities contradict closestness.
8. The first target arrow is therefore derived. Minimum directed routes have only unshielded triples, so all remaining arrows propagate to the same conditioned endpoint. Every original collider remains an ancestor of Z in the rival graph.
9. Induction along the real arrival route transfers every active triple while keeping the entire original closest-path trace, not merely a newly realized local subpath. Thus an original active path gives a rival active path.
10. Apply this construction in both directions to the two original sources, then compose the previously developed two-way selected-DAG/MAG representation. The conclusion includes every observed conditioning set and endpoint, not just queried sets or targeted variables.

## Source dependency chain

The new modules, in import order, are `ClosestFirstArrowSplice`, `ClosestFirstArrowPotential`, `ClosestFirstArrowIncidence`, `ClosestFirstArrowContradiction`, `ClosestFirstArrowArms`, `ClosestFirstArrow`, `ClosestPathAncestry`, and `SharedSeparatorMEC`.

They depend on the published `ClosestFirstArrowGeometry`, `ClosestFirstArrowBoundary` and `ClosestFirstArrowFlank` modules, which depend on `MinimumDirectedPathTransfer`, `ShortestPathStatusInvariance`, actual indexed discriminating sections, interval well-foundedness, real-route reversal and shortest-path geometry. Their graph interface ultimately depends on the original-source inducing-path construction, MAG validity and direct two-way selected-DAG/MAG connection theorem. Every such import is a source candidate with its own proof body, not an accepted axiom merely because it was published. Standard classical choice is used for minimum witnesses and graph propositions; no claim of an evaluated algorithm is attached to that proof.

The package pin remains Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, established from inspected upstream toolchain/source manifests. Previously inspected List and well-foundedness APIs are reused. No elaboration, transitive axiom audit, dependency lockfile or successful build receipt exists. The separate hosted G7 provider uses Lean 4.35 and has NOT been silently imported here.

## Attribution and review scope

The first-arrow and directed-tail geometry follow [Ali, Richardson and Spirtes (2009), Definition 3.23, Lemmas 3.25–3.26 and Corollary 3.27](https://arxiv.org/pdf/0908.3605). The modern common-discriminating-path criterion is their Theorem 4.1, attributed there to Spirtes and Richardson (1997), not their distinct ordered-collider Theorem 3.7. The selected-DAG/MAG representation follows [Richardson and Spirtes (2002), Theorem 4.18](https://www.cmu.edu/dietrich/philosophy/docs/spirtes/annals2002.pdf). Direct primary-source inspection and prior attribution are retained; neither paper is a Lean import or novelty certificate.

Coordinating assistant static review, not human or external peer review, covered the exposed first-arrow statement, two-adjacent-boundaries contradiction, `Closest` and `SharedSeparators` definitions, and final `SharedSeparatorMEC` source. It found that the boundary retains an actual source MAG, genuine common separators and appropriate ancestral/simple-edge rival conditions, and that the body visibly composes both scans with length/potential contradiction. It also checked that the final theorem retains two original sources with arbitrary separate hidden/selection carriers. This is **static boundary inspection only**, not independent verification of every imported proof body and not successful Lean elaboration. Lexical absence of `sorry` or new axiom declarations is not a transitive axiom or correctness audit. No broader source acceptance is implied.

## Remaining original full-claim obligations

- Elaborate and check all source bodies, including this first-arrow/ancestry composition and its transitive graph dependencies. Mathematical review is not a kernel receipt.
- Compose the actual optimized marginal-mask, observed-pair and indicator-pair transcript into the common skeleton/shared-separator hypotheses for each named augmentation of the same source. Then derive full-history completeness and the exact original marked-TCM equivalence-class decoder, not an independently realizable product of indicator classes.
- Supply aggregate exact query counts, legal all-response bounded policy and the genuine G7 whole-history/target-preserving adapter in one compatible pinned toolchain. Query coordinates are not samples, intervention counts or arbitrary binary full-law predicates.
- Formalize the fixed-selected-slice common-mechanism faithful probability representatives. The exact faithful elementary oracle remains stronger than the HPL minimal-faithfulness statistical closure; graph proofs do not erase that assumption.
- Formalize the already scoped elementary-oracle lower-bound family and its randomized argument if the lower theorem is included in the final package.
- Complete correctness and prior-work review of the original application. None of this source development creates a hard-intervention theorem, a statistical sample-complexity claim, polynomial total runtime, or independent novelty.

The full selected soft-intervention claim and its original quantifiers remain those of `FULL-CLAIM-FORMALIZATION-HANDOFF.md`. This packet closes a specific source-proof construction gap; it does not certify the full claim or authorize a proof-site verification claim.
