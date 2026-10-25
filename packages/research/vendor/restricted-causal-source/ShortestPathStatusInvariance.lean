import IndexedPrefixColliders

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Every triple of an actual shortest selected-MAG active path has invariant
collider status under equal skeletons and one valid shared separator per
nonedge. The proof performs genuine well-founded induction on the actual
discriminating sections, reconstructing target prefixes at every local step.
It does not yet transfer collider ancestry to the conditioning set, and so
does not by itself prove MAG Markov equivalence.
-/

namespace RestrictedCausal.IndexedDiscriminatingSections

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection HPLTarget
open InducingSeparation DiscriminatingStatus VertexActivePaths WeakInducing
open DiscriminatingIntervalGeometry IntervalDependency

universe u v w

theorem position_section_data {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) (Z : X → Prop) (x y : X)
    {xs : List X} (shortest : Shortest (mag D) Z x y xs) («trace» : Trace vertex 0 (x :: xs))
    (i : Nat) (lower : 0 < i) (upper : i + 1 < (x :: xs).length) :
    Adjacent (mag D) (vertex (i - 1)) (vertex i) ∧
      Adjacent (mag D) (vertex i) (vertex (i + 1)) ∧
      ([vertex (i - 1), vertex i, vertex (i + 1)] : List X).Nodup := by
  obtain ⟨front, back, equation⟩ := trace_three_section vertex (x :: xs) 0 «trace» i lower
    (by simpa only [Nat.zero_add] using upper)
  obtain ⟨«section»⟩ := realize_three_section (mag D) (mag_single_edges D) Z x y
    (vertex (i - 1)) (vertex i) (vertex (i + 1)) front back shortest equation
  obtain ⟨firstLeft, firstRight, firstEdge, _, _⟩ := «section».first_step
  obtain ⟨lastLeft, lastRight, lastEdge, _, _⟩ := «section».second_step
  refine ⟨⟨firstLeft, firstRight, ?_⟩, ⟨lastLeft, lastRight, ?_⟩, ?_⟩
  · simpa only [«section».first_vertex, «section».middle_vertex] using firstEdge
  · simpa only [«section».middle_vertex, «section».third_vertex] using lastEdge
  · have injective : ∀ a b, a < (x :: xs).length → b < (x :: xs).length →
        vertex a = vertex b → a = b := by
      intro a b aBound bBound same
      exact trace_injective vertex (x :: xs) 0 «trace» shortest.1.2.1 a b
        (by omega) (by simpa only [Nat.zero_add] using aBound)
        (by omega) (by simpa only [Nat.zero_add] using bBound) same
    have firstNe : vertex (i - 1) ≠ vertex i := by
      intro same
      have indices := injective (i - 1) i (by omega) (by omega) same
      omega
    have endsNe : vertex (i - 1) ≠ vertex (i + 1) := by
      intro same
      have indices := injective (i - 1) (i + 1) (by omega) upper same
      omega
    have lastNe : vertex i ≠ vertex (i + 1) := by
      intro same
      have indices := injective i (i + 1) (by omega) upper same
      omega
    simp [firstNe, endsNe, lastNe]

theorem unshielded_position_status {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X) (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent H a b)
    (shared : SharedSeparators (mag D) H)
    (vertex : Nat → X) (Z : X → Prop) (x y : X) {xs : List X}
    (shortest : Shortest (mag D) Z x y xs) («trace» : Trace vertex 0 (x :: xs))
    (i : Nat) (lower : 0 < i) (upper : i + 1 < (x :: xs).length)
    (unshielded : ¬ Adjacent (mag D) (vertex (i - 1)) (vertex (i + 1))) :
    Collider (mag D) (vertex (i - 1)) (vertex i) (vertex (i + 1)) ↔
      Collider H (vertex (i - 1)) (vertex i) (vertex (i + 1)) := by
  obtain ⟨«first», last, simple⟩ := position_section_data D vertex Z x y shortest «trace» i lower upper
  have distinct : vertex (i - 1) ≠ vertex (i + 1) := by
    intro same
    apply (List.nodup_cons.mp simple).1
    exact List.mem_cons_of_mem _ (by simpa only [List.mem_singleton] using same)
  exact shared_separators_unshielded (mag D) H (mag_single_edges D) singleH skeleton shared
    _ _ _ distinct «first» last unshielded simple

/-- Status invariance on the physical shortest path, not on an independently
chosen equivalent graph summary. The earlier prefix triples are located in
the actual dependency interval using the retained full trace and exact span.
Unshielded parents use the shared-separator base case; shielded parents use
the proved well-founded dependency, so there is no circular invariance step. -/
theorem shortest_path_status_invariant {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X) (lawsH : AncestralLaws H)
    (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent H a b)
    (shared : SharedSeparators (mag D) H)
    (Z : X → Prop) (x y : X) {xs : List X}
    (shortest : Shortest (mag D) Z x y xs) (notStart : ¬ Z x) (notEnd : ¬ Z y) :
    AllTriples (fun a b c => Collider (mag D) a b c ↔ Collider H a b c) (x :: xs) := by
  classical
  obtain ⟨vertex, «trace», chosen, start, matches, bounds, wellFounded⟩ :=
    shortest_path_wellFounded_dependencies D Z x y shortest notStart notEnd
  have indexed : ∀ i, 0 < i → i + 1 < (x :: xs).length →
      (Collider (mag D) (vertex (i - 1)) (vertex i) (vertex (i + 1)) ↔
        Collider H (vertex (i - 1)) (vertex i) (vertex (i + 1))) := by
    intro i
    apply wellFounded.induction i
    intro i earlier lower upper
    by_cases chord : Adjacent (mag D) (vertex (i - 1)) (vertex (i + 1))
    · have active : ShieldedPosition D vertex (x :: xs).length i := ⟨lower, upper, chord⟩
      let w := chosen i active
      have startBound : w.start < (x :: xs).length := bounds i active
      have prefixInvariant : ∀ j, Interior w.start i j →
          Collider H (vertex (j - 1)) (vertex j) (vertex (j + 1)) := by
        intro j interior
        have jLower : 0 < j := by rcases interior with h | h <;> omega
        have jUpper : j + 1 < (x :: xs).length := by rcases interior with h | h <;> omega
        have sourceCollider := w.colliders j interior
        by_cases jChord : Adjacent (mag D) (vertex (j - 1)) (vertex (j + 1))
        · have jActive : ShieldedPosition D vertex (x :: xs).length j := ⟨jLower, jUpper, jChord⟩
          have dependency : RestrictedBetween (ShieldedPosition D vertex (x :: xs).length) start j i := by
            refine ⟨jActive, active, ?_⟩
            simpa only [BetweenStart, matches i active, w, Interior] using interior
          exact (earlier j dependency jLower jUpper).mp sourceCollider
        · exact (unshielded_position_status D H singleH skeleton shared vertex Z x y
            shortest «trace» j jLower jUpper jChord).mp sourceCollider
      have targetPrefix := indexed_prefix_colliders D H lawsH.symmetric vertex w prefixInvariant
      have witnessStatus := witness_status_transfer (mag D) H lawsH (mag_single_edges D) singleH
        skeleton shared w.witness targetPrefix
      exact indexed_status_to_standard D H lawsH.symmetric vertex w witnessStatus
    · exact unshielded_position_status D H singleH skeleton shared vertex Z x y
        shortest «trace» i lower upper chord
  apply all_triples_of_trace vertex _ (x :: xs) 0 «trace»
  intro i lower upper
  exact indexed i lower (by simpa only [Nat.zero_add] using upper)

end RestrictedCausal.IndexedDiscriminatingSections
