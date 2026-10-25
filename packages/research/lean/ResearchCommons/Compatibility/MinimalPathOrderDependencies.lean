import ReversedPositionTrace

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual acyclic discriminating-section dependencies on a shortest legal
selected-MAG active path. This composes both literal occurrence adapters,
finite-position injectivity and the graphical interval obstruction. It is
the classical order-dependency component, not yet the full collider-order
induction or closest-path ancestry transfer.
-/

namespace RestrictedCausal.IndexedDiscriminatingSections

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection HPLTarget
open InducingSeparation DiscriminatingStatus VertexActivePaths
open DiscriminatingIntervalGeometry IntervalDependency

universe u v w

theorem trace_three_section {X : Type u} (vertex : Nat → X) (whole : List X) :
    ∀ offset, Trace vertex offset whole → ∀ i, offset < i → i + 1 < offset + whole.length →
      ∃ front back, whole = front ++ [vertex (i - 1), vertex i, vertex (i + 1)] ++ back := by
  induction whole with
  | nil => intro offset «trace» i lower upper; simp only [List.length_nil] at upper; omega
  | cons a rest ih =>
      intro offset «trace» i lower upper
      by_cases «first» : i = offset + 1
      · cases rest with
        | nil => simp only [List.length_cons, List.length_nil] at upper; omega
        | cons b rest =>
            cases rest with
            | nil => simp only [List.length_cons, List.length_nil] at upper; omega
            | cons c back =>
                have previous : i - 1 = offset := by omega
                have following : i + 1 = offset + 1 + 1 := by omega
                refine ⟨[], back, ?_⟩
                simp only [List.nil_append, List.cons_append, previous, «first», following, Nat.add_sub_cancel,
                  «trace».1, «trace».2.1, «trace».2.2.1]
      · have lowerTail : offset + 1 < i := by omega
        have upperTail : i + 1 < offset + 1 + rest.length := by
          simp only [List.length_cons] at upper
          omega
        obtain ⟨front, back, equation⟩ := ih (offset + 1) «trace».2 i lowerTail upperTail
        exact ⟨a :: front, back, by simpa only [List.cons_append, equation]⟩

theorem shortest_shielded_position_indexed {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) (Z : X → Prop) (x y : X)
    {xs : List X} (shortest : Shortest (mag D) Z x y xs)
    («trace» : Trace vertex 0 (x :: xs)) (notStart : ¬ Z x) (notEnd : ¬ Z y)
    (i : Nat) (lower : 0 < i) (upper : i + 1 < (x :: xs).length)
    (chord : Adjacent (mag D) (vertex (i - 1)) (vertex (i + 1))) :
    ∃ indexed : IndexedWitness D vertex i, indexed.start < (x :: xs).length := by
  obtain ⟨front, back, equation⟩ := trace_three_section vertex (x :: xs) 0 «trace» i lower
    (by simpa only [Nat.zero_add] using upper)
  rcases shortest_shielded_triple_discriminated (mag D) (mag_ancestral_laws D) (mag_single_edges D)
      Z x y (vertex (i - 1)) (vertex i) (vertex (i + 1)) front back shortest equation
      notStart notEnd chord with «left» | «right»
  · obtain ⟨w, occurs⟩ := «left»
    obtain ⟨offset, indexed, start, before, finish, bounded, label⟩ :=
      index_forward_occurrence D vertex w (x :: xs) «trace» occurs
    have centerBound : offset + w.parents.length + 1 < (x :: xs).length := by
      rw [finish] at bounded
      omega
    have sameIndex : offset + w.parents.length + 1 = i :=
      trace_injective vertex (x :: xs) 0 «trace» shortest.1.2.1
        (offset + w.parents.length + 1) i (by omega) (by simpa only [Nat.zero_add] using centerBound)
        (by omega) (by simp only [Nat.zero_add]; omega) label
    rw [← sameIndex]
    exact ⟨indexed, by rw [start]; omega⟩
  · obtain ⟨w, occurs⟩ := «right»
    obtain ⟨center, indexed, finishBelow, centerBelow, startBound, label⟩ :=
      index_reverse_occurrence D vertex w (x :: xs) «trace» occurs
    have centerBound : center < (x :: xs).length := by omega
    have sameIndex : center = i :=
      trace_injective vertex (x :: xs) 0 «trace» shortest.1.2.1 center i
        (by omega) (by simpa only [Nat.zero_add] using centerBound)
        (by omega) (by simp only [Nat.zero_add]; omega) label
    rw [← sameIndex]
    exact ⟨indexed, startBound⟩

def ShieldedPosition {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) (size i : Nat) : Prop :=
  0 < i ∧ i + 1 < size ∧ Adjacent (mag D) (vertex (i - 1)) (vertex (i + 1))

/-- The chosen discriminating dependency on the actual shortest active path
is acyclic. Choice is only over proved finite-path witnesses, not over source
realizations or target classes. The theorem retains the unbounded original
latent/selection carriers and all physical observed vertices. -/
theorem shortest_path_dependency_system {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) (Z : X → Prop) (x y : X)
    {xs : List X} (shortest : Shortest (mag D) Z x y xs)
    («trace» : Trace vertex 0 (x :: xs)) (notStart : ¬ Z x) (notEnd : ¬ Z y) :
    ∃ (chosen : ∀ i, ShieldedPosition D vertex (x :: xs).length i → IndexedWitness D vertex i)
      (start : Nat → Nat),
      (∀ i (hi : ShieldedPosition D vertex (x :: xs).length i), start i = (chosen i hi).start) ∧
      (∀ i (hi : ShieldedPosition D vertex (x :: xs).length i), (chosen i hi).start < (x :: xs).length) ∧
      (∀ a vertices, Route (RestrictedBetween (ShieldedPosition D vertex (x :: xs).length) start)
        a vertices a → vertices = []) := by
  classical
  let chosen : ∀ i, ShieldedPosition D vertex (x :: xs).length i → IndexedWitness D vertex i :=
    fun i hi => Classical.choose (shortest_shielded_position_indexed D vertex Z x y shortest «trace»
      notStart notEnd i hi.1 hi.2.1 hi.2.2)
  have bounds : ∀ i (hi : ShieldedPosition D vertex (x :: xs).length i),
      (chosen i hi).start < (x :: xs).length := by
    intro i hi
    exact Classical.choose_spec (shortest_shielded_position_indexed D vertex Z x y shortest «trace»
      notStart notEnd i hi.1 hi.2.1 hi.2.2)
  let start : Nat → Nat := fun i =>
    if hi : ShieldedPosition D vertex (x :: xs).length i then (chosen i hi).start else i
  have «matches» : ∀ i (hi : ShieldedPosition D vertex (x :: xs).length i), start i = (chosen i hi).start := by
    intro i hi
    simp only [start, dif_pos hi]
  exact ⟨chosen, start, «matches», bounds,
    indexed_dependencies_acyclic D vertex (ShieldedPosition D vertex (x :: xs).length) chosen start «matches»⟩

/-- No indexing oracle remains: the total position function and all actual
discriminating witnesses are constructed from the given finite active path. -/
theorem shortest_path_has_acyclic_dependencies {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) {xs : List X}
    (shortest : Shortest (mag D) Z x y xs) (notStart : ¬ Z x) (notEnd : ¬ Z y) :
    ∃ vertex : Nat → X, Trace vertex 0 (x :: xs) ∧
      ∃ (chosen : ∀ i, ShieldedPosition D vertex (x :: xs).length i → IndexedWitness D vertex i)
        (start : Nat → Nat),
        (∀ i (hi : ShieldedPosition D vertex (x :: xs).length i), start i = (chosen i hi).start) ∧
        (∀ i (hi : ShieldedPosition D vertex (x :: xs).length i), (chosen i hi).start < (x :: xs).length) ∧
        (∀ a vertices, Route (RestrictedBetween (ShieldedPosition D vertex (x :: xs).length) start)
          a vertices a → vertices = []) := by
  let vertex := vertexAt x (x :: xs)
  have «trace» : Trace vertex 0 (x :: xs) := trace_vertexAt x (x :: xs)
  exact ⟨vertex, «trace», shortest_path_dependency_system D vertex Z x y shortest «trace» notStart notEnd⟩

end RestrictedCausal.IndexedDiscriminatingSections
