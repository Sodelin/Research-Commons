import MinimalPathOrderDependencies
import Mathlib.Order.WellFounded
import Mathlib.Data.Fintype.Pigeonhole

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Turn the proved acyclic finite path dependency into genuine well-founded
induction. Pinned upstream APIs were inspected read-only: the descending-
chain characterization and finite/infinite pigeonhole theorem. A repeated
position yields a concrete nonempty closed route, not an assumed finite-DAG
well-foundedness theorem.
-/

namespace RestrictedCausal.IntervalDependency

open SelectedWalk

theorem descending_segment (R : Nat → Nat → Prop) (f : Nat → Nat)
    (step : ∀ n, R (f (n + 1)) (f n)) (start count : Nat) :
    ∃ vertices, Route R (f (start + count)) vertices (f start) ∧ vertices.length = count := by
  induction count with
  | zero => exact ⟨[], by simpa only [Nat.add_zero] using Route.nil (f start), rfl⟩
  | succ count ih =>
      obtain ⟨vertices, route, length⟩ := ih
      refine ⟨f (start + count) :: vertices, ?_, ?_⟩
      · have edge : R (f (start + (count + 1))) (f (start + count)) := by
          simpa only [Nat.add_assoc] using step (start + count)
        exact .cons edge route
      · simpa only [List.length_cons, length]

theorem bounded_acyclic_wellFounded (R : Nat → Nat → Prop) (bound : Nat)
    (bounded : ∀ a b, R a b → a < bound ∧ b < bound)
    (acyclic : ∀ a vertices, Route R a vertices a → vertices = []) : WellFounded R := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨?_⟩
  rintro ⟨f, step⟩
  let finitePosition : Nat → Fin bound := fun n => ⟨f n, (bounded _ _ (step n)).2⟩
  obtain ⟨i, j, different, same⟩ := Finite.exists_ne_map_eq_of_infinite finitePosition
  have sameValue : f i = f j := congrArg Fin.val same
  have ordered : i < j ∨ j < i := by omega
  have collisionImpossible : ∀ i j, i < j → f i = f j → False := by
    intro i j less equal
    obtain ⟨vertices, route, length⟩ := descending_segment R f step i (j - i)
    have endpoint : i + (j - i) = j := by omega
    rw [endpoint, ← equal] at route
    have empty := acyclic (f i) vertices route
    rw [empty] at length
    simp only [List.length_nil] at length
    omega
  rcases ordered with less | greater
  · exact collisionImpossible i j less sameValue
  · exact collisionImpossible j i greater sameValue.symm

end RestrictedCausal.IntervalDependency

namespace RestrictedCausal.IndexedDiscriminatingSections

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection HPLTarget
open InducingSeparation DiscriminatingStatus VertexActivePaths
open DiscriminatingIntervalGeometry IntervalDependency

universe u v w

theorem shortest_path_wellFounded_dependencies {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) {xs : List X}
    (shortest : Shortest (mag D) Z x y xs) (notStart : ¬ Z x) (notEnd : ¬ Z y) :
    ∃ vertex : Nat → X, Trace vertex 0 (x :: xs) ∧
      ∃ (chosen : ∀ i, ShieldedPosition D vertex (x :: xs).length i → IndexedWitness D vertex i)
        (start : Nat → Nat),
        (∀ i (hi : ShieldedPosition D vertex (x :: xs).length i), start i = (chosen i hi).start) ∧
        (∀ i (hi : ShieldedPosition D vertex (x :: xs).length i), (chosen i hi).start < (x :: xs).length) ∧
        WellFounded (RestrictedBetween (ShieldedPosition D vertex (x :: xs).length) start) := by
  obtain ⟨vertex, «trace», chosen, start, matches, bounds, acyclic⟩ :=
    shortest_path_has_acyclic_dependencies D Z x y shortest notStart notEnd
  refine ⟨vertex, «trace», chosen, start, matches, bounds, ?_⟩
  apply bounded_acyclic_wellFounded _ (x :: xs).length ?_ acyclic
  intro a b edge
  have aBound := edge.1.2.1
  have bBound := edge.2.1.2.1
  exact ⟨by omega, by omega⟩

end RestrictedCausal.IndexedDiscriminatingSections
