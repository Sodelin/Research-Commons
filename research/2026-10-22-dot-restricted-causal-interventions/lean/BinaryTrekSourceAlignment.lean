import BinaryActivePathMinor

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The fair-source subtype used in the actual circuit has exactly one member
in every connected component left by removing the main-path colliders.
Existence follows original-arrow parents down the derived finite-DAG
rank. Uniqueness follows actual copy equations for arbitrary source-bit
assignments. Thus no numbering, unused fair source, or hidden source
multiplicity is needed for the positive-minor proof.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryWitnessGeometry

open SelectedWalk BinaryCPT

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Literal adjacency in the main trace, restricted to the vertices
remaining after collider deletion. Its connected components are treks. -/
def TrekStep (g : BinaryWitnessGeometry V) (a b : V) : Prop :=
  g.ordinary a ∧ g.ordinary b ∧ (NextOn g.main a b ∨ NextOn g.main b a)

theorem trek_step_value (g : BinaryWitnessGeometry V) (bits : g.SourceIndex → Bool)
    {a b : V} (step : g.TrekStep a b) : g.circuit.value bits a = g.circuit.value bits b := by
  rcases step.2.2 with forward | backward
  · exact g.ordinary_adjacent_equal bits forward step.1.2 step.2.1.2
  · exact (g.ordinary_adjacent_equal bits backward step.2.1.2 step.1.2).symm

theorem trek_route_value (g : BinaryWitnessGeometry V) (bits : g.SourceIndex → Bool)
    {a b : V} {vertices : List V} (route : Route g.TrekStep a vertices b) :
    g.circuit.value bits a = g.circuit.value bits b := by
  induction route with
  | nil a => rfl
  | cons step tail ih => exact (g.trek_step_value bits step).trans ih

/-- This is the actual root of the original path component, reached by
repeated unique main-parent choices, not an arbitrary fresh random node. -/
theorem component_source_exists (g : BinaryWitnessGeometry V) (vertex : V)
    (ordinary : g.ordinary vertex) :
    ∃ i : g.SourceIndex, ∃ vertices, Route g.TrekStep i.val vertices vertex := by
  classical
  have descend : ∀ n, ∀ vertex, g.rank vertex = n → g.ordinary vertex →
      ∃ i : g.SourceIndex, ∃ vertices, Route g.TrekStep i.val vertices vertex := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro vertex rankEq ordinary
        by_cases parentExists : ∃ parent, MainParent g.arrow g.main parent vertex
        · obtain ⟨parent, parentOn⟩ := parentExists
          have parentOrdinary : g.ordinary parent :=
            ⟨mainParent_member g.arrow parentOn,
              mainParent_ordinary g.arrow g.acyclic g.simple parentOn⟩
          have earlier := g.rank_strict parentOn.2
          obtain ⟨i, vertices, route⟩ := ih (g.rank parent) (by omega) parent rfl parentOrdinary
          exact ⟨i, vertices ++ [vertex], route.append
            (.cons ⟨parentOrdinary, ordinary, parentOn.1⟩ (.nil vertex))⟩
        · exact ⟨⟨vertex, ordinary.1, ordinary.2, parentExists⟩, [], .nil vertex⟩
  exact descend (g.rank vertex) vertex rfl ordinary

theorem source_unique_in_component (g : BinaryWitnessGeometry V) (i j : g.SourceIndex)
    {vertex : V} {fromI fromJ : List V}
    (first : Route g.TrekStep i.val fromI vertex) (second : Route g.TrekStep j.val fromJ vertex) : i = j := by
  classical
  by_contra different
  let bits : g.SourceIndex → Bool := fun k => if k = i then true else false
  have equalBits : bits i = bits j := by
    rw [← g.circuit.value_at_source bits i, ← g.circuit.value_at_source bits j]
    exact (g.trek_route_value bits first).trans (g.trek_route_value bits second).symm
  simp only [bits, if_pos rfl, if_neg different.symm] at equalBits
  cases equalBits

theorem component_has_unique_source (g : BinaryWitnessGeometry V) (vertex : V)
    (ordinary : g.ordinary vertex) :
    ∃! i : g.SourceIndex, ∃ vertices, Route g.TrekStep i.val vertices vertex := by
  obtain ⟨i, vertices, route⟩ := g.component_source_exists vertex ordinary
  refine ⟨i, ⟨vertices, route⟩, ?_⟩
  intro j reachable
  obtain ⟨other, second⟩ := reachable
  exact g.source_unique_in_component j i second route

theorem endpoint_copies_its_component_source (g : BinaryWitnessGeometry V)
    (bits : g.SourceIndex → Bool) (vertex : V) (ordinary : g.ordinary vertex) :
    ∃ i : g.SourceIndex, (∃ vertices, Route g.TrekStep i.val vertices vertex) ∧
      g.circuit.value bits vertex = bits i := by
  obtain ⟨i, vertices, route⟩ := g.component_source_exists vertex ordinary
  refine ⟨i, ⟨vertices, route⟩, ?_⟩
  exact (g.trek_route_value bits route).symm.trans (g.circuit.value_at_source bits i)

end RestrictedCausal.ProbabilitySource.BinaryWitnessGeometry
