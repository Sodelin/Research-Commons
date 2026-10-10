import GraphCuts

/-!
# Actual-source child-bridge graph component of G5

New proof contribution: the dot dedicated Lean lane, 2026-10-01.
The imported edge-indexed graph API and its foundations retain the original
Samuel Alexander research attribution and exact source baseline.

This file proves a graph theorem on the actual finite rooted binary source.
Parallel edge IDs are retained. There is no bounded-source replacement and
no canonical shape, switching-support, or desired biological conclusion in
the premises. The calendar/no-merger support and chronological lifting
parts of G5 are separate proof obligations.
-/

namespace GProgram.G5

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- The component below an actual directed bridge consists exactly of its
target's directed descendants. This is independent of inheritance mode. -/
theorem bridge_target_component_iff_descendant (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) (v : V) :
    N.graph.ReachWithout e (N.graph.target e) v ↔
      N.graph.DReach (N.graph.target e) v := by
  constructor
  · intro hv
    by_contra hn
    have hr := N.graph.dreach_without_of_no_return e (N.rooted v) hn
    have hs := (N.root_on_source_side e).trans hr
    exact N.graph.bridge_sides_disjoint he hs hv
  · intro hv
    exact N.graph.dreach_preserves
      (fun _ _ hstep hmem => N.graph.bridge_target_forward_closed he hstep hmem)
      hv (.refl)

/-- On the original source, a selected tip is in the child component iff it
descends from the child. No pruned selected-tip source is introduced. -/
theorem bridge_selected_tip_iff (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) (x : X) :
    N.graph.ReachWithout e (N.graph.target e) (N.leaf x) ↔
      N.graph.DReach (N.graph.target e) (N.leaf x) :=
  bridge_target_component_iff_descendant N he (N.leaf x)

/-- A one-child vertex has exactly one outgoing original edge identity. -/
theorem unique_child_edge (N : RootedBinary V E X) {h : V}
    (hh : N.graph.outDegree h = 1) :
    ∃! e : E, N.graph.source e = h := by
  classical
  obtain ⟨e, he, hu⟩ := Finset.card_eq_one_iff_existsUnique.mp hh
  refine ⟨e, (Finset.mem_filter.mp he).2, ?_⟩
  intro f hf
  exact hu f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf⟩)

/-- Every genuine descendant other than the one-child vertex itself is
already a descendant of the target of its unique child edge. -/
theorem descendant_via_unique_child (N : RootedBinary V E X)
    {h v : V} (hh : N.graph.outDegree h = 1) {e : E}
    (hs : N.graph.source e = h) (hne : h ≠ v) :
    N.graph.DReach h v ↔ N.graph.DReach (N.graph.target e) v := by
  obtain ⟨f, hf, hu⟩ := unique_child_edge N hh
  have hfe : f = e := (hu e hs).symm
  subst f
  constructor
  · intro hv
    rcases Relation.ReflTransGen.cases_head hv with heq | ⟨u, hstep, huv⟩
    · exact False.elim (hne heq)
    · obtain ⟨g, hgs, hgt⟩ := hstep
      have hge := hu g hgs
      subst g
      simpa only [EdgeGraph.DReach, hgt] using huv
  · intro hv
    exact (Relation.ReflTransGen.single ⟨e, hs, rfl⟩).trans hv

/-- The selected descendants of a hybrid are precisely its child-bridge
component, when the actual source cut-child condition is supplied. -/
theorem hybrid_descendant_component (N : RootedBinary V E X)
    {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e) (x : X) :
    N.graph.DReach h (N.leaf x) ↔
      N.graph.ReachWithout e (N.graph.target e) (N.leaf x) := by
  have hne : h ≠ N.leaf x := by
    intro heq
    have hz := (N.leaf_degrees x).2
    rw [← heq, hh.2] at hz
    cases hz
  rw [descendant_via_unique_child N hh.2 hs hne]
  exact (bridge_selected_tip_iff N he x).symm

#print axioms bridge_target_component_iff_descendant
#print axioms unique_child_edge
#print axioms descendant_via_unique_child
#print axioms hybrid_descendant_component

end GProgram.G5
