import G5CalendarRoutes

/-!
# Exact protective population block on original no-merger route families

New proof contribution: dot's dedicated Lean lane, 2026-10-01.
This tests the stronger 'exact whole block' step in G5, rather than a claim
that descendants are merely possibly co-located or contained in a larger block.

A route family contains original-tip paths on the unchanged original source.
Its existence follows from source rootedness. No assumptions concerning the
desired population-block support, gene-law identifiability, or Q/S appear as
fields. Probability/support of these route families remains a separate task.
-/

namespace GProgram.G5

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

structure RouteFamily (N : RootedBinary V E X) where
  edges : X → List E
  valid : ∀ x, EdgePath N.graph N.root (N.leaf x) (edges x)

theorem routeFamily_exists (N : RootedBinary V E X) : Nonempty (RouteFamily N) := by
  classical
  exact ⟨⟨fun x => Classical.choose (original_tip_route_exists N x),
    fun x => Classical.choose_spec (original_tip_route_exists N x)⟩⟩

noncomputable def selectedPopulationBlock (N : RootedBinary V E X)
    (R : RouteFamily N) (B : Finset X) (C : Calendar N.graph) (t : ℝ) (e : E) :
    Finset X := by
  classical
  exact B.filter (fun x => e ∈ R.edges x ∧ C.Active t e)

noncomputable def selectedDescendants (N : RootedBinary V E X)
    (B : Finset X) (h : V) : Finset X := by
  classical
  exact B.filter (fun x => N.graph.DReach h (N.leaf x))

/-- At every protective calendar time, the child population's selected-tip
fiber is exactly the whole selected descendant set, for every original-route
assignment, even if different tips choose hybrid parents independently. -/
theorem protective_population_block_eq (N : RootedBinary V E X)
    (R : RouteFamily N) (B : Finset X) (C : Calendar N.graph)
    {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e) {t : ℝ}
    (ht : C.age (N.graph.target e) ≤ t ∧ t < C.age h) :
    selectedPopulationBlock N R B C t e = selectedDescendants N B h := by
  classical
  apply Finset.filter_congr
  intro x _
  constructor
  · intro hmem
    exact (Relation.ReflTransGen.single ⟨e, hs, rfl⟩).trans
      ((R.valid x).target_reaches_end_of_mem hmem.1)
  · intro hd
    have hp := protective_edge_active_on_every_route N C hh hs he hd (R.valid x) ht
    exact ⟨hp.1, hp.2.1⟩

#print axioms routeFamily_exists
#print axioms protective_population_block_eq

end GProgram.G5
