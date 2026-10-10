import G5ActualComponentSupport

/-!
# Complete original root routes induce the actual current component support

Contributor: dot, 2026-10-02. The active support is defined using every complete
original root-to-port path. Its equality with the nonbridge component support
is proved using the actual incoming bridge and strictly positive clocks. The
resulting bound comes from original binary cut-child degrees, with original
parallel edge occurrences retained. No stochastic coin law or observation
chronology is asserted here.
-/
namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentCalendar
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Current original population support over all complete original routes. -/
noncomputable def activeRootRouteEdges (G : EdgeGraph V E) (C : Calendar G)
    (root port : V) (t : ℝ) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ∃ es : List E,
    EdgePath G root port es ∧ e ∈ es ∧ C.Active t e)

theorem mem_activeRootRouteEdges_iff (G : EdgeGraph V E) (C : Calendar G)
    (root port : V) (t : ℝ) (e : E) :
    e ∈ activeRootRouteEdges G C root port t ↔ ∃ es : List E,
      EdgePath G root port es ∧ e ∈ es ∧ C.Active t e := by
  classical
  simp only [activeRootRouteEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every complete original route into an incoming bridge's actual component
contains that exact bridge occurrence. -/
theorem incoming_bridge_mem_root_route (N : RootedBinary V E X)
    {entry : E} (he : N.graph.IsBridge entry) {port : V}
    (hb : N.graph.SameBlob (N.graph.target entry) port)
    {es : List E} (p : EdgePath N.graph N.root port es) : entry ∈ es := by
  by_contra hn
  have hsource : N.graph.ReachWithout entry (N.graph.source entry) port :=
    (N.root_on_source_side entry).trans (p.reach_without_of_not_mem hn)
  have htarget : N.graph.ReachWithout entry (N.graph.target entry) port :=
    GProgram.G5.ComponentEntries.sameBlob_avoids_bridge N.graph he hb
  exact N.graph.bridge_sides_disjoint he hsource htarget

/-- Before the component entry age, every active edge of a complete original
route lies on its actual all-nonbridge suffix. Prefixes and the entry bridge
are excluded by their original clocks. -/
theorem active_root_edge_has_nonbridge_suffix (N : RootedBinary V E X)
    (C : Calendar N.graph) {entry : E} (he : N.graph.IsBridge entry)
    {port : V} (hb : N.graph.SameBlob (N.graph.target entry) port)
    {es : List E} (p : EdgePath N.graph N.root port es)
    {t : ℝ} (hu : t < C.age (N.graph.target entry)) {f : E}
    (hf : f ∈ es) (ha : C.Active t f) :
    ∃ post : List E, EdgePath N.graph (N.graph.target entry) port post ∧
      (∀ g ∈ post, ¬N.graph.IsBridge g) ∧ f ∈ post := by
  have hem := incoming_bridge_mem_root_route N he hb p
  obtain ⟨pre,post,hes,hpre,hpost⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge p hem
  refine ⟨post,hpost,
    GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob N.root
      N.acyclic N.rooted hpost hb,?_⟩
  rw [hes] at hf
  rcases List.mem_append.mp hf with hp | hp
  · have hage : C.age (N.graph.source entry) ≤ C.age (N.graph.target f) :=
      C.age_le_of_directed (hpre.target_reaches_end_of_mem hp)
    have hlt : t < C.age (N.graph.target f) :=
      hu.trans ((C.edge_older entry).trans_le hage)
    exact False.elim (not_le_of_gt hlt ha.1)
  · rcases List.mem_cons.mp hp with h | hp
    · subst f
      exact False.elim (not_le_of_gt hu ha.1)
    · exact hp

/-- Exact equality: complete original root-route support equals the support
of actual component paths in an incoming-entry calendar interval. -/
theorem activeRootRouteEdges_eq_component (N : RootedBinary V E X)
    (C : Calendar N.graph) {entry : E} (he : N.graph.IsBridge entry)
    {port : V} (hb : N.graph.SameBlob (N.graph.target entry) port)
    {t : ℝ} (hu : t < C.age (N.graph.target entry)) :
    activeRootRouteEdges N.graph C N.root port t =
      activeComponentEdges N.graph C (N.graph.target entry) port t := by
  classical
  ext f
  rw [mem_activeRootRouteEdges_iff, mem_activeComponentEdges_iff]
  constructor
  · rintro ⟨es,hp,hmem,hactive⟩
    obtain ⟨post,hpost,hkeep,hf⟩ :=
      active_root_edge_has_nonbridge_suffix N C he hb hp hu hmem hactive
    exact ⟨post,hpost,hkeep,hf,hactive⟩
  · rintro ⟨post,hpost,_,hf,hactive⟩
    obtain ⟨pre,hpre⟩ := exists_edgePath_of_directed (N.rooted (N.graph.source entry))
    have hentry : EdgePath N.graph (N.graph.source entry) (N.graph.target entry) [entry] :=
      .cons rfl (.nil _)
    exact ⟨pre ++ [entry] ++ post,(hpre.append hentry).append hpost,
      List.mem_append_right _ hf,hactive⟩

/-- Root-component routes are themselves all-nonbridge paths. -/
theorem activeRootRouteEdges_eq_root_component (N : RootedBinary V E X)
    (C : Calendar N.graph) {port : V} (hb : N.graph.SameBlob N.root port) (t : ℝ) :
    activeRootRouteEdges N.graph C N.root port t =
      activeComponentEdges N.graph C N.root port t := by
  classical
  ext f
  rw [mem_activeRootRouteEdges_iff, mem_activeComponentEdges_iff]
  constructor
  · rintro ⟨es,hp,hf,ha⟩
    exact ⟨es,hp,GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob
      N.root N.acyclic N.rooted hp hb,hf,ha⟩
  · rintro ⟨es,hp,_,hf,ha⟩
    exact ⟨es,hp,hf,ha⟩

/-- Actual original complete-route current support is bounded by the current
component port's actual incoming edge-occurrence count. -/
theorem activeRootRouteEdges_card_le_indegree_of_entry
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {entry : E} (he : N.graph.IsBridge entry) {port : V}
    (hb : N.graph.SameBlob (N.graph.target entry) port) {t : ℝ}
    (hl : C.age port ≤ t) (hu : t < C.age (N.graph.target entry)) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ N.graph.inDegree port := by
  rw [activeRootRouteEdges_eq_component N C he hb hu]
  exact activeComponentEdges_card_le_indegree N C hcut hl hu

#print axioms incoming_bridge_mem_root_route
#print axioms active_root_edge_has_nonbridge_suffix
#print axioms activeRootRouteEdges_eq_component
#print axioms activeRootRouteEdges_eq_root_component
#print axioms activeRootRouteEdges_card_le_indegree_of_entry
end GProgram.G5.ComponentSupport
