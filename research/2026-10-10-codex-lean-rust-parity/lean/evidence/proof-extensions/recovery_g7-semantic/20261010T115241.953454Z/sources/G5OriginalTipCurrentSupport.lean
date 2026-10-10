import G5CurrentPortTwoPositions

/-!
# Actual original-tip support above an exit bridge equals port support

Contributor: dot, 2026-10-02. An original bridge separating a selected tip from
its older component is present on every complete original tip route. At ages
at least its source-port age, all younger route suffix populations are inactive.
Thus the actual original-tip population support equals actual port support,
and the binary cut-child two-position result applies to original tips. No
conditioning on merger survival or stochastic coin law is involved.
-/
namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Above an actual exit bridge's source age, an active original-tip edge must
belong to the complete original root-to-port prefix. -/
theorem active_tip_edge_has_root_port_prefix
    (N : RootedBinary V E X) (C : Calendar N.graph)
    {exit : E} (he : N.graph.IsBridge exit) {x : X}
    (hd : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {es : List E} (p : EdgePath N.graph N.root (N.leaf x) es)
    {t : ℝ} (hl : C.age (N.graph.source exit) ≤ t) {f : E}
    (hf : f ∈ es) (ha : C.Active t f) :
    ∃ pre : List E, EdgePath N.graph N.root (N.graph.source exit) pre ∧ f ∈ pre := by
  have hem := bridge_mem_every_descendant_route N he p hd
  obtain ⟨pre,post,hes,hpre,hpost⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge p hem
  refine ⟨pre,hpre,?_⟩
  rw [hes] at hf
  rcases List.mem_append.mp hf with hp | hp
  · exact hp
  · rcases List.mem_cons.mp hp with h | hp
    · subst f
      exact False.elim (not_lt_of_ge hl ha.2)
    · have hage : C.age (N.graph.source f) ≤ C.age (N.graph.target exit) :=
        hpost.source_age_le C hp
      have hle : C.age (N.graph.source f) ≤ t :=
        hage.trans ((le_of_lt (C.edge_older exit)).trans hl)
      exact False.elim (not_lt_of_ge hle ha.2)

/-- Exact source support equality for an original tip and its fixed actual
exit-bridge port throughout the older component calendar interval. -/
theorem original_tip_support_eq_port
    (N : RootedBinary V E X) (C : Calendar N.graph)
    {exit : E} (he : N.graph.IsBridge exit) {x : X}
    (hd : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {t : ℝ} (hl : C.age (N.graph.source exit) ≤ t) :
    activeRootRouteEdges N.graph C N.root (N.leaf x) t =
      activeRootRouteEdges N.graph C N.root (N.graph.source exit) t := by
  classical
  ext f
  rw [mem_activeRootRouteEdges_iff, mem_activeRootRouteEdges_iff]
  constructor
  · rintro ⟨es,hp,hf,ha⟩
    obtain ⟨pre,hpre,hmem⟩ := active_tip_edge_has_root_port_prefix N C he hd hp hl hf ha
    exact ⟨pre,hpre,hmem,ha⟩
  · rintro ⟨pre,hpre,hf,ha⟩
    obtain ⟨post,hpost⟩ := exists_edgePath_of_directed hd
    have hexit : EdgePath N.graph (N.graph.source exit) (N.graph.target exit) [exit] :=
      .cons rfl (.nil _)
    exact ⟨pre ++ ([exit] ++ post),hpre.append (hexit.append hpost),
      List.mem_append_left _ hf,ha⟩

/-- The actual original-tip current population support is nonempty and has at
most two original edge occurrences in its exit port's current component. -/
theorem original_tip_current_support_nonempty_card_le_two
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {exit : E} (he : N.graph.IsBridge exit) {x : X}
    (hd : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {t : ℝ} (ht : InCurrentComponentInterval N C (N.graph.source exit) t) :
    (activeRootRouteEdges N.graph C N.root (N.leaf x) t).Nonempty ∧
      (activeRootRouteEdges N.graph C N.root (N.leaf x) t).card ≤ 2 := by
  rw [original_tip_support_eq_port N C he hd ht.1]
  exact ⟨current_port_support_nonempty N C ht,current_port_support_card_le_two N C hcut ht⟩

/-- During an actual exit-bridge population interval, every original tip below
that bridge has precisely that one original population in its route support. -/
theorem original_tip_bridge_support_eq_singleton
    (N : RootedBinary V E X) (C : Calendar N.graph)
    {exit : E} (he : N.graph.IsBridge exit) {x : X}
    (hd : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {t : ℝ} (ht : C.Active t exit) :
    activeRootRouteEdges N.graph C N.root (N.leaf x) t = {exit} := by
  classical
  ext f
  rw [mem_activeRootRouteEdges_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨es,hp,hf,ha⟩
    exact hp.active_unique C hf (bridge_mem_every_descendant_route N he hp hd) ha ht
  · intro hf
    subst f
    obtain ⟨es,hp⟩ := original_tip_route_exists N x
    exact ⟨es,hp,bridge_mem_every_descendant_route N he hp hd,ht⟩

#print axioms active_tip_edge_has_root_port_prefix
#print axioms original_tip_support_eq_port
#print axioms original_tip_current_support_nonempty_card_le_two
#print axioms original_tip_bridge_support_eq_singleton
end GProgram.G5.ComponentSupport
