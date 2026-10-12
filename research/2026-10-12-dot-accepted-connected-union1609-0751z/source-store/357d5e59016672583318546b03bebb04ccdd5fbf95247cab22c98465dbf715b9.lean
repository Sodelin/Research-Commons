import G5OriginalTipCurrentSupport

/-!
# Original hybrid parent occurrence determines its entire current calendar route

Contributor: dot, 2026-10-02. Component entries are actual original roots or
actual incoming bridge targets. Each original hybrid parent occurrence admits
an all-nonbridge route from that entry; the binary cut-child graph uniquely
fixes it once the last original parent is specified. Strict clocks then give
one actual current population for each parent bit. No stochastic probability
or source-observation chronology is an interface field here.
-/
namespace GProgram.G5.ParentCalendar
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentSupport
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Actual entry into the bridge-deleted component of a specified port. -/
def IsComponentEntryFor (N : RootedBinary V E X) (entry port : V) : Prop :=
  (entry = N.root ∧ N.graph.SameBlob N.root port) ∨
    ∃ e : E, N.graph.IsBridge e ∧ entry = N.graph.target e ∧
      N.graph.SameBlob (N.graph.target e) port

theorem component_entry_sameBlob (N : RootedBinary V E X) {entry port : V}
    (he : IsComponentEntryFor N entry port) : N.graph.SameBlob entry port := by
  rcases he with ⟨rfl,hb⟩ | ⟨e,_,rfl,hb⟩ <;> exact hb

/-- Rootedness and actual incoming-bridge connectivity imply a directed route
from the component entry to every vertex in that same component. -/
theorem component_entry_reaches_sameBlob (N : RootedBinary V E X)
    {entry port v : V} (he : IsComponentEntryFor N entry port)
    (hb : N.graph.SameBlob entry v) : N.graph.DReach entry v := by
  rcases he with ⟨rfl,_⟩ | ⟨e,hbridge,rfl,_⟩
  · exact N.rooted v
  · exact (GProgram.G5.Minimal.bridge_component_iff_descendant N.graph N.root
      N.acyclic N.rooted hbridge v).mp
        (GProgram.G5.ComponentEntries.sameBlob_avoids_bridge N.graph hbridge hb)

theorem original_parent_nonbridge {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (b : Bool) :
    ¬N.graph.IsBridge (H.parent b) := by
  cases b
  · exact (GProgram.G6.BridgeEntry.original_hybrid_parents_nonbridge H).1
  · exact (GProgram.G6.BridgeEntry.original_hybrid_parents_nonbridge H).2

theorem original_parent_target {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (b : Bool) :
    N.graph.target (H.parent b) = H.hybrid := by
  cases b
  · exact H.target0
  · exact H.target1

/-- Every actual original parent occurrence admits an all-nonbridge route
from the actual entry. Parallel incoming arcs remain distinct choices. -/
theorem parent_route_prefix_exists {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) :
    ∃ pre : List E, EdgePath N.graph entry (N.graph.source (H.parent b)) pre ∧
      (∀ f ∈ pre, ¬N.graph.IsBridge f) := by
  have hp := N.graph.nonbridge_sameBlob (original_parent_nonbridge H b)
  rw [original_parent_target H b] at hp
  have hb := (component_entry_sameBlob N he).trans (N.graph.sameBlob_symm hp)
  obtain ⟨pre,hpre⟩ := exists_edgePath_of_directed
    (component_entry_reaches_sameBlob N he hb)
  exact ⟨pre,hpre,GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob
    N.root N.acyclic N.rooted hpre hb⟩

noncomputable def parentRoutePrefix {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) : List E :=
  Classical.choose (parent_route_prefix_exists H he b)

noncomputable def parentRoute {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) : List E :=
  parentRoutePrefix H he b ++ [H.parent b]

theorem parentRoute_path {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) :
    EdgePath N.graph entry H.hybrid (parentRoute H he b) := by
  have hpre := (Classical.choose_spec (parent_route_prefix_exists H he b)).1
  have hparent : EdgePath N.graph (N.graph.source (H.parent b)) H.hybrid [H.parent b] :=
    .cons rfl (by rw [original_parent_target H b]; exact .nil _)
  exact hpre.append hparent

theorem parentRoute_nonbridge {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) :
    ∀ f ∈ parentRoute H he b, ¬N.graph.IsBridge f :=
  GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob N.root N.acyclic N.rooted
    (parentRoute_path H he b) (component_entry_sameBlob N he)

/-- The deterministic original cut-child graph fixes the entire path once its
last original parent occurrence is given. This is stronger than a support bound. -/
theorem parent_route_unique {N : RootedBinary V E X}
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool)
    {pre : List E} (hp : EdgePath N.graph entry H.hybrid (pre ++ [H.parent b])) :
    pre ++ [H.parent b] = parentRoute H he b := by
  have hk := GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob
    N.root N.acyclic N.rooted hp (component_entry_sameBlob N he)
  have p := GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hp hk
  have q := GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse
    (parentRoute_path H he b) (parentRoute_nonbridge H he b)
  simp only [parentRoute, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append] at p q
  have hrev := original_nonbridge_route_unique_of_first N hcut p q
  have heq := List.reverse_inj.mp hrev
  exact congrArg (fun xs => xs ++ [H.parent b]) heq

/-- A current actual population selected deterministically by one ORIGINAL
parent coin, including coincidence of both choices above their joining point. -/
noncomputable def parentPosition {N : RootedBinary V E X}
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) (b : Bool) : E :=
  Classical.choose (GProgram.G5.ComponentCalendar.EdgePath.active_exists C
    (parentRoute_path H he b) hl hu)

theorem parentPosition_spec {N : RootedBinary V E X}
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) (b : Bool) :
    parentPosition C H he hl hu b ∈ parentRoute H he b ∧
      C.Active t (parentPosition C H he hl hu b) :=
  Classical.choose_spec (GProgram.G5.ComponentCalendar.EdgePath.active_exists C
    (parentRoute_path H he b) hl hu)

/-- Every other actual route with that last original parent has the same
current population. The result is valid for each switching, not in expectation. -/
theorem active_edge_eq_parentPosition {N : RootedBinary V E X}
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) (b : Bool)
    {pre : List E} (hp : EdgePath N.graph entry H.hybrid (pre ++ [H.parent b]))
    {f : E} (hf : f ∈ pre ++ [H.parent b]) (ha : C.Active t f) :
    f = parentPosition C H he hl hu b := by
  have hroute := parent_route_unique hcut H he b hp
  rw [hroute] at hf
  exact (parentRoute_path H he b).active_unique C hf
    (parentPosition_spec C H he hl hu b).1 ha (parentPosition_spec C H he hl hu b).2

#print axioms component_entry_reaches_sameBlob
#print axioms parent_route_prefix_exists
#print axioms parent_route_unique
#print axioms parentPosition_spec
#print axioms active_edge_eq_parentPosition
end GProgram.G5.ParentCalendar
