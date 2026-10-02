import G5ParentChoiceCalendar
import G5OriginalCoinPMF

/-!
# Actual current hybrid-port support and fair original-source pushforward

Contributor: dot, 2026-10-02. Both original parent occurrences exhaust the
binary hybrid's incoming edges. Every actual component path therefore ends
with one of them, and its active population is the constructed parent-position
map. The full root-route support equals that map's image. Distinct original
finite source sites then have the genuine fair-selector co-occupancy law for
these actual graph/calendar positions. Entire safe-past disjointness and the
continuous trace/observed chronology remain separate.
-/
namespace GProgram.G5.ParentCalendar
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentSupport
open GProgram.G5.OriginalCoinLaw
open GProgram.G5.QuartetKernel
open scoped ENNReal NNReal Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Original indegree TWO and the supplied distinct parent occurrences exhaust
all actual incoming edges, including parallel arcs. -/
theorem incoming_edge_is_original_parent {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {e : E}
    (ht : N.graph.target e = H.hybrid) : ∃ b : Bool, H.parent b = e := by
  classical
  let incoming : Finset E := Finset.univ.filter (fun f => N.graph.target f = H.hybrid)
  have hsub : ({H.parent0,H.parent1} : Finset E) ⊆ incoming := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · simp [incoming,H.target0]
    · simp [incoming,H.target1]
  have hc : incoming.card ≤ ({H.parent0,H.parent1} : Finset E).card := by
    rw [Finset.card_pair H.different]
    exact le_of_eq H.isHybrid.1
  have heq := Finset.eq_of_subset_of_card_le hsub hc
  have hem : e ∈ ({H.parent0,H.parent1} : Finset E) := by
    rw [heq]
    simp [incoming,ht]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hem
  rcases hem with h | h
  · exact ⟨false,h.symm⟩
  · exact ⟨true,h.symm⟩

/-- Any nonempty original edge-ID path has an actual final incoming edge. -/
theorem EdgePath.empty_or_last {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : GProgram.G5.EdgePath G a b es) :
    es = [] ∨ ∃ pre e, es = pre ++ [e] ∧ G.target e = b := by
  have hp := GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse
    (keep := fun _ => True) p (fun _ _ => trivial)
  cases hr : es.reverse with
  | nil => exact Or.inl (List.reverse_inj.mp (by simpa using hr))
  | cons e rest =>
    rw [hr] at hp
    cases hp with
    | cons ht _ _ =>
      exact Or.inr ⟨rest.reverse,e,by
        have heq := congrArg List.reverse hr
        simpa only [List.reverse_reverse,List.reverse_cons] using heq,ht⟩

/-- The actual component support is exactly the image of the ORIGINAL parent
bit current-position map, including coincidence above a joining point. -/
theorem activeComponentEdges_eq_parentPosition_image {N : RootedBinary V E X}
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) :
    activeComponentEdges N.graph C entry H.hybrid t =
      Finset.univ.image (parentPosition C H he hl hu) := by
  classical
  ext f
  rw [mem_activeComponentEdges_iff,Finset.mem_image]
  constructor
  · rintro ⟨es,hp,_,hf,ha⟩
    rcases GProgram.G5.ParentCalendar.EdgePath.empty_or_last hp with hnil | ⟨pre,e,hes,hte⟩
    · rw [hnil] at hf
      simp at hf
    · obtain ⟨b,hbe⟩ := incoming_edge_is_original_parent H hte
      subst e
      rw [hes] at hp hf
      exact ⟨b,Finset.mem_univ _,(active_edge_eq_parentPosition C hcut H he hl hu b hp hf ha).symm⟩
  · rintro ⟨b,_,rfl⟩
    exact ⟨parentRoute H he b,parentRoute_path H he b,parentRoute_nonbridge H he b,
      (parentPosition_spec C H he hl hu b).1,(parentPosition_spec C H he hl hu b).2⟩

/-- The exact parent image also describes ALL complete original root routes. -/
theorem activeRootRouteEdges_eq_parentPosition_image {N : RootedBinary V E X}
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) :
    activeRootRouteEdges N.graph C N.root H.hybrid t =
      Finset.univ.image (parentPosition C H he hl hu) := by
  trans activeComponentEdges N.graph C entry H.hybrid t
  · rcases he with ⟨rfl,hb⟩ | ⟨e,hbridge,rfl,hb⟩
    · exact activeRootRouteEdges_eq_root_component N C hb t
    · exact activeRootRouteEdges_eq_component N C hbridge hb hu
  · exact activeComponentEdges_eq_parentPosition_image C hcut H he hl hu

/-- Genuine source PMF co-occupancy for actual graph/calendar parent positions.
The sites are distinct ORIGINAL source coordinates; safe chronology must still
justify that condition for the retained original representatives. -/
theorem actual_parent_position_fair_meeting_probability
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    {N : RootedBinary V E X} (C : Calendar N.graph)
    (H K : GProgram.G2.OriginalHybridParents N) {entryH entryK : V}
    (heH : IsComponentEntryFor N entryH H.hybrid)
    (heK : IsComponentEntryFor N entryK K.hybrid) {t : ℝ}
    (hlH : C.age H.hybrid ≤ t) (huH : t < C.age entryH)
    (hlK : C.age K.hybrid ≤ t) (huK : t < C.age entryK)
    {u v : Site} (hne : u ≠ v) :
    (independentPMF (1 / 2) (by norm_num) (by norm_num)).toOuterMeasure
      {coin : Site → Bool |
        parentPosition C H heH hlH huH (coin u) =
          parentPosition C K heK hlK huK (coin v)} =
      fairMeetingMass (binaryPositions (parentPosition C H heH hlH huH))
        (binaryPositions (parentPosition C K heK hlK huK)) := by
  classical
  exact fair_source_meeting_probability hne _ _

#print axioms incoming_edge_is_original_parent
#print axioms EdgePath.empty_or_last
#print axioms activeComponentEdges_eq_parentPosition_image
#print axioms activeRootRouteEdges_eq_parentPosition_image
#print axioms actual_parent_position_fair_meeting_probability
end GProgram.G5.ParentCalendar
