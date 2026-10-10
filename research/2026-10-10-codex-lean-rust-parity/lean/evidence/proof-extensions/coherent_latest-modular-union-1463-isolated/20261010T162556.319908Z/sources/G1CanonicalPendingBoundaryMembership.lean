import G1CanonicalPendingActorSets

/-! Every private ORIGINAL node/exit is assigned to an ACTUALLY pending
runtime actor at that precise batch position. Coincident dates and arbitrary
many actors are handled by literal cut identity and unchanged source order. -/
namespace G1CanonicalPendingBoundaryMembership
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1PrivateActorLifetimeAdmission
open G1OriginalSpanRegion G1OriginalActorTemporalFootprint G1CanonicalPendingActorSets
open G1ActiveCoreBridgeCohorts
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- All actors at the original node batch have already opened after its exits.
Every private node belongs to one of those actual current pending slots. -/
theorem actual_original_owned_node_is_active (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (node : O.Vertex) (actor : BridgeActor T) (howner : nodeActorOwner O H D hD node = some actor) :
    actor ∈ afterOpeningActors T (O.calendar.age node) := by
  have hm := actual_owned_node_member O H D hD node actor howner
  have hb := actual_span_node_temporal_bounds O (bridgeSpan O T D actor.val actor.property) node hm
  simp only [afterOpeningActors,Finset.mem_filter,Finset.mem_univ,true_and,Calendar.Active,D.calendar]
  exact hb

/-- An original private exit always precedes its actor close. If its upper
age is this date, it MUST be that one final cut, so source-site uniqueness
prevents this slot from having closed earlier in the same batch. -/
theorem actual_original_owned_exit_is_pending (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (date : ℝ) (processed : List O.Edge) (edge : O.Edge)
    (hprocessed : ∀ e ∈ processed, O.calendar.age (O.network.graph.source e) = date)
    (hdate : O.calendar.age (O.network.graph.source edge) = date) (hnew : edge ∉ processed)
    (actor : BridgeActor T) (howner : eventActor O H D hD (.exit edge) = some actor) :
    actor ∈ afterExitActors O H D hD date processed := by
  have hm := actual_owned_exit_member O H D hD edge actor howner
  have hb := actual_span_exit_temporal_bounds O (bridgeSpan O T D actor.val actor.property) edge hm
  have hupper : date ≤ O.calendar.age (D.vertex (T.network.graph.source actor.val)) := hdate ▸ hb.2
  have hnot : actorCut O H D hD actor ∉ processed := by
    intro hc
    have hcutdate := hprocessed _ hc
    rw [actual_actor_cut_source] at hcutdate
    have heq : edge = actorCut O H D hD actor := actual_only_last_exit_at_end_date O _ _
      (actual_actor_cut_ends_at O H D hD actor) edge hm (hdate.trans hcutdate.symm)
    exact hnew (heq.symm ▸ hc)
  simp only [afterExitActors,beforeExitActors,Finset.mem_filter,Finset.mem_univ,true_and,D.calendar]
  exact ⟨⟨hdate ▸ hb.1,hupper⟩,hnot⟩

/-- Distinct pre-exit pending actors have disjoint ORIGINAL descendant cohorts,
including arbitrary coincident upper dates. A real common interior time is
constructed from their two lower dates; no uniform witness-time field. -/
theorem actual_before_exit_pending_cohorts_disjoint (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (date : ℝ) (first second : BridgeActor T) (hne : first ≠ second)
    (hf : first ∈ beforeExitActors T date) (hs : second ∈ beforeExitActors T date)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) :
    Disjoint (originalInsideCopies O sample (actorInput O D first))
      (originalInsideCopies O sample (actorInput O D second)) := by
  obtain ⟨hfl,hfu⟩ := (Finset.mem_filter.mp hf).2
  obtain ⟨hsl,hsu⟩ := (Finset.mem_filter.mp hs).2
  let time := max (T.calendar.age (T.network.graph.target first.val)) (T.calendar.age (T.network.graph.target second.val))
  have ht : time < date := max_lt hfl hsl
  have ha : T.calendar.Active time first.val := ⟨le_max_left _ _,ht.trans_le hfu⟩
  have hb : T.calendar.Active time second.val := ⟨le_max_right _ _,ht.trans_le hsu⟩
  exact actual_active_originated_original_cohorts_disjoint O H D hD first.val second.val first.property second.property
    (fun he => hne (Subtype.ext he)) time ha hb sample

#print axioms actual_original_owned_exit_is_pending
#print axioms actual_before_exit_pending_cohorts_disjoint
end G1CanonicalPendingBoundaryMembership
