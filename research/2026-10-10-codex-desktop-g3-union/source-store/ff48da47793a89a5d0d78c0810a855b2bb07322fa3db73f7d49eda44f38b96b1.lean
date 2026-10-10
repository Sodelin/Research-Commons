import G1CanonicalOriginalActorOpening

/-! Closing updates the actual pending family/base complement exactly. The
whole ORIGINAL actor panel is delivered at its literal last cut; every other
held actor remains private. This includes arbitrary coincident closings. -/
namespace G1CanonicalOriginalActorClosing
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1ActiveCoreBridgeCohorts G1ActualFinitePanelProgramTensor G1CanonicalFiniteActiveEpochAdmission
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1InitializedFrontierPrefix
open G1ActualOriginalPrivateAsyncStep G1ActualOriginalOpenCloseAsyncInterface G1PendingActorInterfaceCommutation
open G1CanonicalOriginalActorOpening G1CanonicalPendingActorSets G1CanonicalPendingBoundaryMembership
open G1ActualFinalCutCloseAdmission
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_original_slots_remove (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (actors : List (BridgeActor T)) (actor : BridgeActor T) :
    originalPendingSlots O D sample (actors.filter (fun other => decide (other ≠ actor))) =
      Function.update (originalPendingSlots O D sample actors) actor ∅ := by
  funext other
  by_cases he : other = actor
  · subst other; simp [originalPendingSlots]
  · simp [originalPendingSlots,he]

lemma actual_original_base_remove (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (actors : List (BridgeActor T)) (actor : BridgeActor T)
    (hm : actor ∈ actors)
    (hdis : ∀ other ∈ actors, other ≠ actor → Disjoint (originalInsideCopies O sample (actorInput O D actor))
      (originalInsideCopies O sample (actorInput O D other))) :
    activeOriginalBase O D sample (actors.filter (fun other => decide (other ≠ actor))) =
      originalInsideCopies O sample (actorInput O D actor) ∪ activeOriginalBase O D sample actors := by
  ext x
  simp only [activeOriginalBase,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union]
  constructor
  · intro hn
    by_cases hx : x ∈ originalInsideCopies O sample (actorInput O D actor)
    · exact Or.inl hx
    · right
      intro hold
      obtain ⟨keep,hk,hxk⟩ := (actual_panel_union_member _ x).mp hold
      obtain ⟨other,ho,rfl⟩ := List.mem_map.mp hk
      by_cases he : other = actor
      · subst other; exact hx hxk
      · apply hn
        exact (actual_panel_union_member _ x).mpr ⟨_,List.mem_map.mpr ⟨other,List.mem_filter.mpr ⟨ho,decide_eq_true he⟩,rfl⟩,hxk⟩
  · rintro (hx | hn)
    · intro hold
      obtain ⟨keep,hk,hxk⟩ := (actual_panel_union_member _ x).mp hold
      obtain ⟨other,ho,rfl⟩ := List.mem_map.mp hk
      have hf := List.mem_filter.mp ho
      exact Finset.disjoint_left.mp (hdis other hf.1 (of_decide_eq_true hf.2)) hx hxk
    · intro hold
      obtain ⟨keep,hk,hxk⟩ := (actual_panel_union_member _ x).mp hold
      obtain ⟨other,ho,rfl⟩ := List.mem_map.mp hk
      exact hn ((actual_panel_union_member _ x).mpr ⟨_,List.mem_map.mpr ⟨other,(List.mem_filter.mp ho).1,rfl⟩,hxk⟩)

lemma actual_pending_actor_base_disjoint (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (actors : List (BridgeActor T)) (actor : BridgeActor T)
    (hm : actor ∈ actors) : Disjoint (originalInsideCopies O sample (actorInput O D actor)) (activeOriginalBase O D sample actors) := by
  apply Finset.disjoint_left.mpr
  intro x hx hbase
  exact (Finset.mem_sdiff.mp hbase).2 ((actual_panel_union_member _ x).mpr
    ⟨_,List.mem_map.mpr ⟨actor,hm,rfl⟩,hx⟩)

/-- Actual real-prefix/cut support discharges close purity and the new runtime
base/slot shape. No source law, exit population or K equality is assumed by
the caller; the actor's opaque original descendants are delivered first. -/
theorem actual_canonical_original_actor_close_interface (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (actors : List (BridgeActor T)) (hm : actor ∈ actors)
    (hbefore : ∀ other ∈ actors, other ∈ beforeExitActors T (T.calendar.age (T.network.graph.source actor.val)))
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) {initial : Code O.network sample}
    (hs : initial ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.source actor.val)))) (initialCode O.network sample register)).support)
    (processed : List O.Edge) (hunclosed : actorCut O H D hD actor ∉ processed)
    {s : Code O.network sample}
    (hp : s ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support)
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r [.boundary (.exit (actorCut O H D hD actor))] s).support) :
    PMF.pure (originalAsyncProjection O
      (activeOriginalBase O D sample (actors.filter (fun other => decide (other ≠ actor))))
      (originalPendingSlots O D sample (actors.filter (fun other => decide (other ≠ actor)))) d) =
      asyncStep (.interface actor (originalCloseKernel (originalInsideCopies O sample (actorInput O D actor))))
        (originalAsyncProjection O (activeOriginalBase O D sample actors) (originalPendingSlots O D sample actors) d) := by
  rw [actual_original_slots_remove,actual_original_base_remove O D sample actors actor hm]
  · apply actual_canonical_final_cut_close_async_interface O H D hD actor sample register gamma common r hs
      processed hunclosed hp hd _ _ (actual_pending_actor_base_disjoint O D sample actors actor hm)
    simp [originalPendingSlots,hm]
  · intro other ho hne
    exact actual_before_exit_pending_cohorts_disjoint O H D hD _ actor other (Ne.symm hne)
      (hbefore actor hm) (hbefore other ho) sample

#print axioms actual_canonical_original_actor_close_interface
end G1CanonicalOriginalActorClosing
