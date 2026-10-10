import G1ActualFinalCutCloseAdmission

/-! Canonical actual actor opening from the retained ORIGINAL base. All old
currently active cohorts are disjoint from a new descendant interface, so
all saved opaque input trees really reside in base before this open. -/
namespace G1CanonicalOriginalActorOpening
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1ActiveCoreBridgeCohorts G1ActualFinitePanelProgramTensor G1CanonicalFiniteActiveEpochAdmission
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler
open G1ActualOriginalPrivateAsyncStep G1ActualOriginalOpenCloseAsyncInterface G1PendingActorInterfaceCommutation
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalPendingSlots (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (actors : List (BridgeActor T)) : BridgeActor T → Finset Copy :=
  fun actor => if actor ∈ actors then originalInsideCopies O sample (actorInput O D actor) else ∅

lemma actual_original_slots_append_new (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (actors : List (BridgeActor T)) (actor : BridgeActor T) :
    originalPendingSlots O D sample (actors ++ [actor]) =
      Function.update (originalPendingSlots O D sample actors) actor (originalInsideCopies O sample (actorInput O D actor)) := by
  funext other
  by_cases h : other = actor
  · subst other; simp [originalPendingSlots]
  · simp [originalPendingSlots,h,Function.update_of_ne h]

lemma actual_original_base_append_new (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (actors : List (BridgeActor T)) (actor : BridgeActor T) :
    activeOriginalBase O D sample (actors ++ [actor]) =
      activeOriginalBase O D sample actors \ originalInsideCopies O sample (actorInput O D actor) := by
  unfold activeOriginalBase activeOriginalPanels
  rw [List.map_append,actual_panel_union_append]
  simp only [List.map_singleton,panelUnion,Finset.union_empty]
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union,not_or]

/-- The new original cohort is part of the retained base: it is disjoint
from every other physically active core bridge at this real opening date. -/
lemma actual_new_original_actor_cohort_in_base (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (actors : List (BridgeActor T)) (actor : BridgeActor T) (hnew : actor ∉ actors)
    (hactive : ∀ other ∈ actors, T.calendar.Active (T.calendar.age (T.network.graph.target actor.val)) other.val) :
    originalInsideCopies O sample (actorInput O D actor) ⊆ activeOriginalBase O D sample actors := by
  intro x hx
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro hold
  obtain ⟨keep,hkeep,hxkeep⟩ := (actual_panel_union_member _ x).mp hold
  obtain ⟨other,ho,rfl⟩ := List.mem_map.mp hkeep
  have hne : actor.val ≠ other.val := by
    intro h
    exact hnew ((Subtype.ext h).symm ▸ ho)
  have hd := actual_active_originated_original_cohorts_disjoint O H D hD actor.val other.val actor.property other.property hne
    (T.calendar.age (T.network.graph.target actor.val)) ⟨le_rfl,T.calendar.edge_older actor.val⟩ (hactive other ho) sample
  exact Finset.disjoint_left.mp hd hx hxkeep

/-- The original pending-state open executes at the ACTUAL base interface.
Its subset/opaque-input admission is source-derived, not a supplied kernel
or source-output equality. All previously held outputs remain unobserved. -/
theorem actual_canonical_original_actor_open_interface (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (s : Code O.network sample) (actors : List (BridgeActor T)) (actor : BridgeActor T) (hnew : actor ∉ actors)
    (hactive : ∀ other ∈ actors, T.calendar.Active (T.calendar.age (T.network.graph.target actor.val)) other.val) :
    PMF.pure (originalAsyncProjection O (activeOriginalBase O D sample (actors ++ [actor]))
      (originalPendingSlots O D sample (actors ++ [actor])) s) =
      asyncStep (.interface actor (originalOpenKernel (originalInsideCopies O sample (actorInput O D actor))
        (activeOriginalBase O D sample actors)))
        (originalAsyncProjection O (activeOriginalBase O D sample actors) (originalPendingSlots O D sample actors) s) := by
  rw [actual_original_base_append_new,actual_original_slots_append_new]
  exact actual_original_open_async_interface O s actor _ _ _
    (actual_new_original_actor_cohort_in_base O H D hD sample actors actor hnew hactive)

#print axioms actual_canonical_original_actor_open_interface
end G1CanonicalOriginalActorOpening
