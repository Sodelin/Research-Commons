import G1PendingInterfaceEntryRecorder

/-! The OWN opening interface's exact concrete position is derived from the
canonical original-site opening list. This uses the existing compiler and
pure original opaque-cohort open kernel, not a parallel runtime definition. -/
namespace G1CanonicalOwnOpeningRuntimePosition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalOriginalActorOpening G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalOpeningAsyncBatch
open G1ActualOriginalOpenCloseAsyncInterface G1CanonicalFiniteActiveEpochAdmission
open G1ActiveCoreBridgeCohorts
open G1OriginalCalendarDecomposition G1PendingActorInterfaceCommutation G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_opening_batch_list_split (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (actors first last : List (BridgeActor T)) :
    canonicalOpeningBatchOps O D sample actors (first ++ last) =
      canonicalOpeningBatchOps O D sample actors first ++
      canonicalOpeningBatchOps O D sample (actors ++ first) last := by
  induction first generalizing actors with
  | nil => simp [canonicalOpeningBatchOps]
  | cons actor first ih =>
    simp only [List.cons_append,canonicalOpeningBatchOps]
    rw [ih]
    simp only [List.append_assoc,List.singleton_append]

noncomputable def sourceOpenPrefix (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :=
  (canonicalOriginalOpeningActors O H D hD (O.calendar.age (actorInput O D actor))).takeWhile
    (fun other => decide (other ≠ actor))

noncomputable def sourceOpenSuffix (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :=
  ((canonicalOriginalOpeningActors O H D hD (O.calendar.age (actorInput O D actor))).dropWhile
    (fun other => decide (other ≠ actor))).tail

theorem actual_own_original_opening_list_cut (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T) :
    canonicalOriginalOpeningActors O H D hD (O.calendar.age (actorInput O D actor)) =
      sourceOpenPrefix O H D hD actor ++ [actor] ++ sourceOpenSuffix O H D hD actor := by
  apply original_exit_list_cut
  apply (actual_original_opening_actor_membership O H D hD _ actor).mpr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  simp only [actorInput,D.calendar]

/-- Concrete OWN opening interface position, including the exact original
base cohort after earlier same-date openings. Coincident actor dates use the
compiler's own original site order; no output or lifecycle oracle is supplied. -/
theorem actual_own_original_opening_runtime_cut (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (actor : BridgeActor T) (actors : List (BridgeActor T)) :
    canonicalOpeningBatchOps O D sample actors
      (canonicalOriginalOpeningActors O H D hD (O.calendar.age (actorInput O D actor))) =
      canonicalOpeningBatchOps O D sample actors (sourceOpenPrefix O H D hD actor) ++
      [AsyncOperation.interface actor (originalOpenKernel (originalInsideCopies O sample (actorInput O D actor))
        (activeOriginalBase O D sample (actors ++ sourceOpenPrefix O H D hD actor)))] ++
      canonicalOpeningBatchOps O D sample ((actors ++ sourceOpenPrefix O H D hD actor) ++ [actor])
        (sourceOpenSuffix O H D hD actor) := by
  rw [actual_own_original_opening_list_cut,actual_opening_batch_list_split,actual_opening_batch_list_split]
  simp only [canonicalOpeningBatchOps,List.append_nil,List.cons_append,List.nil_append,List.append_assoc]

#print axioms actual_own_original_opening_runtime_cut
end G1CanonicalOwnOpeningRuntimePosition
