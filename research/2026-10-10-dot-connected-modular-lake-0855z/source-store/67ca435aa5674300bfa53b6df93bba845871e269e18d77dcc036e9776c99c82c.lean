import G1CanonicalOwnInteriorPrivateWord

/-! Actual source-derived ONE-bridge pending K replacement in the whole
original network, with every original root checkpoint and SAME unbounded
completion. All two-interface/private-word admissions are derived. The
arbitrary finite all-actor sweep is a subsequent protocol-preservation gate. -/
namespace G1ActualOwnPendingKReplacement
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCompletionHarmonic
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalOriginalExitAsyncStep
open G1CanonicalOwnTwoInterfaceRuntime G1CanonicalInteriorInterfaceAdmission G1CanonicalOwnInteriorPrivateWord
open G1CanonicalWholePrivateSourceWord G1WholeCanonicalPrivateWordTrueK G1CanonicalPendingTrueKExposure
open G1CanonicalExtractedPrivateKWord G1OriginalActorPrivateWordKernel G1ActualOriginalUnrankedLocalKernel
open G1OriginalExteriorCohort G1ActiveCoreBridgeCohorts G1CanonicalOriginalKOnlyActorRow
open G1CanonicalInitializedWholeCalendarHistory G1CanonicalWholeCalendarSameCompletion
open G1ActualOriginalRootRecordedProgram G1PendingBaseCheckpointRecorder
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1UnrankedSourceView
open G1OriginalWholeCausalView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_own_interior_source_K_kernel_all_values (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :
    actorWordKernel (ownerKernels actor (ownRuntimeParts O H D hD sample gamma common r actor).interior) =
      canonicalPendingKRow O H D hD sample gamma common r actor := by
  funext value
  rw [actual_own_interior_kernel_list_is_whole_private_word,actual_whole_calendar_private_fused_source_row,
    actual_whole_original_private_word_is_extracted_span]
  have he : originalActorInsideCopies O sample (actorInput O D actor) = originalInsideCopies O sample (actorInput O D actor) := by
    ext x; simp [originalActorInsideCopies,originalOutsideCopies,originalInsideCopies]
  simp only [canonicalPendingKRow,he]

noncomputable def ownPendingKRuntime (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T) :=
  let parts := ownRuntimeParts O H D hD sample gamma common r actor
  parts.before ++ [parts.opening] ++
    [.localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor)] ++
    outsideOperations actor parts.interior ++ [parts.closing] ++ parts.future

/-- ONE actual bridge private word is replaced by its source-derived K row
at the OWN opening. Its opaque output remains private until the actual OWN
release; every outside operation/checkpoint still runs exactly once. -/
theorem actual_entire_original_runtime_one_pending_K_row (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (actor : BridgeActor T)
    (state : (UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
      (BridgeActor T → UnrankedView O.Vertex O.Edge Copy)) :
    asyncProgram (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r) state =
      asyncProgram (ownPendingKRuntime O H D hD sample gamma common r actor) state := by
  let parts := ownRuntimeParts O H D hD sample gamma common r actor
  have hbody : asyncProgram parts.interior = asyncProgram
      ([.localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor)] ++ outsideOperations actor parts.interior) := by
    funext entry
    rw [actual_finite_pending_actor_promotion actor parts.interior
      (actual_own_runtime_interior_has_no_own_interface O H D hD sample gamma common r actor) entry]
    have hword : actorWordKernel (ownerKernels actor parts.interior) = canonicalPendingKRow O H D hD sample gamma common r actor :=
      actual_own_interior_source_K_kernel_all_values O H D hD sample gamma common r actor
    rw [pendingWordStep,hword]
    simp only [async_program_append,asyncProgram,PMF.bind_pure]
  rw [actual_entire_original_runtime_two_interface_split O H D hD sample gamma common r actor]
  change asyncProgram (parts.before ++ [parts.opening] ++ parts.interior ++ [parts.closing] ++ parts.future) state = _
  calc
    _ = asyncProgram (parts.before ++ [parts.opening] ++
        ([.localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor)] ++ outsideOperations actor parts.interior) ++
        [parts.closing] ++ parts.future) state := by
      simp_rw [async_program_append]
      rw [hbody]
    _ = _ := by simp only [ownPendingKRuntime,parts,List.append_assoc]

/-- Actual whole original source/calendar to ONE pending true-K-labelled
bridge, through SAME actual ancestral completion, JOINTLY retaining every
original root/ancestral calendar checkpoint and the whole completed tree. -/
theorem actual_one_pending_K_same_completed_original_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (actor : BridgeActor T) (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val))
      (initialCode O.network sample register) history).bind
      (fun result => (completionKernel O.network r result.1).map (fun final => (wholeOriginalView O.network final,result.2))) =
    (asyncProgram (ownPendingKRuntime O H D hD sample gamma common r actor)
      (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
        (initialCode O.network sample register)))).bind
      (fun out => canonicalCompletedBaseHistory O r (initialCode O.network sample register) out.1) := by
  rw [actual_whole_original_calendar_same_completed_history O H D hD sample register gamma common r history,
    actual_entire_original_runtime_one_pending_K_row O H D hD sample gamma common r actor]

#print axioms actual_entire_original_runtime_one_pending_K_row
#print axioms actual_one_pending_K_same_completed_original_history
end G1ActualOwnPendingKReplacement
