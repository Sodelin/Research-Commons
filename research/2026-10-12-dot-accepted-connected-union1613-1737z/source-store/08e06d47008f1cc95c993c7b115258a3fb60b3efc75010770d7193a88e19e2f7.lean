import G1InitializedStoppedRuntimeAdmission

/-! Every initialized ORIGINAL runtime entering frontier has a REAL original
source support witness, including the whole saved opaque inside trees and
SAME register. This derives the true-K input admission for the actual opening;
transfer to subsequently cached/promoted computation is proved separately. -/
namespace G1InitializedOpeningRuntimeAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingBoundaryMembership
open G1CanonicalOriginalActorOpening G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalNodeAsyncBatch
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalOpeningAsyncBatch G1CanonicalOriginalBoundaryAsyncBatch
open G1ActualOriginalExitBatchRootHistory G1ActualOriginalRootRecordedProgram G1ActualOriginalBoundaryRootHistory
open G1PendingBaseCheckpointRecorder G1PendingActorInterfaceCommutation G1ActualJointProgram
open G1OriginalClosingRuntimeDecomposition G1InitializedStoppedRuntimeAdmission G1OriginalRuntimeCalendarCuts
open G1ContextualForestReplacement G1InitializedFrontierPrefix G1OriginalCalendarDecomposition
open G1CanonicalPendingTrueKExposure G1CanonicalOriginalKOnlyActorRow G1ActiveCoreBridgeCohorts G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_real_original_exit_open_history (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node : O.Vertex) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r ((originalExits O.network O.calendar (O.calendar.age node)).map (fun e => .boundary (.exit e))) s history).map
      (fun result => withBaseHistory result.2 (canonicalDateProjection O D (O.calendar.age node) result.1)) =
    asyncProgram (canonicalRecordedExitBatchOps O H D hD sample gamma common r (O.calendar.age node) []
      (originalExits O.network O.calendar (O.calendar.age node)) ++
      (canonicalOpeningBatchOps O D sample
        (canonicalExitActors O H D hD (O.calendar.age node) (originalExits O.network O.calendar (O.calendar.age node)))
        (canonicalOriginalOpeningActors O H D hD (O.calendar.age node))).map (historyLift (Obs := UnrankedView O.Vertex O.Edge Copy)))
      (withBaseHistory history (canonicalExitProjection O H D hD (O.calendar.age node) [] s)) := by
  let opens := (canonicalOpeningBatchOps O D sample
    (canonicalExitActors O H D hD (O.calendar.age node) (originalExits O.network O.calendar (O.calendar.age node)))
    (canonicalOriginalOpeningActors O H D hD (O.calendar.age node))).map (historyLift (Obs := UnrankedView O.Vertex O.Edge Copy))
  let oldView := fun result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy) =>
    withBaseHistory result.2 (canonicalExitProjection O H D hD (O.calendar.age node)
      (originalExits O.network O.calendar (O.calendar.age node)) result.1)
  have hopen (result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy)) :
      asyncProgram opens (oldView result) = PMF.pure
        (withBaseHistory result.2 (canonicalDateProjection O D (O.calendar.age node) result.1)) := by
    rw [←actual_history_lift_program,←actual_canonical_original_opening_batch_replay O H D hD (O.calendar.age node) result.1,
      PMF.pure_map]
  calc
    _ = ((originalRootRecordedProgram O r
        ((originalExits O.network O.calendar (O.calendar.age node)).map (fun e => .boundary (.exit e))) s history).map oldView).bind
        (asyncProgram opens) := by
      rw [PMF.bind_map]
      simp only [Function.comp_def]
      simp_rw [hopen]
      rfl
    _ = _ := by
      rw [actual_real_original_exit_batch_root_history O H D hD sample register gamma common r node hs history]
      exact (async_program_append _ _ _).symm

/-- Actual old entering source frontier is the exact initialized runtime
prefix through all original-site openings. Whole input/history admission is
derived; it is not supplied as a desired quotient or kernel equality. -/
theorem actual_initialized_original_opening_frontier_history (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node : O.Vertex) (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register) history).map
      (fun result => withBaseHistory result.2 (canonicalDateProjection O D (O.calendar.age node) result.1)) =
    asyncProgram (openingRuntimeFrontier O H D hD sample gamma common r node)
      (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
        (initialCode O.network sample register))) := by
  let before := beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)
  let after := canonicalRecordedExitBatchOps O H D hD sample gamma common r (O.calendar.age node) []
      (originalExits O.network O.calendar (O.calendar.age node)) ++
      (canonicalOpeningBatchOps O D sample
        (canonicalExitActors O H D hD (O.calendar.age node) (originalExits O.network O.calendar (O.calendar.age node)))
        (canonicalOriginalOpeningActors O H D hD (O.calendar.age node))).map (historyLift (Obs := UnrankedView O.Vertex O.Edge Copy))
  let view := fun result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy) =>
    withBaseHistory result.2 (canonicalExitProjection O H D hD (O.calendar.age node) [] result.1)
  have hnext (result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy))
      (hr : result ∈ (originalRootRecordedProgram O r before (initialCode O.network sample register) history).support) :
      (originalRootRecordedProgram O r ((originalExits O.network O.calendar (O.calendar.age node)).map (fun e => .boundary (.exit e)))
        result.1 result.2).map (fun final => withBaseHistory final.2 (canonicalDateProjection O D (O.calendar.age node) final.1)) =
      asyncProgram after (view result) :=
    actual_real_original_exit_open_history O H D hD sample register gamma common r node
      (actual_original_root_recorded_support_endpoint O r _ _ history hr) result.2
  calc
    _ = (originalRootRecordedProgram O r before (initialCode O.network sample register) history).bind
        (fun result => asyncProgram after (view result)) := by
      rw [actualFrontierProgram,actual_original_root_recorded_append,PMF.map_bind]
      exact bind_eq_of_eq_on_support _ _ _ hnext
    _ = ((originalRootRecordedProgram O r before (initialCode O.network sample register) history).map view).bind
        (asyncProgram after) := by rw [PMF.bind_map]; rfl
    _ = _ := by
      rw [actual_initialized_original_before_runtime_history O H D hD sample register gamma common r node history,
        ←async_program_append]
      simp only [openingRuntimeFrontier,after,List.append_assoc]

/-- Every actually emitted entering quotient has a REAL initialized original
source witness with the same complete causal coordinates/history. -/
theorem actual_opening_runtime_support_has_real_source (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node : O.Vertex) (history : List (UnrankedView O.Vertex O.Edge Copy))
    {out : (UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
      (BridgeActor T → UnrankedView O.Vertex O.Edge Copy)}
    (hout : out ∈ (asyncProgram (openingRuntimeFrontier O H D hD sample gamma common r node)
      (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
        (initialCode O.network sample register)))).support) :
    ∃ s : Code O.network sample,
      s ∈ (sourceProgram O.network r
        (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
        (initialCode O.network sample register)).support ∧
      out = withBaseHistory out.1.2 (canonicalDateProjection O D (O.calendar.age node) s) := by
  rw [←actual_initialized_original_opening_frontier_history O H D hD sample register gamma common r node history] at hout
  obtain ⟨result,hr,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  refine ⟨result.1,actual_original_root_recorded_support_endpoint O r _ _ history hr,?_⟩
  rw [←he]
  rfl

#print axioms actual_initialized_original_opening_frontier_history
#print axioms actual_opening_runtime_support_has_real_source
end G1InitializedOpeningRuntimeAdmission
