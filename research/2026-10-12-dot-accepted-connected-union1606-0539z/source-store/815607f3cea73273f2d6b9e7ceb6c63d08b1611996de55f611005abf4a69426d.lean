import G1ActualOriginalNodeBatchRootHistory

/-! Complete chronological root history for a WHOLE actual original date
boundary: every old exit checkpoint, immediate physical closes, original
opens, every old node checkpoint. Artificial interfaces add no observation. -/
namespace G1ActualOriginalBoundaryRootHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1PendingActorInterfaceCommutation G1PendingBaseCheckpointRecorder
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalExitAsyncBatch G1CanonicalOriginalOpeningAsyncBatch
open G1CanonicalOriginalNodeAsyncBatch G1CanonicalOriginalBoundaryAsyncBatch
open G1ActualOriginalExitBatchRootHistory G1ActualOriginalNodeBatchRootHistory G1ActualOriginalRootRecordedProgram
open G1PendingOriginalRootBlobCheckpointHistory G1InitializedFrontierPrefix G1ActualJointProgram
open G1OriginalCalendarDecomposition G1CanonicalComponentSegment
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_original_root_recorded_support_endpoint (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network)) (s : Code O.network sample)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy))
    {result : Code O.network sample × List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)}
    (hr : result ∈ (originalRootRecordedProgram O r ops s history).support) :
    result.1 ∈ (sourceProgram O.network r ops s).support := by
  have hm : result.1 ∈ ((originalRootRecordedProgram O r ops s history).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨result,hr,rfl⟩
  rw [actual_original_root_recorded_endpoint] at hm
  exact hm

noncomputable def canonicalRecordedBoundaryOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (date : ℝ) :=
  canonicalRecordedExitBatchOps O H D hD sample gamma common r date [] (originalExits O.network O.calendar date) ++
  (canonicalOpeningBatchOps O D sample (canonicalExitActors O H D hD date (originalExits O.network O.calendar date))
    (canonicalOriginalOpeningActors O H D hD date)).map historyLift ++
  canonicalRecordedNodeBatchOps O H D hD sample gamma common r
    (Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList

/-- Exact full actual original date-boundary history row. Every original
micro-checkpoint is retained JOINTLY with full original causal runtime state;
initial real support discharges all closing/opening/recording admissions. -/
theorem actual_real_original_boundary_root_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s history).map
      (fun result => withBaseHistory result.2 (canonicalDateProjection O D (O.calendar.age node) result.1)) =
    asyncProgram (canonicalRecordedBoundaryOps O H D hD sample gamma common r (O.calendar.age node))
      (withBaseHistory history (canonicalExitProjection O H D hD (O.calendar.age node) [] s)) := by
  let date := O.calendar.age node
  let exits : List (ProgramStep O.network) := (originalExits O.network O.calendar date).map (fun e => .boundary (.exit e))
  let opens := canonicalOpeningBatchOps O D sample (canonicalExitActors O H D hD date (originalExits O.network O.calendar date))
    (canonicalOriginalOpeningActors O H D hD date)
  let nodes := canonicalRecordedNodeBatchOps O H D hD sample gamma common r
    (Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList
  let output := fun result : Code O.network sample × List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy) =>
    withBaseHistory result.2 (canonicalExitProjection O H D hD date (originalExits O.network O.calendar date) result.1)
  have heq : boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date =
      exits ++ nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date := rfl
  have hnext (result : Code O.network sample × List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy))
      (hr : result ∈ (originalRootRecordedProgram O r exits s history).support) :
      (originalRootRecordedProgram O r (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date)
        result.1 result.2).map (fun last => withBaseHistory last.2 (canonicalDateProjection O D date last.1)) =
      asyncProgram (opens.map historyLift ++ nodes) (output result) := by
    have hd := actual_original_root_recorded_support_endpoint O r exits s history hr
    have hf := actual_real_after_exits_frontier_support O H sample register gamma common r date hs hd
    have hn := actual_real_original_node_batch_root_history O H D hD sample register gamma common r node hf result.2
    change _ = asyncProgram nodes (withBaseHistory result.2 (canonicalDateProjection O D date result.1)) at hn
    rw [hn]
    calc
      _ = (PMF.pure (withBaseHistory result.2 (canonicalDateProjection O D date result.1))).bind (asyncProgram nodes) :=
        (PMF.pure_bind _ _).symm
      _ = (asyncProgram (opens.map historyLift) (output result)).bind (asyncProgram nodes) := by
        rw [←actual_history_lift_program]
        rw [←actual_canonical_original_opening_batch_replay O H D hD date result.1]
        rw [PMF.pure_map]
      _ = _ := (async_program_append _ _ _).symm
  calc
    _ = (originalRootRecordedProgram O r exits s history).bind
        (fun result => asyncProgram (opens.map historyLift ++ nodes) (output result)) := by
      rw [heq,actual_original_root_recorded_append,PMF.map_bind]
      exact bind_eq_of_eq_on_support _ _ _ hnext
    _ = ((originalRootRecordedProgram O r exits s history).map output).bind
        (asyncProgram (opens.map historyLift ++ nodes)) := by rw [PMF.bind_map]; rfl
    _ = _ := by
      rw [actual_real_original_exit_batch_root_history O H D hD sample register gamma common r node hs history]
      simpa only [canonicalRecordedBoundaryOps,List.append_assoc] using (async_program_append _ _ _).symm

#print axioms actual_real_original_boundary_root_history
end G1ActualOriginalBoundaryRootHistory
