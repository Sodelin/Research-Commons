import G1OriginalRuntimeCalendarCuts

/-! Exact own opening-frontier/last-cut decomposition of the concrete
history-carrying runtime. Original exit order, immediate cut close and its
post-close checkpoint are kept; no abstract lifecycle trace is supplied. -/
namespace G1OriginalClosingRuntimeDecomposition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1OriginalSpanClosingPhase
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalOpeningAsyncBatch
open G1ActualOriginalExitBatchRootHistory G1ActualOriginalNodeBatchRootHistory G1ActualOriginalBoundaryRootHistory
open G1CanonicalOriginalBoundaryAsyncBatch G1PendingBaseCheckpointRecorder G1PendingActorInterfaceCommutation
open G1CanonicalInitializedWholeCalendarHistory G1OriginalRuntimeCalendarCuts
open G1OriginalCalendarDecomposition G1CanonicalThreeEpochList
open G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_recorded_exit_batch_split (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) (processed first last : List O.Edge) :
    canonicalRecordedExitBatchOps O H D hD sample gamma common r date processed (first ++ last) =
      canonicalRecordedExitBatchOps O H D hD sample gamma common r date processed first ++
      canonicalRecordedExitBatchOps O H D hD sample gamma common r date (processed ++ first) last := by
  induction first generalizing processed with
  | nil => simp [canonicalRecordedExitBatchOps]
  | cons edge edges ih =>
    simp only [List.cons_append,canonicalRecordedExitBatchOps]
    rw [ih]
    simp only [List.append_assoc,List.singleton_append]

noncomputable def afterExitRuntimeOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (date : ℝ) :=
  (canonicalOpeningBatchOps O D sample (canonicalExitActors O H D hD date (originalExits O.network O.calendar date))
    (canonicalOriginalOpeningActors O H D hD date)).map historyLift ++
  canonicalRecordedNodeBatchOps O H D hD sample gamma common r
    (Finset.univ.filter (fun node : O.Vertex => O.calendar.age node = date)).toList

noncomputable def openingRuntimeFrontier (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (first : O.Vertex) :=
  beforeRuntimeBoundary O H D hD sample gamma common r (O.calendar.age first) ++
    canonicalRecordedExitBatchOps O H D hD sample gamma common r (O.calendar.age first) []
      (originalExits O.network O.calendar (O.calendar.age first)) ++
    (canonicalOpeningBatchOps O D sample
      (canonicalExitActors O H D hD (O.calendar.age first) (originalExits O.network O.calendar (O.calendar.age first)))
      (canonicalOriginalOpeningActors O H D hD (O.calendar.age first))).map historyLift

noncomputable def closingRuntimePhase (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (first last : O.Vertex) (edge : O.Edge) :=
  canonicalRecordedNodeBatchOps O H D hD sample gamma common r
    (Finset.univ.filter (fun node : O.Vertex => O.calendar.age node = O.calendar.age first)).toList ++
  stoppedRuntimeTail O H D hD sample gamma common r (O.calendar.age last) (O.calendar.age first)
    (afterDate O.network O.calendar (O.calendar.age first)) ++
  canonicalRecordedExitBatchOps O H D hD sample gamma common r (O.calendar.age last) [] (closingExits O edge)

noncomputable def closingRuntimeFuture (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (edge : O.Edge) :=
  canonicalRecordedExitBatchOps O H D hD sample gamma common r (O.calendar.age (O.network.graph.source edge))
    (closingExits O edge)
    ((originalExits O.network O.calendar (O.calendar.age (O.network.graph.source edge))).dropWhile
      (fun e => decide (e ≠ edge))).tail ++
  afterExitRuntimeOps O H D hD sample gamma common r (O.calendar.age (O.network.graph.source edge)) ++
  recordedRuntimeTail O H D hD sample gamma common r (O.calendar.age (O.network.graph.source edge))
    (afterDate O.network O.calendar (O.calendar.age (O.network.graph.source edge)))

/-- Literal full runtime decomposition at the actual original component ports.
The final cut closes before its original root checkpoint; remaining original
same-date exits/openings/nodes/time all stay in the SAME runtime future. -/
theorem actual_original_closing_runtime_decomposition (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (first last : O.Vertex) (edge : O.Edge) (he : O.network.graph.source edge = last)
    (hlt : O.calendar.age first < O.calendar.age last) :
    canonicalRecordedWholeCalendarOps O H D hD sample gamma common r =
      openingRuntimeFrontier O H D hD sample gamma common r first ++
      closingRuntimePhase O H D hD sample gamma common r first last edge ++
      closingRuntimeFuture O H D hD sample gamma common r edge := by
  have hstart := actual_whole_recorded_runtime_date_cut O H D hD sample gamma common r (O.calendar.age first)
    (original_date_scheduled O.network O.calendar first)
  have htail := actual_recorded_runtime_tail_cut O H D hD sample gamma common r
    (afterDate O.network O.calendar (O.calendar.age first)) (original_after_ordered _ _ _)
    (O.calendar.age last) (original_after_member _ _ _ last hlt) (O.calendar.age first)
  have hf : (afterDate O.network O.calendar (O.calendar.age first)).filter (fun date => decide (O.calendar.age last < date)) =
      afterDate O.network O.calendar (O.calendar.age last) := filter_after_filter hlt _
  rw [hf] at htail
  have hm : edge ∈ originalExits O.network O.calendar (O.calendar.age last) :=
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg O.calendar.age he⟩)
  have hexits := original_exit_list_cut (originalExits O.network O.calendar (O.calendar.age last)) edge hm
  have hx : originalExits O.network O.calendar (O.calendar.age last) = closingExits O edge ++
      ((originalExits O.network O.calendar (O.calendar.age last)).dropWhile (fun e => decide (e ≠ edge))).tail := by
    simpa only [closingExits,he] using hexits
  have hboundary (date : ℝ) : canonicalRecordedBoundaryOps O H D hD sample gamma common r date =
      canonicalRecordedExitBatchOps O H D hD sample gamma common r date [] (originalExits O.network O.calendar date) ++
      afterExitRuntimeOps O H D hD sample gamma common r date := by
    simp only [canonicalRecordedBoundaryOps,afterExitRuntimeOps,List.append_assoc]
  rw [hstart,htail,hboundary,hboundary]
  conv_lhs => rw [hx]
  rw [actual_recorded_exit_batch_split]
  unfold openingRuntimeFrontier closingRuntimePhase closingRuntimeFuture afterExitRuntimeOps
  rw [he]
  simp only [List.nil_append,List.append_assoc]

#print axioms actual_original_closing_runtime_decomposition
end G1OriginalClosingRuntimeDecomposition
