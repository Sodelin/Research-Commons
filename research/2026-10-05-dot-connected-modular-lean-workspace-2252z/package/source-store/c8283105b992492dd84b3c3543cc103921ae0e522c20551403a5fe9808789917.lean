import G1CanonicalOriginalOpeningAsyncBatch

/-! Exact actual execution of a complete original date boundary batch:
OLD exits with immediate closes, all original-site opens, then OLD nodes.
Every admission follows from the same initialized original source prefix. -/
namespace G1CanonicalOriginalBoundaryAsyncBatch
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalExitAsyncBatch G1CanonicalOriginalOpeningAsyncBatch
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalNodeAsyncBatch G1PendingActorInterfaceCommutation
open G1InitializedFrontierPrefix G1ActualJointProgram G1SameOriginalExteriorContinuation
open G1OriginalCalendarDecomposition G1CanonicalComponentSegment
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalNodeBatchOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (date : ℝ) :=
  ((Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList).map
    (canonicalNodeAsyncOperation O H D hD sample gamma common r)

noncomputable def canonicalBoundaryAsyncOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (date : ℝ) :=
  canonicalExitBatchOps O H D hD sample gamma common r date [] (originalExits O.network O.calendar date) ++
  canonicalOpeningBatchOps O D sample (canonicalExitActors O H D hD date (originalExits O.network O.calendar date))
    (canonicalOriginalOpeningActors O H D hD date) ++
  canonicalNodeBatchOps O H D hD sample gamma common r date

lemma actual_real_after_exits_frontier_support (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) {s d : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date)
      (initialCode O.network sample register)).support)
    (hd : d ∈ (sourceProgram O.network r ((originalExits O.network O.calendar date).map (fun e => .boundary (.exit e))) s).support) :
    d ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date)
      (initialCode O.network sample register)).support := by
  unfold actualFrontierProgram
  rw [actual_source_program_append]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨s,hs,hd⟩

/-- Whole actual original boundary batch→concrete pending runtime program.
The source-derived roles, own-cut closes and original-site openings are bound
in execution, not merely erased as tags. No desired row is assumed. -/
theorem actual_real_original_boundary_batch_async_program (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support) :
    (sourceProgram O.network r
      (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s).map
      (canonicalDateProjection O D (O.calendar.age node)) =
    asyncProgram (canonicalBoundaryAsyncOps O H D hD sample gamma common r (O.calendar.age node))
      (canonicalExitProjection O H D hD (O.calendar.age node) [] s) := by
  let date := O.calendar.age node
  let exits : List (ProgramStep O.network) := (originalExits O.network O.calendar date).map (fun e => ProgramStep.boundary (.exit e))
  let opens := canonicalOpeningBatchOps O D sample (canonicalExitActors O H D hD date (originalExits O.network O.calendar date))
    (canonicalOriginalOpeningActors O H D hD date)
  let nodes := canonicalNodeBatchOps O H D hD sample gamma common r date
  let exitView := canonicalExitProjection O H D hD (sample := sample) date (originalExits O.network O.calendar date)
  have heq : boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date =
      exits ++ nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date := rfl
  have hnext (d : Code O.network sample) (hd : d ∈ (sourceProgram O.network r exits s).support) :
      (sourceProgram O.network r (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date) d).map
        (canonicalDateProjection O D date) = asyncProgram (opens ++ nodes) (exitView d) := by
    have hf := actual_real_after_exits_frontier_support O H sample register gamma common r date hs hd
    have hn := actual_real_original_node_batch_async_program O H D hD sample register gamma common r node hf
    change _ = asyncProgram nodes (canonicalDateProjection O D date d) at hn
    rw [hn]
    calc
      _ = (PMF.pure (canonicalDateProjection O D date d)).bind (asyncProgram nodes) := (PMF.pure_bind _ _).symm
      _ = (asyncProgram opens (exitView d)).bind (asyncProgram nodes) := by
        rw [actual_canonical_original_opening_batch_replay O H D hD date d]
      _ = _ := (async_program_append _ _ _).symm
  calc
    _ = (sourceProgram O.network r exits s).bind (fun d => asyncProgram (opens ++ nodes) (exitView d)) := by
      rw [heq,actual_source_program_append,PMF.map_bind]
      exact bind_eq_of_eq_on_support _ _ _ hnext
    _ = ((sourceProgram O.network r exits s).map exitView).bind (asyncProgram (opens ++ nodes)) := by
      rw [PMF.bind_map]; rfl
    _ = _ := by
      rw [actual_real_original_exit_batch_async_program O H D hD sample register gamma common r node hs]
      simpa only [canonicalBoundaryAsyncOps,List.append_assoc] using (async_program_append _ _ _).symm

#print axioms actual_real_original_boundary_batch_async_program
end G1CanonicalOriginalBoundaryAsyncBatch
