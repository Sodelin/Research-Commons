import G1OriginalClosingRuntimeDecomposition

/-! Real initialized support at every original runtime prefix is derived by
stopped chronological induction. This preserves complete causal coordinates
and root checkpoints, and supplies source admission at actor openings without
claiming cached private outputs are actual intermediate source states. -/
namespace G1InitializedStoppedRuntimeAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalNodeAsyncBatch
open G1CanonicalOriginalAdjacentRecordedRow G1CanonicalOriginalBoundaryEpochAdmission
open G1CanonicalOriginalDateGapRoles G1OriginalRuntimeCalendarCuts
open G1ActualOriginalRootRecordedProgram G1ActualOriginalBoundaryRootHistory G1PendingBaseCheckpointRecorder
open G1PendingActorInterfaceCommutation G1ActualJointProgram G1ContextualForestReplacement
open G1InitializedFrontierPrefix G1CanonicalThreeEpochList G1OriginalCalendarDecomposition G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_real_original_stopped_suffix_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (node stop : O.Vertex) (dates : List ℝ)
    (heq : afterDate O.network O.calendar (O.calendar.age node) = dates)
    (hlt : O.calendar.age node < O.calendar.age stop) (hm : O.calendar.age stop ∈ dates)
    {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) ++
        stopBeforeTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
          (O.calendar.age stop) (O.calendar.age node) dates) s history).map
      (fun result => withBaseHistory result.2 (canonicalExitProjection O H D hD (O.calendar.age stop) [] result.1)) =
    asyncProgram (canonicalRecordedBoundaryOps O H D hD sample gamma common r (O.calendar.age node) ++
      stoppedRuntimeTail O H D hD sample gamma common r (O.calendar.age stop) (O.calendar.age node) dates)
      (withBaseHistory history (canonicalExitProjection O H D hD (O.calendar.age node) [] s)) := by
  induction dates generalizing node s history with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons next dates ih =>
    have hn : next ∈ afterDate O.network O.calendar (O.calendar.age node) := by rw [heq]; exact List.mem_cons_self
    obtain ⟨nextNode,rfl⟩ := actual_original_date_has_vertex O next (List.mem_filter.mp hn).1
    have hpair := actual_after_date_head_tail O (O.calendar.age node) (O.calendar.age nextNode) dates heq
    have hgap := actual_next_original_date_gap O (O.calendar.age node) (O.calendar.age nextNode) dates heq
    by_cases he : O.calendar.age nextNode = O.calendar.age stop
    · rw [←he]
      simpa only [stopBeforeTail,stoppedRuntimeTail,if_true,recordedEpochBlock,canonicalRecordedBoundaryEpochOps] using
        actual_real_original_adjacent_recorded_row O H D hD sample register gamma common r node nextNode hpair.1 hgap hs history
    · have hm' : O.calendar.age stop ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm he)
      have ho := original_after_ordered O.network O.calendar (O.calendar.age node)
      rw [heq] at ho
      have hns := (List.pairwise_cons.mp ho).1 _ hm'
      let first := boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) ++
        [.interval (Real.toNNReal (O.calendar.age nextNode-O.calendar.age node))]
      let last := boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age nextNode) ++
        stopBeforeTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
          (O.calendar.age stop) (O.calendar.age nextNode) dates
      let view := fun result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy) =>
        withBaseHistory result.2 (canonicalExitProjection O H D hD (O.calendar.age nextNode) [] result.1)
      let later := canonicalRecordedBoundaryOps O H D hD sample gamma common r (O.calendar.age nextNode) ++
        stoppedRuntimeTail O H D hD sample gamma common r (O.calendar.age stop) (O.calendar.age nextNode) dates
      have hnext (result : Code O.network sample × List (UnrankedView O.Vertex O.Edge Copy))
          (hr : result ∈ (originalRootRecordedProgram O r first s history).support) :
          (originalRootRecordedProgram O r last result.1 result.2).map
            (fun final => withBaseHistory final.2 (canonicalExitProjection O H D hD (O.calendar.age stop) [] final.1)) =
            asyncProgram later (view result) :=
        ih nextNode hpair.2 hns hm'
          (actual_adjacent_recorded_block_reaches_real_prefix O H sample register gamma common r node nextNode
            hpair.1 dates heq hs history hr) result.2
      have hsplit : boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node) ++
          stopBeforeTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
            (O.calendar.age stop) (O.calendar.age node) (O.calendar.age nextNode::dates) = first ++ last := by
        simp only [stopBeforeTail,if_neg he,first,last,List.append_assoc,List.singleton_append]
      rw [hsplit]
      calc
        _ = (originalRootRecordedProgram O r first s history).bind (fun result => asyncProgram later (view result)) := by
          rw [actual_original_root_recorded_append,PMF.map_bind]
          exact bind_eq_of_eq_on_support _ _ _ hnext
        _ = ((originalRootRecordedProgram O r first s history).map view).bind (asyncProgram later) := by
          rw [PMF.bind_map]; rfl
        _ = _ := by
          rw [actual_real_original_adjacent_recorded_row O H D hD sample register gamma common r node nextNode hpair.1 hgap hs history,
            ←async_program_append]
          simp only [later,canonicalRecordedBoundaryEpochOps,stoppedRuntimeTail,if_neg he,recordedEpochBlock,List.append_assoc]

/-- Initialized complete ORIGINAL before-date prefix equals the exact stopped
runtime prefix, jointly retaining causal coordinates and every earlier root
checkpoint. This is a derived real opening support gate. -/
theorem actual_initialized_original_before_runtime_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (stop : O.Vertex) (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age stop))
      (initialCode O.network sample register) history).map
      (fun result => withBaseHistory result.2 (canonicalExitProjection O H D hD (O.calendar.age stop) [] result.1)) =
    asyncProgram (beforeRuntimeBoundary O H D hD sample gamma common r (O.calendar.age stop))
      (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
        (initialCode O.network sample register))) := by
  have hmember := original_date_scheduled O.network O.calendar stop
  have hne : sortedOriginalDates O.network O.calendar ≠ [] := by
    intro he; rw [he] at hmember; exact List.not_mem_nil hmember
  obtain ⟨date,dates,he⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨node,rfl⟩ := actual_original_date_has_vertex O date (by rw [he]; exact List.mem_cons_self)
  have hfirst : O.calendar.age node = firstOriginalDate O.network O.calendar := by
    have hf := first_compiled_date_is_initial_boundary O.network O.calendar
    simpa only [he,List.getElem_cons_zero] using hf
  have ho := original_dates_strict O.network O.calendar
  rw [he] at ho hmember
  have hp := List.pairwise_cons.mp ho
  by_cases hstop : O.calendar.age node = O.calendar.age stop
  · simp [beforeBoundaryProgram,beforeRuntimeBoundary,he,hstop,←hfirst,originalRootRecordedProgram,asyncProgram,PMF.pure_map]
  · have hm := (List.mem_cons.mp hmember).resolve_left (Ne.symm hstop)
    have hlt := hp.1 _ hm
    have haf : afterDate O.network O.calendar (O.calendar.age node) = dates := by
      unfold afterDate; rw [he,filter_after_head hp.1]
    have hs : initialCode O.network sample register ∈ (sourceProgram O.network r
        (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
        (initialCode O.network sample register)).support := by simp [beforeBoundaryProgram,he,sourceProgram]
    have law := actual_real_original_stopped_suffix_history O H D hD sample register gamma common r node stop dates haf hlt hm hs history
    have hfne : firstOriginalDate O.network O.calendar ≠ O.calendar.age stop := by rw [←hfirst]; exact hstop
    simpa only [beforeBoundaryProgram,beforeRuntimeBoundary,he,hfirst,if_neg hfne] using law

#print axioms actual_initialized_original_before_runtime_history
end G1InitializedStoppedRuntimeAdmission
