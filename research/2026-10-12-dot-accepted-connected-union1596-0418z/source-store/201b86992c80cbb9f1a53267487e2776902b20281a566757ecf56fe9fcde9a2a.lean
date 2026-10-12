import G1ActualOriginalRootRecordedProgram

/-! Every ORIGINAL post-exit root checkpoint is preserved jointly by actual
exit-batch runtime replay. Own final cuts close before their checkpoint; no
endpoint substitution stands in for the chronological trajectory. -/
namespace G1ActualOriginalExitBatchRootHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1PendingActorInterfaceCommutation G1PendingBaseCheckpointRecorder
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalExitCloseReplay G1CanonicalOriginalExitAsyncBatch
open G1ActualOriginalExitRootCheckpoint G1ActualOriginalRootRecordedProgram
open G1PendingOriginalRootBlobCheckpointHistory G1ActualRootBlobPopulationFootprint G1OriginalWholeCausalView
open G1InitializedFrontierPrefix G1ActualJointProgram G1OriginalCalendarDecomposition
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalRecordedExitBatchOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) : List O.Edge → List O.Edge → List (AsyncOperation (BridgeActor T)
      (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)
      (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy × List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)))
  | _,[] => []
  | processed,edge::edges => recordedBlock (pendingRootBlobObservation O)
      (canonicalRuntimeExitOps O H D hD sample gamma common r date processed edge) ++
      canonicalRecordedExitBatchOps O H D hD sample gamma common r date (processed ++ [edge]) edges

/-- Joint law of the full old root-blob trajectory through a remaining actual
same-date exit suffix. Original edge uniqueness/date/source support admit
every micro-cut; arbitrary previously correlated history is fixed and carried. -/
theorem actual_same_date_original_exits_recorded_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) (processed edges : List O.Edge)
    (hprocessed : ∀ e ∈ processed, O.calendar.age (O.network.graph.source e) = O.calendar.age node)
    (hdate : ∀ e ∈ edges, O.calendar.age (O.network.graph.source e) = O.calendar.age node)
    (hnodup : (processed ++ edges).Nodup)
    {initial : Code O.network sample}
    (hs : initial ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (s : Code O.network sample)
    (hp : s ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r (edges.map (fun e => .boundary (.exit e))) s history).map
      (fun result => withBaseHistory result.2
        (canonicalExitProjection O H D hD (O.calendar.age node) (processed ++ edges) result.1)) =
    asyncProgram (canonicalRecordedExitBatchOps O H D hD sample gamma common r (O.calendar.age node) processed edges)
      (withBaseHistory history (canonicalExitProjection O H D hD (O.calendar.age node) processed s)) := by
  induction edges generalizing processed s history with
  | nil => simp [originalRootRecordedProgram,canonicalRecordedExitBatchOps,asyncProgram,PMF.pure_map]
  | cons edge edges ih =>
    have he := hdate edge (List.mem_cons_self)
    have hnew : edge ∉ processed := by
      intro hm
      exact (List.nodup_append.mp hnodup).2.2 edge hm edge (List.mem_cons_self) rfl
    have hp' : ∀ e ∈ processed ++ [edge], O.calendar.age (O.network.graph.source e) = O.calendar.age node := by
      intro e hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hprocessed e hm
      · exact (List.mem_singleton.mp hm) ▸ he
    have ht := fun e hm => hdate e (List.mem_cons_of_mem edge hm)
    have hn' : ((processed ++ [edge]) ++ edges).Nodup := by
      simpa only [List.append_assoc,List.singleton_append] using hnodup
    let output := fun d : Code O.network sample => withBaseHistory
      (history ++ [originalRootBlobView O.network (wholeOriginalView O.network d)])
      (canonicalExitProjection O H D hD (O.calendar.age node) (processed ++ [edge]) d)
    let later := canonicalRecordedExitBatchOps O H D hD sample gamma common r (O.calendar.age node) (processed ++ [edge]) edges
    calc
      _ = (sourceProgram O.network r [.boundary (.exit edge)] s).bind (fun d => asyncProgram later (output d)) := by
        simp only [List.map_cons,originalRootRecordedProgram,sourceProgram,PMF.bind_pure,PMF.map_bind]
        apply bind_eq_of_eq_on_support
        intro d hd
        have hd' : d ∈ (sourceProgram O.network r [.boundary (.exit edge)] s).support := by
          simpa only [sourceProgram,PMF.bind_pure] using hd
        have hm := actual_exit_prefix_support_append O r processed edge initial s d hp hd'
        have hi := ih (processed ++ [edge]) hp' ht hn' d hm
          (history ++ [originalRootBlobView O.network (wholeOriginalView O.network d)])
        simpa only [List.append_assoc,List.singleton_append] using hi
      _ = ((sourceProgram O.network r [.boundary (.exit edge)] s).map output).bind (asyncProgram later) := by
        rw [PMF.bind_map]; rfl
      _ = _ := by
        have hrow := actual_real_original_exit_root_checkpoint O H D hD sample register gamma common r node processed edge
          hprocessed he hnew hs s hp history
        dsimp only [output]
        rw [hrow]
        exact (async_program_append _ _ _).symm

/-- Whole literal original exit batch, recording EVERY post-exit original
root checkpoint and returning complete original causal runtime coordinates. -/
theorem actual_real_original_exit_batch_root_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r ((originalExits O.network O.calendar (O.calendar.age node)).map (fun e => .boundary (.exit e))) s history).map
      (fun result => withBaseHistory result.2
        (canonicalExitProjection O H D hD (O.calendar.age node) (originalExits O.network O.calendar (O.calendar.age node)) result.1)) =
    asyncProgram (canonicalRecordedExitBatchOps O H D hD sample gamma common r (O.calendar.age node) []
      (originalExits O.network O.calendar (O.calendar.age node)))
      (withBaseHistory history (canonicalExitProjection O H D hD (O.calendar.age node) [] s)) := by
  apply actual_same_date_original_exits_recorded_history O H D hD sample register gamma common r node []
    (originalExits O.network O.calendar (O.calendar.age node)) (fun _ hm => by cases hm)
  · intro e he
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
  · simp only [List.nil_append,originalExits]
    exact Finset.nodup_toList _
  · exact hs
  · simp [sourceProgram]

#print axioms actual_real_original_exit_batch_root_history
end G1ActualOriginalExitBatchRootHistory
