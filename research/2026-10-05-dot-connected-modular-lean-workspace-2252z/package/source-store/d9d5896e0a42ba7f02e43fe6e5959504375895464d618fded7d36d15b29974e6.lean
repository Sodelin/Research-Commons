import G1ActualOriginalExitBatchRootHistory

/-! EVERY original node checkpoint has its actual root-blob/base recording;
the complete original node batch retains this entire chronological history,
not merely its endpoint. Private source region support propagates per node. -/
namespace G1ActualOriginalNodeBatchRootHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1PendingActorInterfaceCommutation G1PendingBaseCheckpointRecorder
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalNodeAsyncBatch G1ActualOriginalRootRecordedProgram
open G1PendingOriginalRootBlobCheckpointHistory G1ActualRootBlobPopulationFootprint G1OriginalWholeCausalView
open G1ActualRootBlobBaseObserver G1InitializedFrontierPrefix G1ActualJointProgram G1ContextualForestReplacement
open G1CanonicalComponentSegment G1NaturalActiveActorFrontier G1TaggedOriginalCalendar
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_same_date_node_root_checkpoint (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) (node : O.Vertex) (hdate : O.calendar.age node = date)
    (s : Code O.network sample) (hin : DateActorRegion O D date s)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    (sourceProgram O.network r [eraseEvent O H gamma common (.node node)] s).map (fun d =>
      withBaseHistory (history ++ [originalRootBlobView O.network (wholeOriginalView O.network d)])
        (canonicalDateProjection O D date d)) =
    asyncProgram (recordedBlock (pendingRootBlobObservation O)
      [canonicalNodeAsyncOperation O H D hD sample gamma common r node])
      (withBaseHistory history (canonicalDateProjection O D date s)) := by
  have hrow := actual_canonical_original_node_async_step O H D hD gamma common r node s
    (by simpa only [hdate,DateActorRegion] using hin)
  have hrow' : (sourceProgram O.network r [eraseEvent O H gamma common (.node node)] s).map
      (canonicalDateProjection O D date) =
      asyncProgram [canonicalNodeAsyncOperation O H D hD sample gamma common r node]
        (canonicalDateProjection O D date s) := by
    unfold canonicalDateProjection
    simpa only [hdate,asyncProgram,PMF.bind_pure] using hrow
  calc
    _ = (sourceProgram O.network r [eraseEvent O H gamma common (.node node)] s).map (fun d =>
        withBaseHistory (history ++ [pendingRootBlobObservation O (canonicalDateProjection O D date d).1])
          (canonicalDateProjection O D date d)) := by
      apply map_eq_of_eq_on_support
      intro d hd
      have hr := actual_node_source_preserves_date_actor_region O H D hD gamma common r date node s hin
        (by simpa only [sourceProgram,PMF.bind_pure] using hd)
      rw [actual_original_root_blob_view_from_active_base O H D hD (canonicalDateActors T date) d hr]
      rfl
    _ = ((sourceProgram O.network r [eraseEvent O H gamma common (.node node)] s).map
        (canonicalDateProjection O D date)).map (fun next =>
        withBaseHistory (history ++ [pendingRootBlobObservation O next.1]) next) := by rw [PMF.map_comp]; rfl
    _ = _ := by rw [hrow']; exact actual_recorded_block_row _ _ _ _

noncomputable def canonicalRecordedNodeBatchOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (nodes : List O.Vertex) := nodes.flatMap (fun node => recordedBlock (pendingRootBlobObservation O)
      [canonicalNodeAsyncOperation O H D hD sample gamma common r node])

/-- Actual full same-date node-list row jointly with EVERY post-node original
root checkpoint. All per-step region support is derived from the input. -/
theorem actual_same_date_original_nodes_recorded_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) (nodes : List O.Vertex) (hdate : ∀ node ∈ nodes, O.calendar.age node = date)
    (s : Code O.network sample) (hin : DateActorRegion O D date s)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r (nodes.map (fun node => eraseEvent O H gamma common (.node node))) s history).map
      (fun result => withBaseHistory result.2 (canonicalDateProjection O D date result.1)) =
    asyncProgram (canonicalRecordedNodeBatchOps O H D hD sample gamma common r nodes)
      (withBaseHistory history (canonicalDateProjection O D date s)) := by
  induction nodes generalizing s history with
  | nil => simp [originalRootRecordedProgram,canonicalRecordedNodeBatchOps,asyncProgram,PMF.pure_map]
  | cons node nodes ih =>
    have ha := hdate node (List.mem_cons_self)
    have ht := fun n hn => hdate n (List.mem_cons_of_mem node hn)
    let output := fun d : Code O.network sample => withBaseHistory
      (history ++ [originalRootBlobView O.network (wholeOriginalView O.network d)]) (canonicalDateProjection O D date d)
    let later := canonicalRecordedNodeBatchOps O H D hD sample gamma common r nodes
    calc
      _ = (sourceProgram O.network r [eraseEvent O H gamma common (.node node)] s).bind (fun d => asyncProgram later (output d)) := by
        simp only [List.map_cons,originalRootRecordedProgram,sourceProgram,PMF.bind_pure,PMF.map_bind]
        apply bind_eq_of_eq_on_support
        intro d hd
        exact ih ht d (actual_node_source_preserves_date_actor_region O H D hD gamma common r date node s hin hd) _
      _ = ((sourceProgram O.network r [eraseEvent O H gamma common (.node node)] s).map output).bind (asyncProgram later) := by
        rw [PMF.bind_map]; rfl
      _ = _ := by
        dsimp only [output]
        rw [actual_same_date_node_root_checkpoint O H D hD gamma common r date node ha s hin history]
        exact (async_program_append _ _ _).symm

/-- Genuine initialization discharges the input-region admission for the
ENTIRE literal original node batch and EVERY chronological node checkpoint. -/
theorem actual_real_original_node_batch_root_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support)
    (history : List (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s history).map
      (fun result => withBaseHistory result.2 (canonicalDateProjection O D (O.calendar.age node) result.1)) =
    asyncProgram (canonicalRecordedNodeBatchOps O H D hD sample gamma common r
      (Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = O.calendar.age node)).toList)
      (withBaseHistory history (canonicalDateProjection O D (O.calendar.age node) s)) := by
  apply actual_same_date_original_nodes_recorded_history O H D hD gamma common r (O.calendar.age node)
    ((Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = O.calendar.age node)).toList)
  · intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
  · intro actor hm
    exact actual_real_frontier_active_actor_region O H D hD actor node
      (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2 sample register gamma common r hs

#print axioms actual_real_original_node_batch_root_history
end G1ActualOriginalNodeBatchRootHistory
