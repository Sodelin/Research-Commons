import G1CanonicalOriginalExitCloseReplay

/-! The whole literal original exit batch executes on actual changing actor
roles. Every final cut is immediately followed by its physical close; equal
upper dates and arbitrary many simultaneous actors require no ordering fit. -/
namespace G1CanonicalOriginalExitAsyncBatch
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalExitCloseReplay G1PendingActorInterfaceCommutation
open G1TaggedOriginalCalendar G1InitializedFrontierPrefix G1ActualJointProgram G1SameOriginalExteriorContinuation
open G1OriginalCalendarDecomposition
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalExitBatchOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) : List O.Edge → List O.Edge → List (AsyncOperation (BridgeActor T)
      (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy) (G1UnrankedSourceView.UnrankedView O.Vertex O.Edge Copy))
  | _,[] => []
  | processed,edge::edges => canonicalRuntimeExitOps O H D hD sample gamma common r date processed edge ++
      canonicalExitBatchOps O H D hD sample gamma common r date (processed ++ [edge]) edges

lemma actual_exit_prefix_support_append (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (processed : List O.Edge) (edge : O.Edge) (initial s d : Code O.network sample)
    (hp : s ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support)
    (hd : d ∈ (sourceProgram O.network r [.boundary (.exit edge)] s).support) :
    d ∈ (sourceProgram O.network r ((processed ++ [edge]).map (fun e => .boundary (.exit e))) initial).support := by
  rw [List.map_append,actual_source_program_append]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨s,hp,hd⟩

/-- Exact source-to-runtime replay of an arbitrary remaining suffix of the
literal same-date exit batch. Initial real source support, actual distinct
original edge IDs and dates discharge every changing-role/close premise. -/
theorem actual_same_date_original_exits_async_program (O : Source.{u,v,w} X)
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
    (hp : s ∈ (sourceProgram O.network r (processed.map (fun e => .boundary (.exit e))) initial).support) :
    (sourceProgram O.network r (edges.map (fun e => .boundary (.exit e))) s).map
      (canonicalExitProjection O H D hD (O.calendar.age node) (processed ++ edges)) =
    asyncProgram (canonicalExitBatchOps O H D hD sample gamma common r (O.calendar.age node) processed edges)
      (canonicalExitProjection O H D hD (O.calendar.age node) processed s) := by
  induction edges generalizing processed s with
  | nil => simp [sourceProgram,canonicalExitBatchOps,asyncProgram,PMF.pure_map]
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
    let next := canonicalExitProjection O H D hD (sample := sample) (O.calendar.age node) (processed ++ [edge])
    let later := canonicalExitBatchOps O H D hD sample gamma common r (O.calendar.age node) (processed ++ [edge]) edges
    calc
      _ = (sourceProgram O.network r [.boundary (.exit edge)] s).bind (fun d => asyncProgram later (next d)) := by
        simp only [List.map_cons,sourceProgram,PMF.bind_pure,PMF.map_bind]
        apply bind_eq_of_eq_on_support
        intro d hd
        have hd' : d ∈ (sourceProgram O.network r [.boundary (.exit edge)] s).support := by
          simpa only [sourceProgram,PMF.bind_pure] using hd
        have hm := actual_exit_prefix_support_append O r processed edge initial s d hp hd'
        have hi := ih (processed ++ [edge]) hp' ht hn' d hm
        simpa only [List.append_assoc,List.singleton_append] using hi
      _ = ((sourceProgram O.network r [.boundary (.exit edge)] s).map next).bind (asyncProgram later) := by
        rw [PMF.bind_map]; rfl
      _ = _ := by
        have hrow := actual_real_original_exit_close_replay O H D hD sample register gamma common r node processed edge
          hprocessed he hnew hs hp
        simp only [eraseEvent] at hrow
        dsimp only [next]
        rw [hrow]
        exact (async_program_append _ _ _).symm

/-- The entire OLD same-date exit batch, with a source-derived immediate
close after each final cut, is the actual concrete runtime asyncProgram. -/
theorem actual_real_original_exit_batch_async_program (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support) :
    (sourceProgram O.network r ((originalExits O.network O.calendar (O.calendar.age node)).map (fun e => .boundary (.exit e))) s).map
      (canonicalExitProjection O H D hD (O.calendar.age node) (originalExits O.network O.calendar (O.calendar.age node))) =
    asyncProgram (canonicalExitBatchOps O H D hD sample gamma common r (O.calendar.age node) []
      (originalExits O.network O.calendar (O.calendar.age node)))
      (canonicalExitProjection O H D hD (O.calendar.age node) [] s) := by
  apply actual_same_date_original_exits_async_program O H D hD sample register gamma common r node []
    (originalExits O.network O.calendar (O.calendar.age node)) (fun _ hm => by cases hm)
  · intro e he
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
  · simp only [List.nil_append,originalExits]
    exact Finset.nodup_toList _
  · exact hs
  · simp [sourceProgram]

#print axioms actual_real_original_exit_batch_async_program
end G1CanonicalOriginalExitAsyncBatch
