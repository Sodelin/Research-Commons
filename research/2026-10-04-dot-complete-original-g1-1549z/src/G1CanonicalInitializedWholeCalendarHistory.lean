import G1CanonicalWholeCalendarRecordedSuffix
import G1CanonicalPendingRootTerminal

/-! Initialized complete original calendar execution, with the entire actual
post-operation root/ancestral history. The compiler itself supplies all dates;
all pending actors are released at the actual original root, so final base is
the complete original descendant-labelled unranked causal view. -/
namespace G1CanonicalInitializedWholeCalendarHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalOriginalNodeAsyncBatch G1CanonicalOriginalExitAsyncStep
open G1CanonicalActorLifecycleCompiler
open G1CanonicalOriginalNodeAsyncStep
open G1CanonicalOriginalActorOpening G1CanonicalPendingActorSets G1CanonicalPendingRootTerminal
open G1CanonicalOriginalBoundaryAsyncBatch G1CanonicalOriginalEpochAsync
open G1CanonicalOriginalDateGapRoles G1CanonicalOriginalBoundaryEpochAdmission
open G1CanonicalWholeCalendarRecordedSuffix G1ActualOriginalBoundaryRootHistory
open G1ActualOriginalRootRecordedProgram G1PendingBaseCheckpointRecorder
open G1PendingOriginalRootBlobCheckpointHistory G1PendingActorInterfaceCommutation
open G1ContextualForestReplacement G1SameOriginalExteriorContinuation G1ActualJointProgram
open G1InitializedFrontierPrefix G1CanonicalThreeEpochList G1UnrankedSourceView
open G1OriginalCalendarDecomposition G1OriginalWholeCausalView
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_calendar_suffix_final_date_is_root (O : Source.{u,v,w} X) (node : O.Vertex) (dates : List ℝ)
    (heq : afterDate O.network O.calendar (O.calendar.age node) = dates) :
    lastCalendarDate (O.calendar.age node) dates = O.calendar.age O.network.root := by
  induction dates generalizing node with
  | nil =>
    change O.calendar.age node = O.calendar.age O.network.root
    apply le_antisymm (original_root_latest O.network O.calendar node)
    by_contra hn
    have hm := original_after_member O.network O.calendar _ O.network.root (lt_of_not_ge hn)
    rw [heq] at hm
    exact List.not_mem_nil hm
  | cons next later ih =>
    have hm : next ∈ afterDate O.network O.calendar (O.calendar.age node) := by rw [heq]; exact List.mem_cons_self
    obtain ⟨nextNode,rfl⟩ := actual_original_date_has_vertex O next (List.mem_filter.mp hm).1
    exact ih nextNode (actual_after_date_head_tail O _ _ later heq).2

noncomputable def canonicalRecordedWholeCalendarOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) :=
  match sortedOriginalDates O.network O.calendar with
  | [] => []
  | date::dates => canonicalRecordedCalendarSuffix O H D hD sample gamma common r date dates

/-- The entire actual initialized old source/calendar maps to its concrete
chronological pending interpreter, retaining every original root checkpoint
jointly with complete original causal coordinates. No runtime admission,
separator, close list, desired kernel or output equality is supplied. -/
theorem actual_initialized_whole_original_calendar_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val))
      (initialCode O.network sample register) history).map
      (fun result => withBaseHistory result.2 (canonicalDateProjection O D (O.calendar.age O.network.root) result.1)) =
    asyncProgram (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)
      (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
        (initialCode O.network sample register))) := by
  have hne : sortedOriginalDates O.network O.calendar ≠ [] := by
    intro he
    have hm := original_date_scheduled O.network O.calendar O.network.root
    rw [he] at hm; exact List.not_mem_nil hm
  obtain ⟨date,dates,he⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨node,rfl⟩ := actual_original_date_has_vertex O date (by rw [he]; exact List.mem_cons_self)
  have hfirst : O.calendar.age node = firstOriginalDate O.network O.calendar := by
    have hf := first_compiled_date_is_initial_boundary O.network O.calendar
    simpa only [he,List.getElem_cons_zero] using hf
  have hord := original_dates_strict O.network O.calendar
  rw [he] at hord
  have haf : afterDate O.network O.calendar (O.calendar.age node) = dates := by
    unfold afterDate
    rw [he,filter_after_head (List.pairwise_cons.mp hord).1]
  have hs : initialCode O.network sample register ∈ (sourceProgram O.network r
      (beforeBoundaryProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support := by
    simp [beforeBoundaryProgram,he,sourceProgram]
  have law := actual_real_whole_original_calendar_suffix_history O H D hD sample register gamma common r node dates haf hs history
  rw [actual_calendar_suffix_final_date_is_root O node dates haf] at law
  simpa only [compiledCalendarProgram,canonicalRecordedWholeCalendarOps,he,hfirst] using law

lemma actual_root_date_pending_base_whole_original (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X} (s : Code O.network sample) :
    (canonicalDateProjection O D (O.calendar.age O.network.root) s).1 = wholeOriginalView O.network s := by
  have he : O.calendar.age O.network.root = T.calendar.age T.network.root := by
    rw [D.calendar,D.root]
  have hempty : canonicalDateActors T (O.calendar.age O.network.root) = [] := by
    rw [he,canonicalDateActors,actual_after_root_actor_set_empty]
    simp
  unfold canonicalDateProjection
  rw [hempty]
  exact actual_pending_empty_base_whole_original O D s

/-- Concrete endpoint readout contains the WHOLE original view and every
original root/ancestral checkpoint, not hidden ordered representatives. -/
theorem actual_initialized_whole_original_base_history (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    (originalRootRecordedProgram O r
      (compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val))
      (initialCode O.network sample register) history).map
      (fun result => (wholeOriginalView O.network result.1,result.2)) =
    (asyncProgram (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)
      (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
        (initialCode O.network sample register)))).map Prod.fst := by
  rw [←actual_initialized_whole_original_calendar_history O H D hD sample register gamma common r history,PMF.map_comp]
  congr 1
  funext result
  simp only [Function.comp_def,withBaseHistory,actual_root_date_pending_base_whole_original]

#print axioms actual_initialized_whole_original_calendar_history
#print axioms actual_initialized_whole_original_base_history
end G1CanonicalInitializedWholeCalendarHistory
