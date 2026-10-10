import G1AllOriginalKLabelsWithEntryRecords

/-! Every genuine recorded OWN opening coordinate has a REAL initialized
original current-root frontier witness. This uses literal compiler prefixes,
not a cached intermediate Code invented for a prematurely sampled output. -/
namespace G1RecordedOwnOpeningRealFrontier
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCalendarCompatibility
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalOwnTwoInterfaceRuntime G1CanonicalOwnOpeningRuntimePosition G1CanonicalOwnEntryCoordinateAdmission
open G1CanonicalOriginalOpeningAsyncBatch G1CanonicalOriginalExitAsyncStep G1OriginalClosingRuntimeDecomposition
open G1InitializedOpeningRuntimeAdmission G1CanonicalFiniteActiveEpochAdmission G1OriginalCalendarDecomposition
open G1InitializedFrontierPrefix G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalNodeAsyncBatch
open G1ActualOriginalPrivateAsyncStep G1CanonicalOriginalActorOpening
open G1PendingActorInterfaceCommutation G1PendingBaseCheckpointRecorder G1PendingInterfaceEntryRecorder
open G1ActualSafeOwnInputRetention G1ActiveCoreBridgeCohorts G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_recorded_own_opening_has_real_original_frontier (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (actor : BridgeActor T) (history : List (UnrankedView O.Vertex O.Edge Copy))
    (records : List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy))
    {out : ((UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
      List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy)) × (BridgeActor T → UnrankedView O.Vertex O.Edge Copy)}
    (hout : out ∈ (asyncProgram
      (((ownRuntimeParts O H D hD sample gamma common r actor).before ++
        [(ownRuntimeParts O H D hD sample gamma common r actor).opening]).map interfaceRecordingLift)
      (withEntryRecords records (withBaseHistory history
        (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
          (initialCode O.network sample register))))).support) :
    ∃ s : Code O.network sample,
      s ∈ (sourceProgram O.network r
        (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
          (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support ∧
      out.2 actor = unrankedView (selectedView (state s) (originalInsideCopies O sample (actorInput O D actor))) := by
  let parts := ownRuntimeParts O H D hD sample gamma common r actor
  let date := O.calendar.age (actorInput O D actor)
  let actors := canonicalExitActors O H D hD date (originalExits O.network O.calendar date)
  let suffix := (canonicalOpeningBatchOps O D sample ((actors ++ sourceOpenPrefix O H D hD actor) ++ [actor])
    (sourceOpenSuffix O H D hD actor)).map (historyLift (Obs := UnrankedView O.Vertex O.Edge Copy))
  let initial := withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
    (initialCode O.network sample register))
  have hprefix : forgetEntryRecords out ∈ (asyncProgram (parts.before ++ [parts.opening]) initial).support := by
    have hm : forgetEntryRecords out ∈ ((asyncProgram
        ((parts.before ++ [parts.opening]).map interfaceRecordingLift)
        (withEntryRecords records initial)).map forgetEntryRecords).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨out,hout,rfl⟩
    rw [actual_entry_record_program_forget] at hm
    exact hm
  obtain ⟨final,hfinal⟩ := (asyncProgram suffix (forgetEntryRecords out)).support_nonempty
  have hsplit : openingRuntimeFrontier O H D hD sample gamma common r (actorInput O D actor) =
      (parts.before ++ [parts.opening]) ++ suffix := by
    unfold openingRuntimeFrontier
    rw [actual_own_original_opening_runtime_cut O H D hD sample actor]
    simp only [parts,ownRuntimeParts,suffix,actors,date,List.map_append,List.map_singleton,List.append_assoc]
  have hfront : final ∈ (asyncProgram
      (openingRuntimeFrontier O H D hD sample gamma common r (actorInput O D actor)) initial).support := by
    rw [hsplit,async_program_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨forgetEntryRecords out,hprefix,hfinal⟩
  obtain ⟨s,hs,he⟩ := actual_opening_runtime_support_has_real_source O H D hD sample register gamma common r
    (actorInput O D actor) history hfront
  have hsafe : ∀ op ∈ suffix, SafeFor actor op := by
    intro op hm
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hm
    have hn : actor ∉ sourceOpenSuffix O H D hD actor :=
      G1OriginalPrivateFutureExclusion.original_cut_absent_from_remaining _ actor
        (actual_original_opening_actor_nodup O H D hD _)
    have hh := actual_other_opening_batch_safe O D sample actor _ _ hn old ho
    cases old <;> exact hh
  have hretain := actual_safe_program_own_coordinate actor suffix hsafe (forgetEntryRecords out) hfinal
  have ha : actor ∈ canonicalDateActors T date := by
    apply Finset.mem_toList.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change T.calendar.age (T.network.graph.target actor.val) ≤ date ∧ date < T.calendar.age (T.network.graph.source actor.val)
    dsimp [date,actorInput]
    rw [←D.calendar]
    exact ⟨le_rfl,T.calendar.edge_older actor.val⟩
  change actor ∈ canonicalDateActors T (O.calendar.age (actorInput O D actor)) at ha
  refine ⟨s,hs,?_⟩
  rw [he] at hretain
  change (canonicalDateProjection O D (O.calendar.age (actorInput O D actor)) s).2 actor = out.2 actor at hretain
  rw [←hretain]
  simp only [withBaseHistory,canonicalDateProjection,originalAsyncProjection,originalPendingSlots,if_pos ha]

#print axioms actual_recorded_own_opening_has_real_original_frontier
end G1RecordedOwnOpeningRealFrontier
