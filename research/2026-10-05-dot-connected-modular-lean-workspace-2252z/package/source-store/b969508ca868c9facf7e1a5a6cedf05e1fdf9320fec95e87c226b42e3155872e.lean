import G1FirstOwnInterfaceRecordSupport

/-! All first OWN records of the SAME initialized all-actor promoted run
are genuine opaque ORIGINAL source-frontier inputs. The whole record law
is transported, while actual private K-input equality remains separate. -/
namespace G1PromotedFirstEntryRealSourceSupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCalendarCompatibility
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalOwnTwoInterfaceRuntime G1CanonicalOwnProtocolSignature
open G1CanonicalActorLifecycleCompiler G1CanonicalOriginalExitAsyncStep
open G1CanonicalInitializedWholeCalendarHistory G1InitializedFrontierPrefix
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open G1PendingInterfaceEntryRecorder G1PendingBaseCheckpointRecorder G1FirstOwnInterfaceRecordSupport
open G1RecordedOwnOpeningRealFrontier G1ActiveCoreBridgeCohorts G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_original_first_entry_record_has_real_source (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (actor : BridgeActor T) (history : List (UnrankedView O.Vertex O.Edge Copy))
    {out : ((UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
      List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy)) × (BridgeActor T → UnrankedView O.Vertex O.Edge Copy)}
    (hout : out ∈ (asyncProgram
      ((canonicalRecordedWholeCalendarOps O H D hD sample gamma common r).map interfaceRecordingLift)
      (withEntryRecords [] (withBaseHistory history
        (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
          (initialCode O.network sample register))))).support) :
    ∃ s : Code O.network sample,
      s ∈ (sourceProgram O.network r
        (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
          (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support ∧
      FirstOwnRecord actor (unrankedView (selectedView (state s)
        (originalInsideCopies O sample (actorInput O D actor)))) out.1.2 := by
  let parts := ownRuntimeParts O H D hD sample gamma common r actor
  let rest := parts.interior ++ [parts.closing] ++ parts.future
  let initial := withEntryRecords ([] : List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy))
    (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
      (initialCode O.network sample register)))
  have hlist : canonicalRecordedWholeCalendarOps O H D hD sample gamma common r =
      (parts.before ++ [parts.opening]) ++ rest := by
    rw [actual_entire_original_runtime_two_interface_split O H D hD sample gamma common r actor]
    simp only [parts,rest,List.append_assoc]
  rw [hlist,List.map_append,async_program_append] at hout
  obtain ⟨opened,hopened,hlater⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨s,hs,hvalue⟩ := actual_recorded_own_opening_has_real_original_frontier O H D hD sample register
    gamma common r actor history [] hopened
  have hopened' := hopened
  rw [List.map_append,async_program_append] at hopened'
  obtain ⟨before,hbefore,hopen⟩ := (PMF.mem_support_bind_iff _ _ _).mp hopened'
  have hno : NoOwnRecord actor before.1.2 := actual_no_own_record_safe_program actor parts.before
    (actual_own_before_piece_interior_safe O H D hD sample gamma common r actor) initial
    (by simp [initial,withEntryRecords,NoOwnRecord]) hbefore
  obtain ⟨opening,ho⟩ : ∃ opening, parts.opening = AsyncOperation.interface actor opening := ⟨_,rfl⟩
  have hopen : opened ∈ (asyncStep (interfaceRecordingLift (.interface actor opening)) before).support := by
    simpa only [ho,List.map_singleton,asyncProgram,PMF.bind_pure] using hopen
  have hfirst := actual_own_interface_first_record actor opening before hno hopen
  have hfinal := actual_first_own_record_persists actor (opened.2 actor) rest opened hfirst hlater
  refine ⟨s,hs,?_⟩
  simpa only [hvalue] using hfinal

/-- This is actual support of the ONE promoted joint record distribution,
not independently sampled per-actor entry marginals. Every witness belongs
to the SAME original graph/calendar/parameter/registry/source programme. -/
theorem actual_promoted_first_entry_record_has_real_source (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (actor : BridgeActor T) (history : List (UnrankedView O.Vertex O.Edge Copy))
    {out : ((UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
      List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy)) × (BridgeActor T → UnrankedView O.Vertex O.Edge Copy)}
    (hout : out ∈ (asyncProgram (promoteEveryActor (Finset.univ.toList)
      ((canonicalRecordedWholeCalendarOps O H D hD sample gamma common r).map interfaceRecordingLift))
      (withEntryRecords [] (withBaseHistory history
        (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
          (initialCode O.network sample register))))).support) :
    ∃ s : Code O.network sample,
      s ∈ (sourceProgram O.network r
        (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
          (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support ∧
      FirstOwnRecord actor (unrankedView (selectedView (state s)
        (originalInsideCopies O sample (actorInput O D actor)))) out.1.2 := by
  rw [←actual_every_actor_promotion_row] at hout
  exact actual_original_first_entry_record_has_real_source O H D hD sample register gamma common r actor history hout

#print axioms actual_promoted_first_entry_record_has_real_source
end G1PromotedFirstEntryRealSourceSupport
