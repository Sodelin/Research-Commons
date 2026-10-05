import G1CanonicalOwnClosingRuntimePosition

/-! A concrete OWN opening input equals the REAL original opaque inside
coordinate after all same-date openings. Later OTHER openings cannot change
it. The recorded interface extension preserves that value through promotion;
no cached whole original Code state is inferred from the output coordinate. -/
namespace G1CanonicalOwnEntryCoordinateAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalOriginalActorOpening G1CanonicalOriginalExitAsyncStep G1CanonicalOriginalOpeningAsyncBatch
open G1ActualOriginalOpenCloseAsyncInterface G1CanonicalFiniteActiveEpochAdmission G1ActiveCoreBridgeCohorts
open G1CanonicalOwnOpeningRuntimePosition G1OriginalCalendarDecomposition
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalNodeAsyncBatch G1ActualOriginalPrivateAsyncStep
open G1PendingActorInterfaceCommutation G1ActualSafeOwnInputRetention G1OriginalPrivateFutureExclusion
open G1PendingInterfaceEntryRecorder G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_other_opening_batch_safe (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (actor : BridgeActor T) (actors opening : List (BridgeActor T)) (hn : actor ∉ opening) :
    ∀ op ∈ canonicalOpeningBatchOps O D sample actors opening, SafeFor actor op := by
  induction opening generalizing actors with
  | nil => simp [canonicalOpeningBatchOps]
  | cons other opening ih =>
    have hne : actor ≠ other := by intro he; exact hn (List.mem_cons.mpr (Or.inl he))
    have ht : actor ∉ opening := fun hm => hn (List.mem_cons_of_mem other hm)
    intro op hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hne
    · exact ih _ ht op hm

noncomputable def ownOpeningPrefixOps (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (actor : BridgeActor T) :=
  let actors := canonicalExitActors O H D hD (O.calendar.age (actorInput O D actor))
    (originalExits O.network O.calendar (O.calendar.age (actorInput O D actor)))
  canonicalOpeningBatchOps O D sample actors (sourceOpenPrefix O H D hD actor) ++
  [AsyncOperation.interface actor (originalOpenKernel (originalInsideCopies O sample (actorInput O D actor))
    (activeOriginalBase O D sample (actors ++ sourceOpenPrefix O H D hD actor)))]

/-- The OWN interface's actual output is the entire original opaque inside
view of the real source frontier. Equal-date remaining opens cannot change
the value which the pending private kernel receives. -/
theorem actual_own_opening_coordinate_is_original_input (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (actor : BridgeActor T) (s : Code O.network sample)
    {middle : UnrankedView O.Vertex O.Edge Copy × (BridgeActor T → UnrankedView O.Vertex O.Edge Copy)}
    (hm : middle ∈ (asyncProgram (ownOpeningPrefixOps O H D hD sample actor)
      (canonicalExitProjection O H D hD (O.calendar.age (actorInput O D actor))
        (originalExits O.network O.calendar (O.calendar.age (actorInput O D actor))) s)).support) :
    middle.2 actor = unrankedView (selectedView (state s) (originalInsideCopies O sample (actorInput O D actor))) := by
  let actors := canonicalExitActors O H D hD (O.calendar.age (actorInput O D actor))
    (originalExits O.network O.calendar (O.calendar.age (actorInput O D actor)))
  let suffix := canonicalOpeningBatchOps O D sample ((actors ++ sourceOpenPrefix O H D hD actor) ++ [actor])
    (sourceOpenSuffix O H D hD actor)
  obtain ⟨final,hfinal⟩ := (asyncProgram suffix middle).support_nonempty
  have hfull : final ∈ (asyncProgram
      (canonicalOpeningBatchOps O D sample actors
        (canonicalOriginalOpeningActors O H D hD (O.calendar.age (actorInput O D actor))))
      (canonicalExitProjection O H D hD (O.calendar.age (actorInput O D actor))
        (originalExits O.network O.calendar (O.calendar.age (actorInput O D actor))) s)).support := by
    rw [actual_own_original_opening_runtime_cut,async_program_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨middle,hm,hfinal⟩
  rw [←actual_canonical_original_opening_batch_replay O H D hD (O.calendar.age (actorInput O D actor)) s] at hfull
  have he : final = canonicalDateProjection O D (O.calendar.age (actorInput O D actor)) s :=
    by simpa only [PMF.mem_support_pure_iff] using hfull
  have hn : actor ∉ sourceOpenSuffix O H D hD actor :=
    original_cut_absent_from_remaining _ actor (actual_original_opening_actor_nodup O H D hD _)
  have hretain := actual_safe_program_own_coordinate actor suffix
    (actual_other_opening_batch_safe O D sample actor _ _ hn) middle hfinal
  have ha : actor ∈ canonicalDateActors T (O.calendar.age (actorInput O D actor)) := by
    apply Finset.mem_toList.mpr
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change T.calendar.age (T.network.graph.target actor.val) ≤ O.calendar.age (actorInput O D actor) ∧
      O.calendar.age (actorInput O D actor) < T.calendar.age (T.network.graph.source actor.val)
    unfold actorInput
    rw [←D.calendar]
    exact ⟨le_rfl,T.calendar.edge_older actor.val⟩
  rw [he] at hretain
  rw [←hretain]
  simp only [canonicalDateProjection,originalAsyncProjection,originalPendingSlots,if_pos ha]

/-- The OWN recorded interface input is the same actual original opaque
coordinate. Additional record state changes neither its genealogy nor Gamma. -/
theorem actual_recorded_own_opening_coordinate_is_original_input (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (actor : BridgeActor T) (s : Code O.network sample) (records : List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy))
    {middle : (UnrankedView O.Vertex O.Edge Copy × List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy)) ×
      (BridgeActor T → UnrankedView O.Vertex O.Edge Copy)}
    (hm : middle ∈ (asyncProgram ((ownOpeningPrefixOps O H D hD sample actor).map interfaceRecordingLift)
      (withEntryRecords records (canonicalExitProjection O H D hD (O.calendar.age (actorInput O D actor))
        (originalExits O.network O.calendar (O.calendar.age (actorInput O D actor))) s))).support) :
    middle.2 actor = unrankedView (selectedView (state s) (originalInsideCopies O sample (actorInput O D actor))) := by
  have hf : forgetEntryRecords middle ∈ ((asyncProgram ((ownOpeningPrefixOps O H D hD sample actor).map interfaceRecordingLift)
      (withEntryRecords records (canonicalExitProjection O H D hD (O.calendar.age (actorInput O D actor))
        (originalExits O.network O.calendar (O.calendar.age (actorInput O D actor))) s))).map forgetEntryRecords).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨middle,hm,rfl⟩
  rw [actual_entry_record_program_forget] at hf
  exact actual_own_opening_coordinate_is_original_input O H D hD actor s hf

#print axioms actual_own_opening_coordinate_is_original_input
#print axioms actual_recorded_own_opening_coordinate_is_original_input
end G1CanonicalOwnEntryCoordinateAdmission
