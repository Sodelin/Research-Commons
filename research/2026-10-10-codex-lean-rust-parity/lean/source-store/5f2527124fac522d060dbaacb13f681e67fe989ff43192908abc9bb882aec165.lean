import G1OwnOpeningKInputCut

/-! Actual inputs to EVERY true-K block of the SAME all-original-bridge
interpreter are genuine real original current-root frontier inputs. This
derives opaque genealogy/population/SAME-register support through promotion. -/
namespace G1EveryPromotedKInputRealCurrentRoot
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCalendarCompatibility
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalOriginalExitAsyncStep
open G1CanonicalOwnTwoInterfaceRuntime G1CanonicalInitializedWholeCalendarHistory G1InitializedFrontierPrefix
open G1CanonicalPendingTrueKExposure G1CanonicalOriginalKOnlyActorRow G1OriginalExteriorCohort
open G1AllOriginalPromotedKLabels G1ExactPromotionInterfaceRecordLift G1OwnOpeningKInputCut
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1WholeFinitePendingPromotion
open G1PendingInterfaceEntryRecorder G1PendingBaseCheckpointRecorder G1OwnProtocolSignatureTransport
open G1FirstOwnInterfaceRecordSupport G1ActualKInputFirstRecord G1PromotedFirstEntryRealSourceSupport
open G1ActiveCoreBridgeCohorts G1UnrankedSourceView
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Every actual computation input, rather than only its stored row label,
is admitted by the original source-derived CURRENT-root K-graft theorem.
No cached whole Code, desired row identity, or original leaf-count cap is a
premise. Its witness uses the SAME graph/calendar/control/rates/register. -/
theorem actual_every_promoted_K_input_is_real_current_root (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (actor : BridgeActor T) (history : List (UnrankedView O.Vertex O.Edge Copy)) :
    ∃ before gap later opening,
      (ownRuntimeParts O H D hD sample gamma common r actor).opening = AsyncOperation.interface actor opening ∧
      promoteEveryActor (Finset.univ.toList) (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r) =
        before ++ .interface actor opening ::
          (gap ++ .localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor) :: later) ∧
      ∀ input : ((UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)) ×
          List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy)) × (BridgeActor T → UnrankedView O.Vertex O.Edge Copy),
        input ∈ (asyncProgram ((before ++ [AsyncOperation.interface actor opening] ++ gap).map interfaceRecordingLift)
          (withEntryRecords [] (withBaseHistory history
            (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
              (initialCode O.network sample register))))).support →
        ∃ s : Code O.network sample,
          s ∈ (sourceProgram O.network r
            (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
              (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support ∧
          input.2 actor = unrankedView (selectedView (state s) (originalInsideCopies O sample (actorInput O D actor))) ∧
          canonicalPendingKRow O H D hD sample gamma common r actor (input.2 actor) =
            canonicalOriginalKActorRow O D gamma common r actor.val actor.property s := by
  let parts := ownRuntimeParts O H D hD sample gamma common r actor
  obtain ⟨opening,ho⟩ : ∃ opening, parts.opening = AsyncOperation.interface actor opening := ⟨_,rfl⟩
  obtain ⟨left,right,hl,_,hs⟩ := actual_all_original_bridge_K_labels O H D hD sample gamma common r actor
  change ownProtocolSignature actor _ = left ++ [parts.opening] ++ _ ++ [parts.closing] ++ right at hs
  rw [ho] at hs
  have hs' : ownProtocolSignature actor
      (promoteEveryActor (Finset.univ.toList) (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)) =
      left ++ .interface actor opening :: .localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor) ::
        (parts.closing :: right) := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using hs
  obtain ⟨before,gap,later,hlist,hb,hg⟩ := actual_optional_identity_open_kernel_cut actor _ opening
    (canonicalPendingKRow O H D hD sample gamma common r actor) _ left hl hs'
  refine ⟨before,gap,later,opening,ho,hlist,?_⟩
  intro input hi
  let initial := withEntryRecords ([] : List (BridgeActor T × UnrankedView O.Vertex O.Edge Copy))
    (withBaseHistory history (canonicalExitProjection O H D hD (firstOriginalDate O.network O.calendar) []
      (initialCode O.network sample register)))
  let suffix := AsyncOperation.localStep actor (canonicalPendingKRow O H D hD sample gamma common r actor) :: later
  have hfirst := actual_input_after_open_and_other_work_is_first_record actor before gap hb hg opening initial
    (by simp [initial,withEntryRecords,NoOwnRecord]) hi
  obtain ⟨out,hout⟩ := (asyncProgram (suffix.map interfaceRecordingLift) input).support_nonempty
  have hall : out ∈ (asyncProgram (promoteEveryActor (Finset.univ.toList)
      ((canonicalRecordedWholeCalendarOps O H D hD sample gamma common r).map interfaceRecordingLift)) initial).support := by
    rw [actual_every_actor_promotion_record_lift,hlist]
    have he : before ++ .interface actor opening :: (gap ++ suffix) =
        (before ++ [AsyncOperation.interface actor opening] ++ gap) ++ suffix := by
      simp only [List.append_assoc,List.cons_append,List.nil_append]
    change out ∈ (asyncProgram ((before ++ .interface actor opening :: (gap ++ suffix)).map interfaceRecordingLift) initial).support
    rw [he,List.map_append,async_program_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨input,hi,hout⟩
  obtain ⟨s,hs,hsourceRecord⟩ := actual_promoted_first_entry_record_has_real_source O H D hD sample register gamma common r
    actor history hall
  have hinputRecord := actual_first_own_record_persists actor (input.2 actor) suffix input hfirst hout
  have hvalue := actual_first_own_record_unique actor (input.2 actor)
    (unrankedView (selectedView (state s) (originalInsideCopies O sample (actorInput O D actor)))) out.1.2
    hinputRecord hsourceRecord
  refine ⟨s,hs,hvalue,?_⟩
  have hpanel : originalActorInsideCopies O sample (actorInput O D actor) = originalInsideCopies O sample (actorInput O D actor) := by
    ext x
    simp [originalActorInsideCopies,originalOutsideCopies,originalInsideCopies]
  have hK := actual_canonical_pending_row_is_true_K_graft O H D hD sample register gamma common r actor s hs
  rw [hpanel] at hK
  rw [hvalue]
  exact hK

#print axioms actual_every_promoted_K_input_is_real_current_root
end G1EveryPromotedKInputRealCurrentRoot
