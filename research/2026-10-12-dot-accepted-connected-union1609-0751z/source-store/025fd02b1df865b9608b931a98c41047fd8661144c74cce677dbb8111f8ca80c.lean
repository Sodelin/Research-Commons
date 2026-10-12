import G1ActualActorOwnedPrivateSyntax

/-! The concrete pending private row is SOURCE-DERIVED and equals the TRUE
current-root OriginalSpan K graft at every real original opening. It depends
only on the complete original unranked inside input, not hidden code IDs or
exterior genealogy. This does not supply a desired kernel field to a plan. -/
namespace G1CanonicalPendingTrueKExposure
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceForestSilentPruning
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalExtractedPrivateKWord
open G1OriginalActorPrivateWordKernel G1ActualOriginalUnrankedLocalKernel G1FinitePendingActorPromotion
open G1CanonicalOriginalKOnlyActorRow G1UnrankedSourceView G1OriginalExteriorCohort G1InitializedFrontierPrefix
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalPendingKRow (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) :=
  originalLocalRow O.network sample r (originalActorInsideCopies O sample (actorInput O D actor))
    (extractedActorWord O H D hD actor gamma common)

/-- The emitted whole ORIGINAL inside view is exactly TRUE independently
initialized CURRENT-root OriginalSpan K, grafted onto the saved old entering
subtrees at the derived one original exit with the SAME register. -/
theorem actual_canonical_pending_row_is_true_K_graft (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support) :
    canonicalPendingKRow O H D hD sample gamma common r actor
      (unrankedView (selectedView (state s) (originalActorInsideCopies O sample (actorInput O D actor)))) =
      canonicalOriginalKActorRow O D gamma common r actor.val actor.property s := by
  have hk := actual_extracted_private_word_true_K_graft O H D hD actor sample register gamma common r s hs
  rw [actual_original_source_private_word] at hk
  exact hk

/-- TRUE K graft exposure is independent of both hidden current-root IDs and
exterior state: only the complete ORIGINAL unranked entering inside view is
an argument to the actual source-derived pending kernel. -/
theorem actual_true_K_graft_original_input_independent (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (firstRegister lastRegister : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (first last : Code O.network sample)
    (hf : first ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (actorInput O D actor))) (initialCode O.network sample firstRegister)).support)
    (hl : last ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (actorInput O D actor))) (initialCode O.network sample lastRegister)).support)
    (hinput : unrankedView (selectedView (state first) (originalActorInsideCopies O sample (actorInput O D actor))) =
      unrankedView (selectedView (state last) (originalActorInsideCopies O sample (actorInput O D actor)))) :
    canonicalOriginalKActorRow O D gamma common r actor.val actor.property first =
      canonicalOriginalKActorRow O D gamma common r actor.val actor.property last := by
  rw [←actual_canonical_pending_row_is_true_K_graft O H D hD sample firstRegister gamma common r actor first hf,
    ←actual_canonical_pending_row_is_true_K_graft O H D hD sample lastRegister gamma common r actor last hl,hinput]

#print axioms actual_canonical_pending_row_is_true_K_graft
#print axioms actual_true_K_graft_original_input_independent
end G1CanonicalPendingTrueKExposure
