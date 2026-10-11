import G1ActualPrivateOriginalWordExtraction
import G1CanonicalKActorCompletedHistory

/-! The actually EXTRACTED private operation word has the TRUE CURRENT-root
OriginalSpan K-only graft row at every REAL original opening frontier. This
binds the private word used by finite pending algebra, rather than supplying
a desired actor kernel or replaying the full exterior phase in that actor. -/
namespace G1CanonicalExtractedPrivateKWord
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1OriginalSpanClosingPhase G1ClosingSpanSafeSyntax
open G1CanonicalActorLifecycleCompiler G1OriginalActorOperationOwnership G1PrivateActorLifetimeAdmission
open G1ActualPrivateOriginalWordExtraction G1SameOriginalExteriorContinuation G1ActualJointProgram
open G1OriginalDescendantCohortAgenda G1ActiveCoreBridgeCohorts G1OriginalExteriorCohort
open G1CanonicalOriginalKOnlyActorRow G1UnrankedSourceView G1ActualOriginalUnrankedLocalKernel
open G1OriginalActorPrivateWordKernel G1FinitePendingActorPromotion
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_source_panel_append (O : Source.{u,v,w} X)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (keep : Finset Copy) (first last : List (ProgramStep O.network)) (s : Code O.network sample) :
    (sourceProgram O.network r (first ++ last) s).map (projection O.network keep) =
      ((sourceProgram O.network r first s).map (projection O.network keep)).bind
        (selectedProgram O.network r keep last) := by
  simp only [actual_source_program_append,PMF.map_bind,PMF.bind_map,Function.comp_def]
  congr 1
  funext d
  exact actual_source_program_projection O.network r keep last d

noncomputable def extractedActorWord (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :=
  privateOriginalOps O (bridgeSpan O T D actor.val actor.property)
    (closingSpanAgenda O H gamma common (actorInput O D actor) (D.vertex (T.network.graph.source actor.val))
      (actorCut O H D hD actor))

lemma actual_actor_closing_private_row (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actor : BridgeActor T)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (keep : Finset Copy)
    (hin : ∀ x ∈ keep, SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    (sourceProgram O.network r (closingSpanAgenda O H gamma common (actorInput O D actor)
      (D.vertex (T.network.graph.source actor.val)) (actorCut O H D hD actor)) s).map (projection O.network keep) =
      (sourceProgram O.network r (extractedActorWord O H D hD actor gamma common) s).map (projection O.network keep) := by
  let word := bridgeSpan O T D actor.val actor.property
  let cut := actorCut O H D hD actor
  let beforeCut := closingSpanPrefix O H gamma common (actorInput O D actor) (D.vertex (T.network.graph.source actor.val)) cut
  have hkeepCut : privateStep O word (.boundary (.exit cut)) = true := by
    exact decide_eq_true (actual_actor_cut_in_region O H D hD actor)
  have hp := actual_safe_private_original_row O word cut (actual_actor_cut_ends_at O H D hD actor) H gamma common r beforeCut
    (actual_closing_span_prefix_safe O H gamma common _ _ cut (actual_actor_cut_source O H D hD actor)
      (G1OriginalSpanCalendarDecomposition.actual_span_dates_strict O.network O.calendar word)) s keep hin
  rw [actual_closing_span_prefix_last]
  have hfilter : extractedActorWord O H D hD actor gamma common =
      privateOriginalOps O word beforeCut ++ [.boundary (.exit cut)] := by
    rw [extractedActorWord,actual_closing_span_prefix_last]
    change privateOriginalOps O word (beforeCut ++ [.boundary (.exit cut)]) = _
    simp only [privateOriginalOps,List.filter_append,List.filter_cons,hkeepCut,List.filter_nil,if_true]
  rw [hfilter,actual_source_panel_append,actual_source_panel_append,hp]

/-- Actual extracted PRIVATE source word equals the independently initialized
CURRENT-root OriginalSpan K graft on the FULL original descendant actor panel.
All input, exit, cohort and forest support are derived at a real frontier. -/
theorem actual_extracted_private_word_true_K_graft (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (s : Code O.network sample)
    (hs : s ∈ (sourceProgram O.network r
      (G1InitializedFrontierPrefix.actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (actorInput O D actor))) (initialCode O.network sample register)).support) :
    actorWordKernel
      ((extractedActorWord O H D hD actor gamma common).map
        (fun op => originalLocalRow O.network sample r (originalActorInsideCopies O sample (actorInput O D actor)) [op]))
      (unrankedView (selectedView (state s) (originalActorInsideCopies O sample (actorInput O D actor)))) =
        canonicalOriginalKActorRow O D gamma common r actor.val actor.property s := by
  rw [actual_original_source_private_word,←actual_original_local_source_row]
  have hcohort : originalActorInsideCopies O sample (actorInput O D actor) = originalInsideCopies O sample (actorInput O D actor) := by
    ext x
    simp [originalActorInsideCopies,originalOutsideCopies,originalInsideCopies]
  have hin : ∀ x ∈ originalActorInsideCopies O sample (actorInput O D actor),
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x) := by
    intro x hx
    rw [hcohort] at hx
    rw [actual_initialized_all_original_descendants_at_input O H D hD sample register gamma common r actor.val actor.property hs x hx]
    exact actual_span_input_in_region O _
  have hrow := congrArg (fun p => p.map (fun v => unrankedView v.val))
    (actual_actor_closing_private_row O H D hD actor gamma common r s _ hin)
  simp only [PMF.map_comp,projection,Function.comp_def] at hrow
  have hK := actual_canonical_original_actor_row_is_K_only O H D hD sample register gamma common r
    actor.val actor.property s hs
  rw [←actual_source_program_projection,PMF.map_comp] at hK
  exact hrow.symm.trans hK

#print axioms actual_extracted_private_word_true_K_graft
end G1CanonicalExtractedPrivateKWord
