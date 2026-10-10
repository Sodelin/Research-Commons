import G1OriginatedSpanRegistryAdmission

/-! Every constructed decorated bridge is admitted to its actual ORIGINAL
multi-span calendar row. Contributor: dot, 2026-10-03. This is full selected
source-row equality; repeated closing-cut/exterior/core assembly stays explicit. -/
namespace G1OriginatedBridgeCalendarAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalDecoratedSpan G1OriginalSpanCalendarDecomposition G1OriginalMultiSpanCalendarRow
open G1OriginatedSpanRegistryAdmission G1OriginalNodeBatchBinding G1CanonicalEpochBlockBinding
open G1ActualKProductInsertion G1ActualJointOpaqueContext
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_originated_bridge_calendar_source_row (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (keep : Finset Copy) (s : Code O.network sample)
    (hs : AtNodePanel (state s) keep (D.vertex (T.network.graph.target e))) :
    (sourceProgram O.network r (fullSpanAgenda O.network O.calendar H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e))) s).map (projection O.network keep) =
      (sourceProgram O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s).map
        (projection O.network keep) :=
  (actual_original_registered_span_calendar_row_and_exit O.network O.calendar H gamma common r keep
    (bridgeSpan O T D e he) (actual_originated_bridge_word_registered O H D hD e he) s hs).1

/-- Single original output population is DERIVED for every real canonical
multi-span support state, retaining all selected original genealogy/register. -/
theorem actual_originated_bridge_calendar_exit_support (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (keep : Finset Copy) (s : Code O.network sample)
    (hs : AtNodePanel (state s) keep (D.vertex (T.network.graph.target e)))
    {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r (fullSpanAgenda O.network O.calendar H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e))) s).support) :
    AtNodePanel (state d) keep (D.vertex (T.network.graph.source e)) := by
  have h := actual_original_registered_span_calendar_row_and_exit O.network O.calendar H gamma common r keep
    (bridgeSpan O T D e he) (actual_originated_bridge_word_registered O H D hD e he) s hs
  exact actual_block_exit_support_from_row O.network r keep _ _ s _ h.1 h.2 hd

/-- The canonical multi-span actual CURRENT-root K is exactly the generated
original-word K. Original descendant/sample/exterior sizes remain uncapped. -/
theorem actual_originated_bridge_current_root_K (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (e : T.Edge) (he : T.network.graph.IsBridge e) (keep : Finset Copy) (s : Code O.network sample)
    (hkeep : keep ⊆ (state s).live)
    (hs : AtNodePanel (state s) keep (D.vertex (T.network.graph.target e))) :
    actualCurrentRootK O.network r (fullSpanAgenda O.network O.calendar H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e))) s keep hkeep =
    actualCurrentRootK O.network r (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he))
      s keep hkeep := by
  dsimp only [actualCurrentRootK]
  rw [← actual_current_panel_program_law,← actual_current_panel_program_law]
  have h := congrArg (fun p => p.map Subtype.val)
    (actual_originated_bridge_calendar_source_row O H D hD r gamma common e he keep s hs)
  simp only [PMF.map_comp,Function.comp_def,projection] at h
  rw [h]

#print axioms actual_originated_bridge_current_root_K
end G1OriginatedBridgeCalendarAdmission
