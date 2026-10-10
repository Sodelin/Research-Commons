import G1OriginalSpanClosingPhase

/-! Full selected source row at the PRECISE last original cut-edge exit.
Contributor: dot, 2026-10-03. Remaining same-date exits/nodes stay exterior. -/
namespace G1OriginalSpanClosingSourceRow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1OriginalSpanBridgeBookends
open G1OriginalSpanClosingPhase G1OriginalSpanCalendarDecomposition G1OriginalMultiSpanCalendarRow
open G1OriginalNodeBatchBinding G1CanonicalEpochBlockBinding G1CompactSourceComposition
open G1CompactComponentBlockRows G1ExtractedComponentProgram G1ActualJointProgram
open G1SameOriginalExteriorContinuation
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_registered_span_closing_source_row (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (keep : Finset Copy) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (hr : RegistrySpan O.network H word)
    (edge : O.Edge) (hend : EndsAt O edge word) (s : Code O.network sample)
    (hs : AtNodePanel (state s) keep a) :
    (sourceProgram O.network r (closingSpanAgenda O H gamma common a b edge) s).map (projection O.network keep) =
      (sourceProgram O.network r (spanProgram O.network O.calendar gamma common word) s).map
        (projection O.network keep) := by
  induction word generalizing s with
  | edge e degree =>
      have he : e = edge := hend
      subst edge
      have hm : e ∈ closingExits O e := by simp [closingExits]
      simpa only [closingSpanAgenda,spanProgram] using
        (actual_canonical_ordinary_block_row O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
          r keep e degree (closingExits O e) hm s hs)
  | bigon B => exact False.elim hend
  | @append a mid b first last ihfirst ihlast =>
      obtain ⟨hrfirst,hrlast⟩ := hr
      have hfirst := actual_original_registered_span_calendar_row_and_exit O.network O.calendar H gamma common r keep
        first hrfirst s hs
      have hactualout {d : Code O.network sample}
          (hd : d ∈ (sourceProgram O.network r (fullSpanAgenda O.network O.calendar H gamma common a mid) s).support) :
          AtNodePanel (state d) keep mid :=
        actual_block_exit_support_from_row O.network r keep _ _ s mid hfirst.1 hfirst.2 hd
      rw [actual_closing_span_agenda_append O H gamma common a mid b edge
        (actual_span_dates_strict O.network O.calendar first) (actual_span_dates_strict O.network O.calendar last)]
      change (sourceProgram O.network r (fullSpanAgenda O.network O.calendar H gamma common a mid ++
        closingSpanAgenda O H gamma common mid b edge) s).map (projection O.network keep) =
        (sourceProgram O.network r (spanProgram O.network O.calendar gamma common first ++
          spanProgram O.network O.calendar gamma common last) s).map (projection O.network keep)
      calc
        _ = (sourceProgram O.network r (fullSpanAgenda O.network O.calendar H gamma common a mid ++
            spanProgram O.network O.calendar gamma common last) s).map (projection O.network keep) := by
          rw [actual_source_program_append,actual_source_program_append,PMF.map_bind,PMF.map_bind]
          apply bind_eq_of_eq_on_support
          intro d hd
          exact ihlast hrlast hend d (hactualout hd)
        _ = _ := actual_source_row_suffix_congr O.network r keep _ _ _ s hfirst.1

theorem actual_registered_span_closing_exit_support (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (keep : Finset Copy) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (hr : RegistrySpan O.network H word)
    (edge : O.Edge) (hend : EndsAt O edge word) (s : Code O.network sample)
    (hs : AtNodePanel (state s) keep a) {d : Code O.network sample}
    (hd : d ∈ (sourceProgram O.network r (closingSpanAgenda O H gamma common a b edge) s).support) :
    AtNodePanel (state d) keep b :=
  actual_block_exit_support_from_row O.network r keep _ _ s b
    (actual_registered_span_closing_source_row O H gamma common r keep word hr edge hend s hs)
    (actual_original_registered_span_calendar_row_and_exit O.network O.calendar H gamma common r keep word hr s hs).2 hd

#print axioms actual_registered_span_closing_source_row
end G1OriginalSpanClosingSourceRow
