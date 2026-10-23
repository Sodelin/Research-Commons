import G1OriginalDescendantCohortAgenda
import G1OriginalSpanClosingSourceRow

/-!
UNCOMPILED use-site composition, existing G3 owner,22October2026UTC.
Inside: literal registered OriginalSpan. Outside: the actual evolving closing
calendar program. SAME original graph/rates/register throughout. The initialized
specialization derives its guards from the actual original frontier. No numerical
kernel, fresh graph, word bound or NO-completeness assumption is introduced.
-/
namespace G3OriginalClosingWordJoint
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginatedSpanRegistryAdmission
open G1OriginalSpanCalendarDecomposition G1OriginalSpanBridgeBookends
open G1OriginatedBridgeBookends G1OriginalSpanClosingPhase G1OriginatedClosingSourceAdmission
open G1OriginalSpanClosingSourceRow G1OriginalNodeBatchBinding G1InitializedFrontierPrefix
open G1OriginalExteriorCohort G1ActiveCoreBridgeCohorts
open G1JointSeparatedSourceGeometry G1ActualJointGenerator G1ActualJointProgram
open G1OriginalDescendantCohortAgenda
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

theorem actual_registered_closing_joint_word
    (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (inside outside : Finset Copy)
    {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (hr : RegistrySpan O.network H word) (edge : O.Edge) (hend : EndsAt O edge word)
    (s : Code O.network sample) (hs : AtNodePanel (state s) inside a)
    (hsep : SeparatedAgenda O.network r inside outside
      (closingSpanAgenda O H gamma common a b edge) s) :
    (sourceProgram O.network r (closingSpanAgenda O H gamma common a b edge) s).map
      (jointProjection O.network inside outside) =
      independentProduct
        ((sourceProgram O.network r (spanProgram O.network O.calendar gamma common word) s).map
          (projection O.network inside))
        (selectedProgram O.network r outside (closingSpanAgenda O H gamma common a b edge)
          (projection O.network outside s)) := by
  calc
    _ = independentProduct
        (selectedProgram O.network r inside (closingSpanAgenda O H gamma common a b edge)
          (projection O.network inside s))
        (selectedProgram O.network r outside (closingSpanAgenda O H gamma common a b edge)
          (projection O.network outside s)) :=
      actual_separated_joint_program_law O.network r inside outside _ s hsep
    _ = _ := by
      apply congrArg (fun law => independentProduct law
        (selectedProgram O.network r outside (closingSpanAgenda O H gamma common a b edge)
          (projection O.network outside s)))
      exact (actual_source_program_projection O.network r inside
        (closingSpanAgenda O H gamma common a b edge) s).symm.trans
          (actual_registered_span_closing_source_row O H gamma common r inside word hr edge hend s hs)

/-- Existing actual Originated/frontier evidence supplies every physical guard;
there is no all-full-Code-live-at-input premise. -/
theorem actual_initialized_originated_closing_joint_word
    (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e))))
      (initialCode O.network sample register)).support) :
    let a := D.vertex (T.network.graph.target e)
    let b := D.vertex (T.network.graph.source e)
    let inside := originalInsideCopies O sample a
    let outside := originalOutsideCopies O sample a
    let phase := closingSpanAgenda O H gamma common a b (originatedLastCut O H D hD e he)
    (sourceProgram O.network r phase s).map (jointProjection O.network inside outside) =
      independentProduct
        ((sourceProgram O.network r
          (spanProgram O.network O.calendar gamma common (bridgeSpan O T D e he)) s).map
          (projection O.network inside))
        (selectedProgram O.network r outside phase (projection O.network outside s)) := by
  dsimp only
  have hbook := actual_bridge_span_bookends O T D e he
    (actual_originated_recipes_bookended O H D hD e)
  have hlast := actual_original_last_cut O (bridgeSpan O T D e he) hbook.2
  exact actual_registered_closing_joint_word O H gamma common r
    (originalInsideCopies O sample (D.vertex (T.network.graph.target e)))
    (originalOutsideCopies O sample (D.vertex (T.network.graph.target e)))
    (bridgeSpan O T D e he) (actual_originated_bridge_word_registered O H D hD e he)
    (originatedLastCut O H D hD e he) hlast.2.2 s
    (actual_initialized_all_original_descendants_at_input
      O H D hD sample register gamma common r e he hs)
    (actual_initialized_original_cohort_span_separator
      O H D hD sample register gamma common r e he hs)

#print axioms actual_registered_closing_joint_word
#print axioms actual_initialized_originated_closing_joint_word
end G3OriginalClosingWordJoint
