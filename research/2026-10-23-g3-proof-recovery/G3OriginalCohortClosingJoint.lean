import G1OriginalDescendantCohortAgenda
import G7WholeAncestorPanelCode
import G7PopulationForestReassembly

/-!
UNCOMPILED source composition, 22 October 2026. Reuses the exact original
frontier/Originated separator and joint-program theorems. No desired law,
all-live-at-one-node premise, independence axiom or sorry is introduced.

This concludes the conditional JOINT selected inside/exterior PMF law on
ONE existing original source and its exact closing calendar segment. It
does not construct a new source, identify a canonical M kernel, freeze an
evolving exterior, or prove cross-source/full-quartet readout equality.
-/
namespace GProgram.G3.OriginalCohortClosingJoint

set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceInitializedCalendar
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalDecoratedSpan G1OriginatedClosingSourceAdmission G1OriginalSpanClosingPhase
open G1InitializedFrontierPrefix G1OriginalExteriorCohort G1ActiveCoreBridgeCohorts
open G1JointSeparatedSourceGeometry G1ActualJointGenerator G1ActualJointProgram
open G1OriginalDescendantCohortAgenda
open scoped Classical

universe u v w
variable {X : Type w} [Fintype X]

/-- The actual old descendant cohort, with concurrent exterior roots allowed.
Natural register mixing is outside this conditional entering-Code identity. -/
theorem actual_initialized_cohort_closing_joint
    (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (e : T.Edge) (he : T.network.graph.IsBridge e)
    {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H
        (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age (D.vertex (T.network.graph.target e))))
      (initialCode O.network sample register)).support) :
    let inside := originalInsideCopies O sample (D.vertex (T.network.graph.target e))
    let outside := originalOutsideCopies O sample (D.vertex (T.network.graph.target e))
    let ops := closingSpanAgenda O H gamma common
      (D.vertex (T.network.graph.target e)) (D.vertex (T.network.graph.source e))
      (originatedLastCut O H D hD e he)
    (sourceProgram O.network r ops s).map (jointProjection O.network inside outside) =
      independentProduct
        (selectedProgram O.network r inside ops (projection O.network inside s))
        (selectedProgram O.network r outside ops (projection O.network outside s)) := by
  dsimp only
  apply actual_separated_joint_program_law
  exact actual_initialized_original_cohort_span_separator
    O H D hD sample register gamma common r e he hs

#print axioms actual_initialized_cohort_closing_joint

end GProgram.G3.OriginalCohortClosingJoint
