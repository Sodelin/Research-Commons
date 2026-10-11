import G1OriginalCalendarDecomposition

/-! Actual complete original-calendar joint forest law via a derived cut
interface. Contributor: dot, 2026-10-03. Full source program equality and the
initialized graph/calendar separator are conclusions. Both current-root
subsource kernels and SAME-original future remain concrete source operations.
Compact unranked K-only admission and decorated core assembly are separate. -/
namespace G1FullOriginalCalendarJointLaw
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1CutChildPorts G1ActualTwoPortBlob G1ActualEnteringFrontier G1InitializedFrontierPrefix
open G1CanonicalComponentSegment G1OriginalCalendarDecomposition
open G1SameOriginalExteriorContinuation G1ActualJointOpaqueContext G1ActualJointEpoch
open G1OpaqueSourceGrafting G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- The COMPLETE naturally initialized original source law factors through
the actual CURRENT-root component and concurrently evolving exterior, restoring
all carried opaque trees and continuing the SAME original retained-root future.
No population separator or stochastic identity is a supplied premise. -/
theorem actual_full_original_calendar_joint_forest_law (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (sourceProgram N r (compiledCalendarProgram N C H gamma common) (initialCode N sample register)).map (rootForest N) =
      (sourceProgram N r (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
        (initialCode N sample register)).bindOnSupport (fun s hs =>
          (independentProduct
            (currentPanelProgramLaw N r (componentAgenda N C b A H gamma common) s
              (enteringRoots N s (N.graph.target A.child)) (Finset.filter_subset _ _))
            (currentPanelProgramLaw N r (componentAgenda N C b A H gamma common) s
              (exteriorRoots N s (N.graph.target A.child)) Finset.sdiff_subset)).bind
                (fun v => actualOriginalContinuation N r (state s).live (originalFuture N C b A H gamma common) s
                  (fun w => (unrankedForest w).image (graftUnranked (state s).genealogy))
                  (joinedPanelView (enteringRoots N s (N.graph.target A.child)) v))) := by
  rw [actual_full_calendar_component_decomposition N C b A H gamma common,List.append_assoc,
    UnifiedLean.Source.SourceCalendarPhysicalSupport.sourceProgram_append,PMF.map_bind]
  have hpart (s : Code N sample) := actual_entering_root_partition N s (N.graph.target A.child)
  have hpoint (s : Code N sample)
      (hs : s ∈ (sourceProgram N r (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
        (initialCode N sample register)).support) :=
    actual_same_original_full_forest_continuation N r
      (enteringRoots N s (N.graph.target A.child)) (exteriorRoots N s (N.graph.target A.child))
      (componentAgenda N C b A H gamma common) (originalFuture N C b A H gamma common) s
      (hpart s).1 (hpart s).2
      (actual_initialized_canonical_component_agenda N hc C b A sample register H gamma common r hs)
  change (sourceProgram N r (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
      (initialCode N sample register)).bind (fun s =>
        (sourceProgram N r (componentAgenda N C b A H gamma common ++ originalFuture N C b A H gamma common) s).map (rootForest N)) = _
  rw [← PMF.bindOnSupport_eq_bind]
  congr 1
  funext s hs
  exact hpoint s hs

end G1FullOriginalCalendarJointLaw
