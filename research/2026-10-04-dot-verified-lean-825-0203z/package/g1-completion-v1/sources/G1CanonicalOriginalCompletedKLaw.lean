import G1CompletedExteriorHistoryKInsertion

/-! Original initialized canonical component to complete original forest law.
Only the final single-exit population binding remains as a physical premise;
initialization, separation, purity and ancestral root admission are derived.
Contributor: dot, 2026-10-03. -/
namespace G1CanonicalOriginalCompletedKLaw
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open G1CutChildPorts G1ActualTwoPortBlob G1ActualEnteringFrontier G1InitializedFrontierPrefix
open G1CanonicalComponentSegment G1OriginalCalendarDecomposition
open G1ContextualForestReplacement G1JointUnrankedForestAssembly G1JointForestPreservation
open G1ActualJointEpoch G1ActualKProductInsertion G1ActualCompletedKInsertion
open G1OriginalCompletedForestReconstruction G1CanonicalCompletedFutureRootAdmission
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

theorem actual_canonical_original_completed_K_law (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (s : Code N sample)
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
      (initialCode N sample register)).support)
    (singleExit : ∀ d ∈ (sourceProgram N r (componentAgenda N C b A H gamma common) s).support,
      ∀ x ∈ enteringRoots N s (N.graph.target A.child),
        copyLocation (state d) x = .node (N.graph.source A.entry)) :
    ((sourceProgram N r (componentAgenda N C b A H gamma common ++
      originalFuture N C b A H gamma common) s).bind
        (UnifiedLean.Source.SourceCompletionHarmonic.completionKernel N r)).map (rootForest N) =
      (independentProduct
        (actualCurrentRootK N r (componentAgenda N C b A H gamma common) s
          (enteringRoots N s (N.graph.target A.child)) (Finset.filter_subset _ _))
        (actualExteriorUnrankedState N r (componentAgenda N C b A H gamma common) s
          (exteriorRoots N s (N.graph.target A.child)) Finset.sdiff_subset)).bind
            (completedKContinuation N r (enteringRoots N s (N.graph.target A.child))
              (exteriorRoots N s (N.graph.target A.child)) (componentAgenda N C b A H gamma common)
              (originalFuture N C b A H gamma common) s
              (fun v => (G1UnrankedActualFuture.unrankedViewForest v).image
                (G1OpaqueSourceGrafting.graftUnranked (state s).genealogy))) := by
  have hpart := actual_entering_root_partition N s (N.graph.target A.child)
  have hsep := actual_initialized_canonical_component_agenda N hc C b A sample register H gamma common r hs
  apply actual_original_completed_K_product_insertion N r
    (enteringRoots N s (N.graph.target A.child)) (exteriorRoots N s (N.graph.target A.child))
    (.node (N.graph.source A.entry)) (componentAgenda N C b A H gamma common)
    (originalFuture N C b A H gamma common) s _ _ hpart.1 hsep
  · intro d hd
    exact ⟨actual_agenda_pruned_panel_separation N r _ _ _ s hsep
      (current_root_partition_pure (state s) s.property.forest _ _ hpart.1 hpart.2) hd,singleExit d hd⟩
  · intro d hd z hz
    exact actual_canonical_completed_future_root_support N C b A sample register H gamma common r hs hd hz

#print axioms actual_canonical_original_completed_K_law
end G1CanonicalOriginalCompletedKLaw
