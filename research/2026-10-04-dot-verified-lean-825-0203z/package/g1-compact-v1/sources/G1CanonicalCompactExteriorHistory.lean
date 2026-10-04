import G1CanonicalCompactCompletedReplacement

/-! The actual canonical K macro retains the entire actual exterior unranked
checkpoint history through the SAME original future and completion.
Contributor: dot, 2026-10-03. Within-epoch clock/event observers are excluded. -/
namespace G1CanonicalCompactExteriorHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCompletionHarmonic
open G1CutChildPorts G1ActualTwoPortBlob G1OriginalRegistryBigon G1ExtractedComponentProgram
open G1ActualEnteringFrontier G1InitializedFrontierPrefix G1CanonicalComponentSegment
open G1OriginalCalendarDecomposition G1CanonicalCompactCompletedReplacement G1CanonicalSingleExitSupport
open G1ActualJointProgram G1ActualJointEpoch G1ActualJointStageHistory
open G1UnrankedSourceView G1UnrankedExteriorHistoryKInsertion G1ActualCompletedKInsertion
open G1CompletedExteriorHistoryKInsertion G1JointUnrankedForestAssembly G1JointForestPreservation
open G1CanonicalCompletedFutureRootAdmission G1OriginalCompletedForestReconstruction
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

theorem actual_canonical_compact_K_whole_exterior_history {Obs : Type*}
    (N : RootedBinary V E X) (hc : CutChild N) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (s : Code N sample)
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
      (initialCode N sample register)).support)
    (readout : List (UnrankedView V E Copy) → UnrankedView V E Copy → Obs) :
    let B := registryAlignedBigon N hc b A H
    let inside := enteringRoots N s (N.graph.target A.child)
    let outside := exteriorRoots N s (N.graph.target A.child)
    let phase := componentAgenda N C b B H gamma common
    let future := originalFuture N C b B H gamma common
    (sourceStageHistory N r phase s).bind (fun tr =>
      ((sourceProgram N r future (tr.getLastD s)).bind (completionKernel N r)).map
        (fun d => readout (exteriorHistory N outside tr)
          (unrankedView (selectedView (state d) (inside ∪ outside))))) =
      (independentProduct
        (G1ActualKProductInsertion.actualCurrentRootK N r (componentProgram N hc C b B
          (gamma (originalHybrid N b B)) (common (originalHybrid N b B))) s inside (Finset.filter_subset _ _))
        ((sourceStageHistory N r phase s).map (exteriorHistory N outside))).bind
          (fun data => completedKContinuation N r inside outside phase future s (readout data.2)
            (data.1,data.2.getLastD (unrankedView (selectedView (state s) outside)))) := by
  dsimp only
  let B := registryAlignedBigon N hc b A H
  have hpart := actual_entering_root_partition N s (N.graph.target B.child)
  have hsep := actual_initialized_canonical_component_agenda N hc C b B sample register H gamma common r hs
  have hsingle := actual_initialized_canonical_single_exit N hc C b A sample register H gamma common r hs
  obtain ⟨_,hin,_⟩ := actual_initialized_cut_frontier N C sample register H gamma common r A.child A.child_bridge hs
  have h := actual_completed_K_whole_exterior_history N r
    (enteringRoots N s (N.graph.target B.child)) (exteriorRoots N s (N.graph.target B.child))
    (.node (N.graph.source B.entry)) (componentAgenda N C b B H gamma common)
    (originalFuture N C b B H gamma common) s (Finset.filter_subset _ _) hsep
    (fun d hd => ⟨actual_agenda_pruned_panel_separation N r _ _ _ s hsep
      (current_root_partition_pure (state s) s.property.forest _ _ hpart.1 hpart.2) hd,hsingle d hd⟩)
    (fun d hd z hz => actual_canonical_completed_future_root_support N C b B sample register H gamma common r hs hd hz)
    readout
  have hk := actual_canonical_compact_current_root_K N hc C b A H gamma common r
    (enteringRoots N s (N.graph.target A.child)) s (Finset.filter_subset _ _) hin
  change G1ActualKProductInsertion.actualCurrentRootK N r (componentAgenda N C b B H gamma common) s
    (enteringRoots N s (N.graph.target B.child)) (Finset.filter_subset _ _) =
    G1ActualKProductInsertion.actualCurrentRootK N r (componentProgram N hc C b B
      (gamma (originalHybrid N b B)) (common (originalHybrid N b B))) s
      (enteringRoots N s (N.graph.target B.child)) (Finset.filter_subset _ _) at hk
  rw [hk] at h
  exact h

#print axioms actual_canonical_compact_K_whole_exterior_history
end G1CanonicalCompactExteriorHistory
