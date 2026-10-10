import G1CanonicalComponentSegment
import G1SameOriginalExteriorContinuation

/-! Actual initialized canonical component/exterior joint forest replacement.
Contributor: dot, 2026-10-03. The joint agenda separator and CURRENT-root
partition are DERIVED from original graph/calendar initialization. Both source
panels are actual current-root carriers; every opaque original tree is restored
and the SAME original exterior/root future continues without separation limits.
Canonical compact unranked component-label compression remains a later gate. -/
namespace G1InitializedJointComponentReplacement
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.UnrankedGenealogyObservation
open G1CutChildPorts G1ActualTwoPortBlob G1ActualEnteringFrontier G1InitializedFrontierPrefix
open G1CanonicalComponentSegment G1ActualJointOpaqueContext G1ActualJointEpoch
open G1SameOriginalExteriorContinuation G1OriginalCurrentRootReconstruction
open G1ContextualForestReplacement G1OpaqueSourceGrafting
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Both complete actual current-root panel laws replace the canonical
original interleaved phase inside the SAME original future. Only the inside
CURRENT roots are capped; original descendant/exterior labels are uncapped. -/
theorem actual_initialized_joint_component_forest_replacement (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (s : Code N sample)
    (hs : s ∈ (sourceProgram N r (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
      (initialCode N sample register)).support)
    (m : ℕ) (hcap : (enteringRoots N s (N.graph.target A.child)).card ≤ m)
    (future : List (ProgramStep N)) :
    Fintype.card (UnifiedLean.Source.SourceCopyCarrierTransport.SelectedCopy
      (enteringRoots N s (N.graph.target A.child))) ≤ m ∧
    (sourceProgram N r (componentAgenda N C b A H gamma common ++ future) s).map (rootForest N) =
      (independentProduct
        (currentPanelProgramLaw N r (componentAgenda N C b A H gamma common) s
          (enteringRoots N s (N.graph.target A.child)) (Finset.filter_subset _ _))
        (currentPanelProgramLaw N r (componentAgenda N C b A H gamma common) s
          (exteriorRoots N s (N.graph.target A.child)) Finset.sdiff_subset)).bind
            (fun v => actualOriginalContinuation N r (state s).live future s
              (fun w => (unrankedForest w).image (graftUnranked (state s).genealogy))
              (joinedPanelView (enteringRoots N s (N.graph.target A.child)) v)) := by
  have hpart := actual_entering_root_partition N s (N.graph.target A.child)
  have hagenda := actual_initialized_canonical_component_agenda N hc C b A sample register H gamma common r hs
  refine ⟨actual_inside_current_carrier_cap _ m hcap,?_⟩
  exact actual_same_original_full_forest_continuation N r _ _ _ future s hpart.1 hpart.2 hagenda

/-- All graph extraction assumptions are the accepted raw graph-class
conditions. The original blob shape is a DERIVED witness, not a premise. -/
theorem actual_raw_nonroot_two_port_initialized_joint_gate (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hp : Fintype.card (N.BlobPort b) = 2)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    let A := G1OriginalRegistryBigon.registryAlignedBigon N hc b
      (extractedBigon N hc b hb ((G1CutChildPorts.actual_quotient_port_card N b).symm.trans hp)) H
    ∀ (s : Code N sample),
      s ∈ (sourceProgram N r (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
        (initialCode N sample register)).support →
      G1ActualJointProgram.SeparatedAgenda N r
        (enteringRoots N s (N.graph.target A.child)) (exteriorRoots N s (N.graph.target A.child))
        (componentAgenda N C b A H gamma common) s := by
  dsimp only
  intro s hs
  exact actual_initialized_canonical_component_agenda N hc C b _ sample register H gamma common r hs

end G1InitializedJointComponentReplacement
