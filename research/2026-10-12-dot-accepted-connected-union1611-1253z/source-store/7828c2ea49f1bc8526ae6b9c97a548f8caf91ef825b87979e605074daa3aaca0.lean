import G1CanonicalSingleExitSupport
import G1CanonicalOriginalCompletedKLaw

/-! Canonical complete original source with its source-derived compact K.
Contributor: dot, 2026-10-03. Single exit, purity, separation and ancestral
completion admission are derived. This is ONE actual component replacement;
repeated decorated-core/displayed/sharpness assembly remains separate. -/
namespace G1CanonicalCompactCompletedReplacement
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalNodeBatchBinding G1CanonicalCompactComponentRow G1CanonicalSingleExitSupport
open G1ExtractedComponentProgram G1OriginalRegistryBigon G1ActualJointOpaqueContext
open G1CutChildPorts G1ActualTwoPortBlob G1CanonicalComponentSegment
open G1ActualEnteringFrontier G1InitializedFrontierPrefix G1OriginalCalendarDecomposition
open G1ActualKProductInsertion G1ActualCompletedKInsertion G1CanonicalOriginalCompletedKLaw
open G1ActualJointEpoch
open G1ContextualForestReplacement G1JointUnrankedForestAssembly
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- The macro K is the TRUE CURRENT-root compact original source law. -/
theorem actual_canonical_compact_current_root_K (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) (hkeep : keep ⊆ (state s).live)
    (hs : AtNodePanel (state s) keep (N.graph.target A.child)) :
    let B := registryAlignedBigon N hc b A H
    actualCurrentRootK N r (componentAgenda N C b B H gamma common) s keep hkeep =
      actualCurrentRootK N r (componentProgram N hc C b B
        (gamma (originalHybrid N b B)) (common (originalHybrid N b B))) s keep hkeep := by
  dsimp only [actualCurrentRootK]
  rw [← actual_current_panel_program_law,← actual_current_panel_program_law]
  have h := congrArg (fun p => p.map Subtype.val)
    (actual_canonical_compact_component_row N hc C b A H gamma common r keep s hs)
  simp only [PMF.map_comp,Function.comp_def,projection] at h
  rw [h]

/-- One derived actual canonical component can be replaced by its compact
K-label in the complete ORIGINAL forest law, including actual unbounded root
completion and every entering opaque subtree. The cap counts entering roots. -/
theorem actual_cap_m_canonical_compact_completed_replacement (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (hb : b ≠ N.graph.blobOf N.root)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (s : Code N sample)
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
      (initialCode N sample register)).support)
    (m : Nat) (cap : (enteringRoots N s (N.graph.target A.child)).card ≤ m) :
    let B := registryAlignedBigon N hc b A H
    let inside := enteringRoots N s (N.graph.target A.child)
    let outside := exteriorRoots N s (N.graph.target A.child)
    Fintype.card (SelectedCopy inside) ≤ m ∧
    (∀ v, (v = B.fragment.upper ∨ v = B.fragment.parents.hybrid) →
      N.graph.blobOf v ≠ N.graph.blobOf N.root) ∧
    ((sourceProgram N r (componentAgenda N C b B H gamma common ++
      originalFuture N C b B H gamma common) s).bind
        (UnifiedLean.Source.SourceCompletionHarmonic.completionKernel N r)).map (rootForest N) =
      (independentProduct
        (actualCurrentRootK N r (componentProgram N hc C b B
          (gamma (originalHybrid N b B)) (common (originalHybrid N b B))) s inside (Finset.filter_subset _ _))
        (actualExteriorUnrankedState N r (componentAgenda N C b B H gamma common) s outside Finset.sdiff_subset)).bind
          (completedKContinuation N r inside outside (componentAgenda N C b B H gamma common)
            (originalFuture N C b B H gamma common) s
            (fun v => (G1UnrankedActualFuture.unrankedViewForest v).image
              (G1OpaqueSourceGrafting.graftUnranked (state s).genealogy))) := by
  dsimp only
  let B := registryAlignedBigon N hc b A H
  obtain ⟨_,hin,_⟩ := actual_initialized_cut_frontier N C sample register H gamma common r A.child A.child_bridge hs
  refine ⟨?_,actual_extracted_internal_vertices_exclude_root_blob N b hb B,?_⟩
  · simpa only [SelectedCopy,Fintype.card_coe] using cap
  · have h := actual_canonical_original_completed_K_law N hc C b B sample register H gamma common r s hs
      (actual_initialized_canonical_single_exit N hc C b A sample register H gamma common r hs)
    have hk := actual_canonical_compact_current_root_K N hc C b A H gamma common r
      (enteringRoots N s (N.graph.target A.child)) s (Finset.filter_subset _ _) hin
    change actualCurrentRootK N r (componentAgenda N C b B H gamma common) s
      (enteringRoots N s (N.graph.target B.child)) (Finset.filter_subset _ _) =
      actualCurrentRootK N r (componentProgram N hc C b B
        (gamma (originalHybrid N b B)) (common (originalHybrid N b B))) s
        (enteringRoots N s (N.graph.target B.child)) (Finset.filter_subset _ _) at hk
    rw [hk] at h
    exact h

#print axioms actual_cap_m_canonical_compact_completed_replacement
end G1CanonicalCompactCompletedReplacement
