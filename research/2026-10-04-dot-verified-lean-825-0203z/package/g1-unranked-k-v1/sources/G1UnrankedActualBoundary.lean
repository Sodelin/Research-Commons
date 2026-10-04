import G1UnrankedNaturalPulse

/-! Original deterministic, SAME-register COMMON and fresh CURRENT-owner
private boundary rows on the exact unranked causal view. Contributor: dot. -/
namespace G1UnrankedActualBoundary
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourceForestCommonPulse
open UnifiedLean.Source.SourceForestPulseTransport
open G1UnrankedSourceView G1UnrankedActualGenerator G1UnrankedActualEpoch G1UnrankedNaturalPulse
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_unranked_transport_view (v w : SelectedView V E Copy)
    (h : unrankedView v = unrankedView w) (f : Location V E → Location V E) :
    unrankedView (transportView v f) = unrankedView (transportView w f) := by
  apply UnrankedView.ext
  · change (fun x => UnifiedLean.Source.UnrankedGenealogyObservation.optionUnranked (v.genealogy x)) =
      (fun x => UnifiedLean.Source.UnrankedGenealogyObservation.optionUnranked (w.genealogy x))
    exact congrArg (fun q : UnrankedView V E Copy => q.genealogy) h
  · funext x
    exact congrArg (fun p => p x |>.map f) (unranked_view_population v w h)
  · exact unranked_view_register v w h

lemma actual_unranked_common_pulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy) (keep : Finset Copy) :
    unrankedView (selectedCommonPulse H v keep) =
      unrankedProjectedPulse H (unrankedView v) keep (fun _ => v.register H.hybrid) := by
  rw [selectedCommonPulse,actual_unranked_projected_pulse]
  rfl

local instance unrankedViewMeasurable : MeasurableSpace (UnrankedView V E Copy) := ⊤

/-- Every ACTUAL original boundary kernel descends to the complete unranked
state. A private pulse is derived by actual finite iid-coin reindexing; COMMON
retains the SAME original register, with no fresh marginal replacement. -/
theorem actual_unranked_boundary_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s z : Code N sample)
    (h : unrankedView (selectedView (state s) keep) = unrankedView (selectedView (state z) keep)) :
    (boundaryKernel N op s).map (unrankedProjection N keep) =
      (boundaryKernel N op z).map (unrankedProjection N keep) := by
  apply pmf_map_injective Subtype.val Subtype.val_injective
  simp only [PMF.map_comp,Function.comp_def,unrankedProjection]
  cases op with
  | exit e =>
      simp only [boundaryKernel,PMF.pure_map,exitCode_view]
      exact congrArg PMF.pure (actual_unranked_transport_view _ _ h (exitLocation N e))
  | ordinary e degree =>
      simp only [boundaryKernel,PMF.pure_map,ordinaryCode_view]
      exact congrArg PMF.pure (actual_unranked_transport_view _ _ h (ordinaryLocation N e))
  | root =>
      simp only [boundaryKernel,PMF.pure_map,rootCode_view]
      exact congrArg PMF.pure (actual_unranked_transport_view _ _ h (rootLocation N))
  | common H =>
      have hs := congrArg (fun p => p.map unrankedView) (common_boundary_kernel_view (N:=N) H s keep)
      have hz := congrArg (fun p => p.map unrankedView) (common_boundary_kernel_view (N:=N) H z keep)
      simp only [PMF.map_comp,Function.comp_def,PMF.pure_map,actual_unranked_common_pulse] at hs hz
      rw [hs,hz,h,unranked_view_register _ _ h]
  | independent H gamma =>
      apply PMF.toMeasure_injective
      change ((independentPulseKernel H gamma s).map _).toMeasure =
        ((independentPulseKernel H gamma z).map _).toMeasure
      rw [actual_source_unranked_private_boundary_measure,actual_source_unranked_private_boundary_measure,h]

noncomputable def unrankedBoundary (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (v : UnrankedIndex N sample keep) :
    PMF (UnrankedIndex N sample keep) :=
  (boundaryKernel N op (unrankedRepresentative N keep v)).map (unrankedProjection N keep)

theorem actual_unranked_source_boundary (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s : Code N sample) :
    (boundaryKernel N op s).map (unrankedProjection N keep) =
      unrankedBoundary N keep op (unrankedProjection N keep s) := by
  exact actual_unranked_boundary_row_independent N keep op s _
    (unrankedRepresentative_view N keep (unrankedProjection N keep s)).symm

#print axioms actual_unranked_boundary_row_independent
end G1UnrankedActualBoundary
