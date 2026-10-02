import UnifiedLean.Source.SourceSmallCarrierPulse

/-!
# Same ORIGINAL boundary law for actual full and small-copy sources

Contributor: dot, 2026-10-02. Derives all original edge exits, ordinary/root
entries, CURRENT-owner independent pulses and SAME-register COMMON pulses on
one original-labelled view. No source boundary kernel identity is an input.
-/
namespace UnifiedLean.Source.SourceCrossCarrierBoundary
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestPulseTransport
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceForestCommonPulse
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceSmallCarrierPulse
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma lift_transportView (keep : Finset Copy) (v : SelectedView V E (SelectedCopy keep))
    (f : Location V E → Location V E) :
    liftView keep (transportView v f) = transportView (liftView keep v) f := by
  apply SelectedView.ext
  · rfl
  · funext x
    by_cases hx : x ∈ keep <;> simp [liftView,transportView,hx]
  · rfl

local instance viewMeasurable : MeasurableSpace (SelectedView V E Copy) := ⊤

/-- The actual small-code Bernoulli PMF uses its genuine current live owners;
its whole original-labelled output law is the derived intrinsic pulse measure. -/
theorem small_independent_kernel_view_measure {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval) (keep : Finset Copy)
    (s : Code N (selectedSample sample keep)) :
    ((independentPulseKernel H gamma s).map
      (fun d => liftView keep (selectedView (state d) Finset.univ))).toMeasure =
      selectedPulseLaw H (liftView keep (selectedView (state s) Finset.univ)) keep gamma := by
  rw [independentPulseKernel,PMF.map_comp]
  have he : (fun d : Code N (selectedSample sample keep) =>
      liftView keep (selectedView (state d) Finset.univ)) ∘ pulseCode H s =
      (fun coin => liftView keep (selectedView (pulse H (state s) coin) Finset.univ)) := by
    funext coin
    rw [Function.comp_apply,pulseCode_view]
  rw [he,← PMF.toMeasure_map _ _ (measurable_of_countable _),currentCoinPMF,Measure.toPMF_toMeasure]
  exact small_original_pulse_law H keep (state s) s.property.forest gamma

/-- Actual COMMON small-source output retains the SAME original shared register,
never an independently refitted site coin or copied-tip randomizer. -/
theorem small_common_kernel_view {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (keep : Finset Copy)
    (s : Code N (selectedSample sample keep)) :
    (boundaryKernel N (.common H) s).map
      (fun d => liftView keep (selectedView (state d) Finset.univ)) =
      PMF.pure (selectedCommonPulse H (liftView keep (selectedView (state s) Finset.univ)) keep) := by
  rw [boundaryKernel,PMF.pure_map,pulseCode_view,small_current_owner_pulse_view H keep (state s) s.property.forest]
  congr 1

/-- Each whole actual original boundary PMF agrees across the full and
independently initialized selected-copy sources on their common pruned view. -/
theorem actual_cross_carrier_boundary_law (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s : Code N sample)
    (z : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state z) Finset.univ)) :
    (boundaryKernel N op s).map (fun d => joinedProjection N keep (.inl d)) =
      (boundaryKernel N op z).map (fun d => joinedProjection N keep (.inr d)) := by
  apply pmf_map_injective Subtype.val Subtype.val_injective
  simp only [PMF.map_comp,Function.comp_def,joinedProjection,joinedView]
  cases op with
  | exit e => simp only [boundaryKernel,PMF.pure_map,exitCode_view,lift_transportView,hs]
  | ordinary e degree => simp only [boundaryKernel,PMF.pure_map,ordinaryCode_view,lift_transportView,hs]
  | root => simp only [boundaryKernel,PMF.pure_map,rootCode_view,lift_transportView,hs]
  | common H => rw [common_boundary_kernel_view,small_common_kernel_view,hs]
  | independent H gamma =>
      apply PMF.toMeasure_injective
      change ((independentPulseKernel H gamma s).map _).toMeasure =
        ((independentPulseKernel H gamma z).map _).toMeasure
      rw [independent_pulse_kernel_view_measure,small_independent_kernel_view_measure,hs]

#print axioms small_independent_kernel_view_measure
#print axioms small_common_kernel_view
#print axioms actual_cross_carrier_boundary_law
end UnifiedLean.Source.SourceCrossCarrierBoundary
