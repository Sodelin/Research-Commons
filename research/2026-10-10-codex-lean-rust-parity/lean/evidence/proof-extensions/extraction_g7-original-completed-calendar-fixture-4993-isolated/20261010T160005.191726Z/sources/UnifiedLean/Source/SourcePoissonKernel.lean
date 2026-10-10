import UnifiedLean.Source.SourceFiniteProjection
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Constructed source finite-time Poisson-mixture kernel and selected transport

Contributor: dot, 2026-10-02. Iterates the actual normalized original-source
step and mixes with the library Poisson count at the derived positive global
rate. The resulting PMF is a genuine finite-time kernel construction, and its
selected internal-state transport is proved from the actual one-step law.
Identification with source exponential holding times, semigroup/clock-rate
independence, calendar-compatible initialization/agenda, timed-path observation
and the unranked quotient remain explicit gates before full original-law claims.
-/
namespace UnifiedLean.Source.SourcePoissonKernel
open Nanuq.Source ProbabilityTheory
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def sourceIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Nat → Code N sample → PMF (Code N sample)
  | 0,s => PMF.pure s
  | k+1,s => (sourceStep N r s).bind (sourceIteration N r k)

noncomputable def selectedIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Nat → SelectedIndex N sample keep → PMF (SelectedIndex N sample keep)
  | 0,s => PMF.pure s
  | k+1,s => (selectedStep N r keep s).bind (selectedIteration N r keep k)

/-- All finite iterations of the ACTUAL source PMF preserve the same selected
whole-state law, not just one scalar or an assumed transition matrix identity. -/
theorem source_iteration_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (k : Nat) (s : Code N sample) :
    (sourceIteration N r k s).map (projection N keep) =
      selectedIteration N r keep k (projection N keep s) := by
  induction k generalizing s with
  | zero => simp [sourceIteration,selectedIteration,PMF.pure_map]
  | succ k ih =>
      rw [sourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (sourceStep N r s).bind (selectedIteration N r keep k ∘ projection N keep) = _
      rw [← PMF.bind_map]
      change (projectedStep N r keep s).bind (selectedIteration N r keep k) = _
      rw [source_step_projection_law]
      rfl

noncomputable def globalClockRate (r : PositivePairRates E) : ℝ≥0 :=
  ⟨globalRateBound (Copy := Copy) r,(globalRateBound_positive (Copy := Copy) r).le⟩

noncomputable def countPMF (rate : ℝ≥0) : PMF Nat := (poissonMeasure rate).toPMF

noncomputable def sourceTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) : PMF (Code N sample) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind
    (fun k => sourceIteration N r k s)

noncomputable def selectedTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0)
    (s : SelectedIndex N sample keep) : PMF (SelectedIndex N sample keep) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind
    (fun k => selectedIteration N r keep k s)

/-- Genuine normalized Poisson/source-step mixture, with exact selected-state
law. No phenotype readout, time-compatible source epoch or observed-law equality
is supplied as a premise hidden in this construction. -/
theorem constructed_source_time_kernel_projection (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (projection N keep) =
      selectedTimeKernel N r keep t (projection N keep s) := by
  rw [sourceTimeKernel,selectedTimeKernel,PMF.map_bind]
  simp_rw [source_iteration_projection]

#print axioms source_iteration_projection
#print axioms constructed_source_time_kernel_projection
end UnifiedLean.Source.SourcePoissonKernel
