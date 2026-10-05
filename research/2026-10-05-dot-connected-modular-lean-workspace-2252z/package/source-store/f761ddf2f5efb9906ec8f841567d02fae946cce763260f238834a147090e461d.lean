import UnifiedLean.Source.SourceFiniteProjection

/-!
# Actual source generator/projection instance through matrix exponentials

Contributor: dot, 2026-10-02. The source matrices are built from the normalized
ORIGINAL source PMF, its copy/rate-derived uniformization constant and the
proved finite selected-view projection. Generator intertwining is derived,
then the prior rectangular exponential adapter is instantiated. This is exact
finite-time ALGEBRA; identifying these exponentials as the full calendar-driven
biological law and timed observer requires stochastic/source temporal binding.
-/
namespace UnifiedLean.Source.SourceGeneratorExponential
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.MatrixProjectionExponential
open Matrix NormedSpace
open scoped Classical Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def sourceGeneratorMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Matrix (Code N sample) (Code N sample) ℝ :=
  globalRateBound (Copy := Copy) r • (sourceTransition N (sample := sample) r - 1)

noncomputable def selectedGeneratorMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Matrix (SelectedIndex N sample keep) (SelectedIndex N sample keep) ℝ :=
  globalRateBound (Copy := Copy) r • (selectedTransition N (sample := sample) r keep - 1)

/-- The required source instance is proved from its actual transition law;
there is no generator/projection equation field in the source input. -/
theorem actual_source_generator_matrix_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) :
    sourceGeneratorMatrix N (sample := sample) r * projectionMatrix N (sample := sample) keep =
      projectionMatrix N (sample := sample) keep * selectedGeneratorMatrix N (sample := sample) r keep := by
  unfold sourceGeneratorMatrix selectedGeneratorMatrix
  rw [Matrix.smul_mul,Matrix.mul_smul]
  congr 1
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
    actual_source_transition_intertwining N r keep]

/-- Actual-source rectangular finite-time algebra, not an assumed source
semigroup identity. Nonnegative durations/stochasticity and calendar epochs
are further explicit source gates; the algebra itself holds for every realt. -/
theorem actual_source_exponential_projection (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ) :
    exp (t • sourceGeneratorMatrix N (sample := sample) r) * projectionMatrix N (sample := sample) keep =
      projectionMatrix N (sample := sample) keep * exp (t • selectedGeneratorMatrix N (sample := sample) r keep) :=
  rectangular_scaled_exp_intertwining _ _ _
    (actual_source_generator_matrix_intertwining N r keep) t

#print axioms actual_source_generator_matrix_intertwining
#print axioms actual_source_exponential_projection
end UnifiedLean.Source.SourceGeneratorExponential
