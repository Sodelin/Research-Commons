import G7AncestralPolynomialKernel
import UnifiedLean.Source.SourceEventualCompletionLimit
import Mathlib.Topology.Algebra.Polynomial

/-! The zero-survival extension is justified by the inherited actual-source
completion limit, not by evaluating a finite-time theorem outside its domain. -/
namespace GProgram.G7.AncestralRationalCompletion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Filter
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceEventualCompletionLimit UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G7.AncestralPolynomialKernel
open scoped Classical NNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]

theorem actual_completion_at_zero (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (hs : AncestralRoot N s) (r : PositivePairRates E) :
    Polynomial.eval₂ (Rat.castHom ℝ) 0 (ancestralPolynomial N s d) =
      (completionKernel N r s d).toReal := by
  have ht : Tendsto (fun t : ℝ≥0 => -r.ancestral*(t:ℝ)) atTop atBot := by
    exact (NNReal.tendsto_coe_atTop.mpr tendsto_id).const_mul_atTop_of_neg
      (neg_neg_of_pos r.ancestral_pos)
  have hp := ((ancestralPolynomial N s d).continuous_eval₂ (Rat.castHom ℝ)).tendsto 0
  have hl := hp.comp (Real.tendsto_exp_atBot.comp ht)
  have ha := actual_ancestral_kernel_tendsto_completion N r s d hs
  simp only [Function.comp_def] at hl
  simp_rw [actual_ancestral_polynomial N s d hs r] at hl
  exact tendsto_nhds_unique hl ha

/-- Actual infinite ancestral completion has rational rows independent of the
positive physical bank, with the complete retained endpoint Code preserved. -/
theorem actual_completion_rational (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (hs : AncestralRoot N s) (r : PositivePairRates E) :
    (((ancestralPolynomial N s d).coeff 0 : ℚ) : ℝ) =
      (completionKernel N r s d).toReal := by
  simpa using actual_completion_at_zero N s d hs r

end GProgram.G7.AncestralRationalCompletion
