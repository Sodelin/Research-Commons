import NativeSparseTableCertificate
import G7FullEpochSupport

/-! Supplied complete native sparse rows are compared against the EXISTING
constructive fullRows, not a new transition oracle or all-state enumerator.
Positive rates/duration and original input validity retain their source types.
Actual native row encoding and each literal Boolean check remain caller work. -/
namespace Astra.OriginalEpochTableCertificate
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceFiniteProjection
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.FullEpochSupport GProgram.G7.FullEpochPolynomial
open Astra.NativeSparseTableCertificate
open scoped NNReal

variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def check (N : RootedBinary V E X) {sample : Copy → X}
    (todo : List (Option E)) (s : Code N sample)
    (supplied : Rows (Option E) (Code N sample)) : Bool :=
  checkRows (project N Finset.univ) (fullRows N todo Copy sample s) supplied

/-- All selected endpoint fibres, including zero on absence, share the SAME
original source and positive rate bank. The Boolean check compares exact
rational coefficients before any physical evaluation; no desired-law premise. -/
theorem checked_original_epoch (N : RootedBinary V E X) {sample : Copy → X}
    (todo : List (Option E)) (s : Code N sample)
    (supplied : Rows (Option E) (Code N sample))
    (h : check N todo s supplied = true)
    (hs : ActiveIn N s todo.toFinset)
    (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates E) (t : ℝ≥0) :
    value (readRows (project N Finset.univ) supplied b) (survival r t) =
      (((sourceTimeKernel N r t s).map (projection N Finset.univ)) b).toReal := by
  have heq := checkRows_sound (project N Finset.univ)
    (fullRows N todo Copy sample s) supplied h b
  have evaluated := congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ) (survival r t)) heq
  rw [eval_polynomial, eval_polynomial] at evaluated
  exact evaluated.symm.trans (fullRows_actual N todo s hs b r t)

end Astra.OriginalEpochTableCertificate
