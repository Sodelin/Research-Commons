import NativeSparseTableCertificate
import G7EffectiveAncestralCompletion
import G7SparseWordComposition

/-! Direct exact table certificate for the EXISTING genuine ancestral limit.
Nonempty Copy and actual full root support are retained. Constant extraction is
justified by the inherited limit theorem, not an arbitrary zero-time/zero-slot
substitution. Native input/row encoding is checked separately by each caller. -/
namespace Astra.OriginalCompletionTableCertificate
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.EffectiveAncestralCompletion
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveCoefficientSupport
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourcePoissonExponential
open GProgram.G7.AncestralRationalCompletion
open GProgram.G7.SparseWordComposition
open scoped BigOperators
open Astra.NativeSparseTableCertificate

variable {I V E X Copy : Type*}
variable [DecidableEq I] [Fintype I]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [FinEnum V] [FinEnum E] [FinEnum Copy] [Nonempty Copy]

def checkCompletion (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (supplied : Rows I (Code N sample)) : Bool :=
  checkRows (project N Finset.univ) (completionRows N s) supplied

theorem checked_original_completion (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (supplied : Rows I (Code N sample))
    (h : checkCompletion N s supplied = true) (hs : AncestralRoot N s)
    (b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) (x : I → ℝ) :
    value (readRows (project N Finset.univ) supplied b) x =
      (((completionKernel N r s).map (projection N Finset.univ)) b).toReal := by
  have heq := checkRows_sound (project N Finset.univ) (completionRows N s) supplied h b
  have evaluated := congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ) x) heq
  rw [eval_polynomial, eval_polynomial] at evaluated
  exact evaluated.symm.trans (completionRows_actual N s hs b r x)

/-- Complete finite-row fibre pushforward. It visits supplied rows only;
the proof uses the inherited exact partition identity. -/
noncomputable def observedValue {Obs : Type*} [DecidableEq Obs]
    (N : RootedBinary V E X) {sample : Copy → X}
    (supplied : Rows I (Code N sample))
    (observe : SelectedIndex N sample Finset.univ → Obs) (event : Obs) (x : I → ℝ) : ℝ :=
  (supplied.map fun row =>
    value row.2 x * (if observe (project N Finset.univ row.1) = event then 1 else 0)).sum

/-- The authorized observer acts on the SAME complete selected fibres.
No arbitrary desired observer-law equality is a premise. -/
theorem checked_completion_observer {Obs : Type*} [DecidableEq Obs]
    (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (supplied : Rows I (Code N sample))
    (h : checkCompletion N s supplied = true) (hs : AncestralRoot N s)
    (observe : SelectedIndex N sample Finset.univ → Obs) (event : Obs)
    (r : PositivePairRates E) (x : I → ℝ) :
    observedValue N supplied observe event x =
      ((((completionKernel N r s).map (projection N Finset.univ)).map observe) event).toReal := by
  classical
  rw [observedValue,
    sum_partition supplied (fun row => project N Finset.univ row.1)
      (fun row => value row.2 x) (fun b => if observe b = event then 1 else 0),
    map_probability_real]
  apply Finset.sum_congr rfl
  intro b _
  rw [← value_readRows, checked_original_completion N s supplied h hs b r x]
  all_goals by_cases he : observe b = event <;> simp [he, eq_comm]

end Astra.OriginalCompletionTableCertificate
