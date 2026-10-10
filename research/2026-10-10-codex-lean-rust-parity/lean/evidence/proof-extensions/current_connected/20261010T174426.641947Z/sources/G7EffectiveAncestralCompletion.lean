import G7FullEpochSupport
import G7SelectedCompletionPolynomial

/-!
# Support-only rational rows for actual infinite ancestral completion

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The actual population and ancestral recurrence bodies are the same inherited
ordered-half-rate formulas under separate namespaces. Their name bridge binds
the executable coefficient list's exponent-zero sum to ancestralPolynomial.
The unchanged actual_completion_rational then supplies the genuine limit law.
No chosen epoch-table uniqueness or finite-time evaluation outside its domain
is assumed. All semantic completion theorems retain nonempty Copy and actual
all-copy ancestral support. Draft pending sole-scheduler kernel/audit checking.
-/
namespace GProgram.G7.EffectiveAncestralCompletion
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.G6.AncestralRateFree
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveCoefficientSupport GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.SparseRowProducts GProgram.G7.AncestralRationalCompletion
open GProgram.G7.SelectedCompletionPolynomial
open scoped BigOperators

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- Names differ, but the unchanged source recurrences have identical bodies.
This equality needs no co-location hypothesis: it compares formal expressions. -/
lemma kernelExpr_eq_ancestral (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : Nat) (s d : Code N sample) :
    kernelExpr N fuel s d = GProgram.G7.AncestralPolynomialKernel.kernelExpr N fuel s d := by
  classical
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      by_cases h : liveCard s ≤ 1
      · simp only [kernelExpr,GProgram.G7.AncestralPolynomialKernel.kernelExpr,if_pos h]
      · rw [kernelExpr,GProgram.G7.AncestralPolynomialKernel.kernelExpr,if_neg h,if_neg h]
        congr 1
        apply congrArg (fun f : Choice N s → Expr =>
          (Finset.univ.toList : List (Choice N s)).flatMap f)
        funext p
        rw [ih]
        rfl

lemma populationPolynomial_eq_ancestral (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) :
    populationPolynomial N s d = GProgram.G7.AncestralPolynomialKernel.ancestralPolynomial N s d := by
  rw [populationPolynomial,GProgram.G7.AncestralPolynomialKernel.ancestralPolynomial,
    kernelExpr_eq_ancestral]
  rfl

def constantExpr (p : Expr) : ℚ :=
  (p.map fun z => if z.1=0 then z.2 else 0).sum

lemma constantExpr_eq_coeff (p : Expr) : constantExpr p = (exprPolynomial p).coeff 0 := by
  induction p with
  | nil => simp [constantExpr,exprPolynomial]
  | cons z p ih =>
      rw [exprPolynomial_cons,Polynomial.coeff_add,Polynomial.C_mul_X_pow_eq_monomial]
      change (if z.1=0 then z.2 else 0) + constantExpr p = _
      rw [ih]
      by_cases h : z.1=0 <;> simp [Polynomial.coeff_monomial,h,eq_comm]

/-- Direct exact rational coefficient identity, independent of physical rates. -/
lemma constantCoefficients (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) :
    constantExpr (coefficients N (Fintype.card Copy) s d) =
      (GProgram.G7.AncestralPolynomialKernel.ancestralPolynomial N s d).coeff 0 := by
  rw [constantExpr_eq_coeff,coefficients_polynomial,populationPolynomial_eq_ancestral]

def rationalRows (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : List (Code N sample × ℚ) :=
  (destinations N (Fintype.card Copy) s).dedup.map fun d =>
    (d,constantExpr (coefficients N (Fintype.card Copy) s d))

def readRational {A K : Type*} [DecidableEq K] (key : A → K)
    (rows : List (A × ℚ)) (target : K) : ℚ :=
  (rows.map fun row => if key row.1=target then row.2 else 0).sum

/-- Every omitted actual Code term is zero by the accepted arbitrary-fuel
support theorem. No complete Code carrier occurs in the executable body. -/
lemma readRational_full (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ) :
    readRational (project N Finset.univ) (rationalRows N s) a =
      ∑ d : Code N sample, if project N Finset.univ d=a then
        constantExpr (coefficients N (Fintype.card Copy) s d) else 0 := by
  classical
  rw [readRational,rationalRows,List.map_map]
  change ((destinations N (Fintype.card Copy) s).dedup.map fun d =>
      if project N Finset.univ d=a then
        constantExpr (coefficients N (Fintype.card Copy) s d) else 0).sum = _
  rw [← List.sum_toFinset
    (fun d : Code N sample => if project N Finset.univ d=a then
      constantExpr (coefficients N (Fintype.card Copy) s d) else 0)
    (List.nodup_dedup (destinations N (Fintype.card Copy) s))]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  have hnot : d ∉ destinations N (Fintype.card Copy) s := by
    simpa only [List.mem_toFinset,List.mem_dedup] using hd
  by_cases h : project N Finset.univ d=a
  · rw [if_pos h,constantExpr_eq_coeff,
      coefficients_polynomial_zero_of_not_mem N _ s d hnot]
    simp
  · rw [if_neg h]

theorem readRational_ancestral (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ) :
    readRational (project N Finset.univ) (rationalRows N s) a =
      ∑ d : Code N sample,
        (GProgram.G7.AncestralPolynomialKernel.ancestralPolynomial N s d).coeff 0 *
          (if projection N Finset.univ d=a then 1 else 0) := by
  classical
  rw [readRational_full]
  apply Finset.sum_congr rfl
  intro d _
  rw [constantCoefficients,project_eq]
  by_cases h : projection N Finset.univ d=a <;> simp [h]

def completionRows {I : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Rows I (Code N sample) :=
  (rationalRows N s).map fun row => (row.1,single row.2)

/-- Infinite completion adds no survival variable to the shared word bank. -/
lemma polynomial_completionRows {I : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (completionRows (I := I) N s) a) =
      MvPolynomial.C (readRational (project N Finset.univ) (rationalRows N s) a) := by
  rw [polynomial_readRows,completionRows,List.map_map,readRational,map_list_sum]
  apply congrArg List.sum
  simp only [List.map_map]
  apply List.map_congr_left
  intro row _
  by_cases h : project N Finset.univ row.1=a <;> simp [single,polynomial,h]

variable [Nonempty Copy]

/-- The inherited actual infinite-time limit justifies the zero coefficient.
Nonempty Copy and actual full ancestral-root support are explicit premises. -/
theorem rationalRows_actual (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s)
    (a : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) :
    (readRational (project N Finset.univ) (rationalRows N s) a : ℝ) =
      (((completionKernel N r s).map (projection N Finset.univ)) a).toReal := by
  classical
  rw [readRational_ancestral,Rat.cast_sum,map_probability_real]
  apply Finset.sum_congr rfl
  intro d _
  rw [Rat.cast_mul,actual_completion_rational N s d hs r]
  by_cases h : projection N Finset.univ d=a <;> simp [h]

/-- Exact equality to the unchanged selected rational completion carrier,
using its already proved source projection and root-support theorem. -/
theorem readRational_eq_completionRational (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s)
    (a : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) :
    readRational (project N Finset.univ) (rationalRows N s) a =
      completionRational N (project N Finset.univ s) a := by
  apply (Rat.cast_injective : Function.Injective ((↑) : ℚ → ℝ))
  rw [rationalRows_actual N s hs a r,actual_source_completion_projection N r s hs,project_eq]
  exact (actual_selected_completion_rational N (projection N Finset.univ s) a
    (actual_root_projection N s hs) r).symm

theorem completionRows_actual {I : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s)
    (a : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) (x : I → ℝ) :
    value (readRows (project N Finset.univ) (completionRows (I := I) N s) a) x =
      (((completionKernel N r s).map (projection N Finset.univ)) a).toReal := by
  rw [← eval_polynomial,polynomial_completionRows,MvPolynomial.eval₂_C]
  exact rationalRows_actual N s hs a r

#print axioms kernelExpr_eq_ancestral
#print axioms constantCoefficients
#print axioms readRational_ancestral
#print axioms rationalRows_actual
#print axioms readRational_eq_completionRational
#print axioms completionRows_actual
end GProgram.G7.EffectiveAncestralCompletion
