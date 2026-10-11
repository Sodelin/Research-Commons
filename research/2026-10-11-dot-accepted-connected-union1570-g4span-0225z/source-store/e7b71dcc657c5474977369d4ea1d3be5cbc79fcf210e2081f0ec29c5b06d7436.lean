import G6OriginalPopulationExposure
import G6OriginalPopulationSpectralSupport
import ActualPolynomialEpochModulus
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Ring.GeomSum

/-!
# Original population generator and coarse full-row remainder

Contributor: Codex / lean_integration_successor, 2026-10-10.
Consumer of the unchanged original rational kernelExpr recursion. Fuel is the
entering live-lineage cap, not the number of carried copies. Ordered original
choices retain their factor 1/2 and the survival-coordinate generator is -P'(1).
The complete row L1 remainder uses the accepted raw-expression mass bound;
there is no Code-carrier multiplier. The constant is the larger coarse cap
constant, not Appendix A's count-conditioned constant. No source construction,
positive generator compression, native refinement, or full G6 is asserted.
Draft pending its own exact kernel checking and complete owned audit.
-/

namespace GProgram.G6.OriginalPopulationGeneratorBounds

open Nanuq.Source
open GProgram.G7.SinglePopulationPolynomialKernel
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteJumpExpansion UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.G6.AncestralRateFree UnifiedLean.G6.ActualKernelCoefficientBound
open GProgram.G6.OriginalPopulationSpectralSupport
open scoped Classical BigOperators NNReal

noncomputable def exprEval (p : Expr) (x : ℝ) : ℝ :=
  Polynomial.eval₂ (Rat.castHom ℝ) x (exprPolynomial p)

noncomputable def exprDerivativeAtOne (p : Expr) : ℝ :=
  Polynomial.eval₂ (Rat.castHom ℝ) 1 (Polynomial.derivative (exprPolynomial p))

noncomputable def centeredQuotient (p : Expr) (x : ℝ) : ℝ :=
  (exprEval p x - exprEval p 1) / (1-x)

@[simp] lemma exprEval_nil (x : ℝ) : exprEval [] x = 0 := by simp [exprEval]
@[simp] lemma exprEval_cons (a : ℕ × ℚ) (p : Expr) (x : ℝ) :
    exprEval (a::p) x = (a.2:ℝ)*x^a.1 + exprEval p x := by
  simp [exprEval,exprPolynomial_cons]
lemma exprEval_append (p q : Expr) (x : ℝ) :
    exprEval (p++q) x = exprEval p x + exprEval q x := by
  simp [exprEval,exprPolynomial,List.map_append,List.sum_append]
lemma exprEval_flatMap {A : Type*} (xs : List A) (f : A → Expr) (x : ℝ) :
    exprEval (xs.flatMap f) x = (xs.map fun a => exprEval (f a) x).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.flatMap_cons,exprEval_append,ih]

@[simp] lemma exprDerivativeAtOne_nil : exprDerivativeAtOne [] = 0 := by
  simp [exprDerivativeAtOne]
@[simp] lemma exprDerivativeAtOne_cons (a : ℕ × ℚ) (p : Expr) :
    exprDerivativeAtOne (a::p) = (a.2:ℝ)*(a.1:ℝ) + exprDerivativeAtOne p := by
  simp [exprDerivativeAtOne,exprPolynomial_cons,Polynomial.derivative_add,
    Polynomial.C_mul_X_pow_eq_monomial,Polynomial.derivative_monomial]
lemma exprDerivativeAtOne_append (p q : Expr) :
    exprDerivativeAtOne (p++q) = exprDerivativeAtOne p + exprDerivativeAtOne q := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih,add_assoc]
lemma exprDerivativeAtOne_flatMap {A : Type*} (xs : List A) (f : A → Expr) :
    exprDerivativeAtOne (xs.flatMap f) =
      (xs.map fun a => exprDerivativeAtOne (f a)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.flatMap_cons,exprDerivativeAtOne_append,ih]

lemma liftTerm_eval_one (n : ℕ) (a : ℕ × ℚ) : exprEval (liftTerm n a) 1 = 0 := by
  simp [liftTerm]
lemma liftExpr_eval_one (n : ℕ) (p : Expr) : exprEval (liftExpr n p) 1 = 0 := by
  induction p with
  | nil => simp [liftExpr]
  | cons a p ih =>
    change exprEval (liftTerm n a ++ liftExpr n p) 1 = 0
    rw [exprEval_append,liftTerm_eval_one,ih]
    simp

lemma liftTerm_derivative_at_one (n : ℕ) (a : ℕ × ℚ) (ha : a.1 < n) :
    exprDerivativeAtOne (liftTerm n a) = -(a.2:ℝ)/2 := by
  have hn : (n:ℝ)-(a.1:ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt (by exact_mod_cast ha))
  simp only [liftTerm,exprDerivativeAtOne_cons,exprDerivativeAtOne_nil,add_zero]
  push_cast
  field_simp [hn]
  ring

lemma liftExpr_derivative_at_one (n : ℕ) (p : Expr)
    (hp : ∀ a ∈ p, a.1 < n) :
    exprDerivativeAtOne (liftExpr n p) = -exprEval p 1/2 := by
  induction p with
  | nil => simp [liftExpr]
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht := ih (fun b hb => hp b (by simp [hb]))
    change exprDerivativeAtOne (liftTerm n a ++ liftExpr n p) = -exprEval (a::p) 1/2
    rw [exprDerivativeAtOne_append,liftTerm_derivative_at_one n a ha,ht,exprEval_cons]
    simp only [one_pow]
    ring

noncomputable def geometricSum (n : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Finset.range n, x^j
noncomputable def triangleCoefficient (n : ℕ) : ℝ := (n:ℝ)*((n:ℝ)-1)/2

lemma geometricSum_remainder (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (n:ℝ)-geometricSum n x ∧
      (n:ℝ)-geometricSum n x ≤ triangleCoefficient n*(1-x) := by
  induction n with
  | zero => simp [geometricSum,triangleCoefficient]
  | succ n ih =>
    have hp : x^n ≤ 1 := pow_le_one₀ hx0 hx1
    have hl : 1-x^n ≤ (n:ℝ)*(1-x) := by
      have h := unit_power_lipschitz x 1 hx0 hx1 (by norm_num) le_rfl n
      rw [one_pow,abs_of_nonpos (sub_nonpos.mpr hp),
        abs_of_nonpos (sub_nonpos.mpr hx1)] at h
      linarith
    have he : ((n+1:ℕ):ℝ)-geometricSum (n+1) x =
        ((n:ℝ)-geometricSum n x) + (1-x^n) := by
      simp only [geometricSum,Finset.sum_range_succ,Nat.cast_add,Nat.cast_one]
      ring
    rw [he]
    refine ⟨add_nonneg ih.1 (sub_nonneg.mpr hp),?_⟩
    calc
      _ ≤ triangleCoefficient n*(1-x) + (n:ℝ)*(1-x) := add_le_add ih.2 hl
      _ = triangleCoefficient (n+1)*(1-x) := by
        simp only [triangleCoefficient,Nat.cast_add,Nat.cast_one]
        ring

lemma triangleCoefficient_mono {n D : ℕ} (h : n ≤ D) :
    triangleCoefficient n ≤ triangleCoefficient D := by
  by_cases hn : n = 0
  · subst n
    by_cases hD : D = 0
    · simp [hD]
    · have h1 : (1:ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
      have hp := mul_nonneg (Nat.cast_nonneg D : (0:ℝ) ≤ D) (by linarith : (0:ℝ) ≤ D-1)
      simp only [triangleCoefficient,Nat.cast_zero,zero_mul,zero_div]
      exact div_nonneg hp (by norm_num)
  · have h1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hR : (n:ℝ) ≤ D := by exact_mod_cast h
    unfold triangleCoefficient
    exact div_le_div_of_nonneg_right
      (mul_le_mul hR (sub_le_sub_right hR 1) (by linarith) (Nat.cast_nonneg D))
      (by norm_num)

lemma triangleCoefficient_nonneg (D : ℕ) : 0 ≤ triangleCoefficient D := by
  simpa [triangleCoefficient] using (triangleCoefficient_mono (Nat.zero_le D))

lemma geometric_secant (n : ℕ) (x : ℝ) (hx : x < 1) :
    (x^n-1)/(1-x) = -geometricSum n x := by
  apply (div_eq_iff (ne_of_gt (sub_pos.mpr hx))).mpr
  have h := geom_sum_mul_neg x n
  change geometricSum n x * (1-x) = 1-x^n at h
  nlinarith

lemma expression_remainder_cons (a : ℕ × ℚ) (p : Expr) (x : ℝ) (hx : x < 1) :
    centeredQuotient (a::p) x + exprDerivativeAtOne (a::p) =
      (a.2:ℝ)*((a.1:ℝ)-geometricSum a.1 x) +
        (centeredQuotient p x + exprDerivativeAtOne p) := by
  have h := geometric_secant a.1 x hx
  simp only [centeredQuotient,exprEval_cons,exprDerivativeAtOne_cons,one_pow]
  calc
    _ = (a.2:ℝ)*((x^a.1-1)/(1-x)) +
        (exprEval p x-exprEval p 1)/(1-x) +
        ((a.2:ℝ)*(a.1:ℝ)+exprDerivativeAtOne p) := by ring
    _ = _ := by rw [h]; ring

/-- The triangle inequality is applied to raw syntax terms before collecting
duplicate monomials. Its mass is the existing accepted expression mass. -/
theorem expression_generator_remainder (p : Expr) (D : ℕ)
    (hD : ∀ a ∈ p, a.1 ≤ D) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |centeredQuotient p x + exprDerivativeAtOne p| ≤
      triangleCoefficient D * (exprMass p:ℝ) * (1-x) := by
  induction p with
  | nil => simp [centeredQuotient]
  | cons a p ih =>
    have ha := hD a (by simp)
    have ht := ih (fun b hb => hD b (by simp [hb]))
    have hg := geometricSum_remainder a.1 x hx0 hx1.le
    have hb : (a.1:ℝ)-geometricSum a.1 x ≤ triangleCoefficient D*(1-x) :=
      hg.2.trans (mul_le_mul_of_nonneg_right (triangleCoefficient_mono ha)
        (sub_nonneg.mpr hx1.le))
    have hh : |(a.2:ℝ)*((a.1:ℝ)-geometricSum a.1 x)| ≤
        |(a.2:ℝ)| *(triangleCoefficient D*(1-x)) := by
      rw [abs_mul,abs_of_nonneg hg.1]
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    rw [expression_remainder_cons a p x hx1]
    calc
      _ ≤ |(a.2:ℝ)*((a.1:ℝ)-geometricSum a.1 x)| +
          |centeredQuotient p x + exprDerivativeAtOne p| := abs_add_le _ _
      _ ≤ |(a.2:ℝ)| *(triangleCoefficient D*(1-x)) +
          triangleCoefficient D*(exprMass p:ℝ)*(1-x) := add_le_add hh ht
      _ = _ := by
        simp only [exprMass_cons,Rat.cast_add,Rat.cast_abs]
        ring

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Stronger than the capped physical theorem: cancellation of the unchanged
lift syntax gives its exact identity row at survival one at every fuel. -/
theorem kernelExpr_eval_one (N : RootedBinary V E X) {sample : Copy → X}
    (budget : ℕ) (s d : Code N sample) :
    Polynomial.eval₂ (Rat.castHom ℝ) 1 (exprPolynomial (kernelExpr N budget s d)) =
      if s=d then 1 else 0 := by
  change exprEval (kernelExpr N budget s d) 1 = _
  cases budget with
  | zero => by_cases h : s=d <;> simp [kernelExpr,h]
  | succ budget =>
    by_cases hk : liveCard s ≤ 1
    · rw [kernelExpr,if_pos hk]
      by_cases h : s=d <;> simp [h]
    · rw [kernelExpr,if_neg hk,exprEval_append,exprEval_flatMap]
      by_cases h : s=d <;> simp [h,liftExpr_eval_one]

noncomputable def cappedPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (M : ℕ) (s d : Code N sample) : Polynomial ℚ := exprPolynomial (kernelExpr N M s d)

noncomputable def populationQuotient (N : RootedBinary V E X) {sample : Copy → X}
    (M : ℕ) (s d : Code N sample) (x : ℝ) : ℝ :=
  (Polynomial.eval₂ (Rat.castHom ℝ) x (cappedPolynomial N M s d) -
    if s=d then 1 else 0)/(1-x)

noncomputable def populationGenerator (N : RootedBinary V E X) {sample : Copy → X}
    (M : ℕ) (s d : Code N sample) : ℝ :=
  -Polynomial.eval₂ (Rat.castHom ℝ) 1 (Polynomial.derivative (cappedPolynomial N M s d))

noncomputable def coarseRemainder (M : ℕ) : ℝ := ((1+M*M:ℕ):ℝ)^M * triangleCoefficient (M.choose 2)

lemma populationQuotient_eq_centered (N : RootedBinary V E X) {sample : Copy → X}
    (M : ℕ) (s d : Code N sample) (x : ℝ) :
    populationQuotient N M s d x = centeredQuotient (kernelExpr N M s d) x := by
  simp only [populationQuotient,cappedPolynomial,centeredQuotient,exprEval,kernelExpr_eval_one]

/-- Any live cap is valid fuel for the full original retained-state PMF,
even when the number of carried copies is larger than that cap. -/
theorem cappedPolynomial_actual (N : RootedBinary V E X) {sample : Copy → X}
    (M : ℕ) (s d : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (hM : liveCard s ≤ M) (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-(pairRate r i)*(t:ℝ)))
      (cappedPolynomial N M s d) = (sourceTimeKernel N r t s d).toReal := by
  rw [cappedPolynomial,exprPolynomial_eval]
  exact kernelExpr_actual N r i M s d t hs hM

theorem cappedPolynomial_level_support (N : RootedBinary V E X) {sample : Copy → X}
    (M : ℕ) (s d : Code N sample) :
    ∀ a ∈ kernelExpr N M s d, ∃ j ≤ liveCard s, a.1 = j.choose 2 :=
  original_kernelExpr_level_support N M s d

/-- Exact unit-population-rate generator. Every original ORDERED choice has
weight 1/2; the diagonal is choose(k,2), and the sign is -P'(1). -/
theorem populationGenerator_eq_ordered_choice (N : RootedBinary V E X)
    {sample : Copy → X} (M : ℕ) (s d : Code N sample) (i : Option E)
    (hs : CoLocated N s i) (hM : liveCard s ≤ M) :
    populationGenerator N M s d =
      (∑ p : Choice N s, (1/2:ℝ)*(if stepDestination N s (some p)=d then 1 else 0)) -
        ((liveCard s).choose 2:ℝ)*(if s=d then 1 else 0) := by
  change -exprDerivativeAtOne (kernelExpr N M s d) = _
  by_cases hk : liveCard s ≤ 1
  · letI := choice_empty_of_terminal_card N s hk
    have hc : (liveCard s).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    cases M with
    | zero =>
      rw [kernelExpr]
      simp [hc]
    | succ budget =>
      rw [kernelExpr,if_pos hk]
      simp [hc]
  · obtain ⟨budget,hbudget⟩ := Nat.exists_eq_succ_of_ne_zero (show M ≠ 0 by omega)
    subst M
    have hl (p : Choice N s) :
        exprDerivativeAtOne (liftExpr ((liveCard s).choose 2)
          (kernelExpr N budget (stepDestination N s (some p)) d)) =
        -(if stepDestination N s (some p)=d then (1:ℝ) else 0)/2 := by
      rw [liftExpr_derivative_at_one]
      · simp only [exprEval,kernelExpr_eval_one]
      · intro a ha
        exact (kernelExpr_bound N budget _ d a ha).trans_lt
          (merger_exponent_lt N s p (by omega))
    rw [kernelExpr,if_neg hk,exprDerivativeAtOne_append,exprDerivativeAtOne_flatMap,
      Finset.sum_map_toList]
    simp only [exprDerivativeAtOne_cons,exprDerivativeAtOne_nil,add_zero]
    simp_rw [hl]
    have hsum : (∑ p : Choice N s, -(if stepDestination N s (some p)=d then (1:ℝ) else 0)/2) =
        -(∑ p : Choice N s, (1/2:ℝ)*(if stepDestination N s (some p)=d then 1 else 0)) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hsum]
    by_cases h : s=d <;> simp [h] <;> ring

/-- Complete original-row L1 error. This is not a TV charge: any later TV
semigroup estimate must retain its separate factor 1/2. -/
theorem row_generator_remainder (N : RootedBinary V E X) {sample : Copy → X}
    (M : ℕ) (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (hM : liveCard s ≤ M) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∑ d : Code N sample, |populationQuotient N M s d x - populationGenerator N M s d|) ≤
      coarseRemainder M*(1-x) := by
  have hd (d : Code N sample) : ∀ a ∈ kernelExpr N M s d, a.1 ≤ M.choose 2 :=
    fun a ha => (kernelExpr_bound N M s d a ha).trans (Nat.choose_le_choose 2 hM)
  have hp (d : Code N sample) :
      |populationQuotient N M s d x - populationGenerator N M s d| ≤
        triangleCoefficient (M.choose 2)*(exprMass (kernelExpr N M s d):ℝ)*(1-x) := by
    rw [populationQuotient_eq_centered]
    simp only [populationGenerator,cappedPolynomial,sub_neg_eq_add]
    exact expression_generator_remainder _ _ (hd d) x hx0 hx1
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => hp d)
  have hm : (rowMass N M s:ℝ) ≤ ((1+M*M:ℕ):ℝ)^M := by
    exact_mod_cast actual_row_mass_bound N M M s i hs hM
  have he : (∑ d : Code N sample,
      triangleCoefficient (M.choose 2)*(exprMass (kernelExpr N M s d):ℝ)*(1-x)) =
      triangleCoefficient (M.choose 2)*(rowMass N M s:ℝ)*(1-x) := by
    simp [rowMass,Finset.mul_sum,Finset.sum_mul]
  rw [he] at hsum
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (triangleCoefficient_nonneg (M.choose 2)))
    (sub_nonneg.mpr hx1.le)
  exact hsum.trans (by simpa only [coarseRemainder,mul_comm,mul_left_comm,mul_assoc] using hmul)

@[simp] theorem coarseRemainder_zero : coarseRemainder 0 = 0 := by
  norm_num [coarseRemainder,triangleCoefficient]
@[simp] theorem coarseRemainder_one : coarseRemainder 1 = 0 := by
  norm_num [coarseRemainder,triangleCoefficient]

end GProgram.G6.OriginalPopulationGeneratorBounds

#print axioms GProgram.G6.OriginalPopulationGeneratorBounds.kernelExpr_eval_one
#print axioms GProgram.G6.OriginalPopulationGeneratorBounds.cappedPolynomial_actual
#print axioms GProgram.G6.OriginalPopulationGeneratorBounds.populationGenerator_eq_ordered_choice
#print axioms GProgram.G6.OriginalPopulationGeneratorBounds.row_generator_remainder
