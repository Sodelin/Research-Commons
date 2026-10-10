import UnifiedLean.G6.AncestralRateFree
import UnifiedLean.Source.SourceFiniteJumpExpansion
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual arbitrary-copy ancestral epoch as a rational polynomial in the
one physical survival coordinate. Source counting, real-merger recursion and
ordered-pair normalization are retained. Contributor: dot,2026-10-09.
This one-population gate does not establish the full G7 graph compiler. -/
namespace GProgram.G7.AncestralPolynomialKernel
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceEpochRenewal UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.AncestralRateFree
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma ancestral_roots (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) :
    populationRoots (state s) (.rootPopulation N.root) = (state s).live := by
  apply Finset.filter_eq_self.mpr
  intro a ha
  exact ancestral_live_location N s hs ha

noncomputable def rootChoices (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) :
    Choice N s ≃ {p : Copy × Copy // p ∈ (state s).live.offDiag} where
  toFun p := ⟨p.2.val,by
    rcases Finset.mem_offDiag.mp p.2.property with ⟨ha,hb,hab⟩
    exact Finset.mem_offDiag.mpr ⟨populationRoots_subset_live _ _ ha,
      populationRoots_subset_live _ _ hb,hab⟩⟩
  invFun p := ⟨none,⟨p.val,by simpa [originalPlace,ancestral_roots N s hs] using p.property⟩⟩
  left_inv p := by
    rcases p with ⟨i,p⟩
    have hi : i = none := ancestral_choice_population N s hs ⟨i,p⟩
    subst i
    rfl
  right_inv p := rfl

lemma ancestral_choice_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) :
    Fintype.card (Choice N s) = liveCard s * (liveCard s - 1) := by
  rw [Fintype.card_congr (rootChoices N s hs),Fintype.card_coe,Finset.offDiag_card]
  simp only [liveCard,Nat.mul_sub_one]
  rfl

lemma actual_ancestral_holding_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    totalRate N r s = r.ancestral * ((liveCard s).choose 2 : ℝ) := by
  rw [ancestral_total_rate N r s hs,ancestral_choice_card N s hs]
  have hn : liveCard s * (liveCard s-1) = 2 * (liveCard s).choose 2 := by
    rw [Nat.choose_two_right]
    exact (Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (liveCard s))).symm
  have hr : ((liveCard s * (liveCard s-1) : ℕ) : ℝ) =
      2 * ((liveCard s).choose 2 : ℝ) := by exact_mod_cast hn
  rw [hr]
  change _ * (r.ancestral/2) = _
  ring

lemma actual_terminal_epoch (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t : ℝ≥0)
    (hk : liveCard s ≤ 1) :
    (sourceTimeKernel N r t s d).toReal = if s = d then 1 else 0 := by
  letI := choice_empty_of_terminal_card N s hk
  rw [actual_source_kernel_first_jump]
  simp [totalRate]

/-- Exact ordered-pair convolution. The half rate is retained. This formula
is valid even at zero duration; it uses no limiting or numerical comparison. -/
lemma damped_monomial_integral (n m rho a t : ℝ) (hnm : n ≠ m) :
    (∫ u in (0:ℝ)..t, Real.exp (-n*rho*u) * (rho/2) * a *
      Real.exp (-m*rho*(t-u))) =
      a / (2*(n-m)) * (Real.exp (-m*rho*t)-Real.exp (-n*rho*t)) := by
  have hd : n-m ≠ 0 := sub_ne_zero.mpr hnm
  let F := fun u : ℝ => a/(2*(n-m)) *
    (Real.exp (-m*rho*t)-Real.exp (-m*rho*t+(m-n)*rho*u))
  have hD (u : ℝ) : HasDerivAt F
      (Real.exp (-n*rho*u) * (rho/2) * a * Real.exp (-m*rho*(t-u))) u := by
    have he := ((((hasDerivAt_id u).const_mul ((m-n)*rho)).const_add (-m*rho*t)).exp)
    have hh := ((hasDerivAt_const u (Real.exp (-m*rho*t))).sub he).const_mul
      (a/(2*(n-m)))
    apply hh.congr_deriv
    have hx : Real.exp (-n*rho*u) * Real.exp (-m*rho*(t-u)) =
        Real.exp (-m*rho*t+(m-n)*rho*u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [id_eq,mul_one]
    rw [← hx]
    field_simp [hd]
    <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hD u) (show IntervalIntegrable
      (fun u : ℝ => Real.exp (-n*rho*u)*(rho/2)*a*Real.exp (-m*rho*(t-u)))
      MeasureTheory.volume 0 t from (by fun_prop : Continuous _).intervalIntegrable _ _)
  rw [hi]
  dsimp [F]
  have hx : -m*rho*t+(m-n)*rho*t = -n*rho*t := by ring
  rw [hx]
  simp

/-- Rational exponential-polynomial syntax, converted to a genuine polynomial
by replacing exp(-m*rho*t) with X^m. Ordered-pair half rates are included in
liftTerm rather than silently switching to unordered paths. -/
abbrev Expr := List (ℕ × ℚ)

def liftTerm (n : ℕ) (z : ℕ × ℚ) : Expr :=
  let b := z.2 / (2 * ((n : ℚ) - (z.1 : ℚ)))
  [(z.1,b),(n,-b)]

def liftExpr (n : ℕ) (p : Expr) : Expr := p.flatMap (liftTerm n)

noncomputable def kernelExpr (N : RootedBinary V E X) {sample : Copy → X} :
    ℕ → Code N sample → Code N sample → Expr
  | 0,s,d => [(0,if s=d then 1 else 0)]
  | budget+1,s,d =>
      if liveCard s ≤ 1 then [(0,if s=d then 1 else 0)]
      else [((liveCard s).choose 2,if s=d then 1 else 0)] ++
        (Finset.univ.toList : List (Choice N s)).flatMap (fun p =>
          liftExpr ((liveCard s).choose 2)
            (kernelExpr N budget (stepDestination N s (some p)) d))

noncomputable def exprPolynomial (p : Expr) : Polynomial ℚ :=
  (p.map (fun z => Polynomial.C z.2 * Polynomial.X ^ z.1)).sum

noncomputable def exprValue (p : Expr) (rho t : ℝ) : ℝ :=
  (p.map (fun z => (z.2 : ℝ) * Real.exp (-(z.1 : ℝ)*rho*t))).sum

@[simp] lemma exprValue_nil (rho t : ℝ) : exprValue [] rho t = 0 := rfl

@[simp] lemma exprValue_cons (z : ℕ × ℚ) (p : Expr) (rho t : ℝ) :
    exprValue (z::p) rho t = (z.2 : ℝ)*Real.exp (-(z.1 : ℝ)*rho*t) + exprValue p rho t := rfl

@[simp] lemma exprValue_append (p q : Expr) (rho t : ℝ) :
    exprValue (p++q) rho t = exprValue p rho t + exprValue q rho t := by
  simp [exprValue,List.sum_append]

lemma exprValue_continuous (p : Expr) (rho : ℝ) : Continuous (fun t => exprValue p rho t) := by
  induction p with
  | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
  | cons z p ih =>
      simp only [exprValue_cons]
      exact ((Real.continuous_exp.comp (by fun_prop)).const_mul _).add ih

lemma exprValue_liftTerm (n : ℕ) (z : ℕ × ℚ) (rho t : ℝ) :
    exprValue (liftTerm n z) rho t =
      (z.2 : ℝ)/(2*((n:ℝ)-(z.1:ℝ))) *
        (Real.exp (-(z.1:ℝ)*rho*t)-Real.exp (-(n:ℝ)*rho*t)) := by
  simp [liftTerm,exprValue,Rat.cast_div,Rat.cast_mul,Rat.cast_sub]
  ring

lemma integral_exprValue (n : ℕ) (p : Expr) (rho t : ℝ)
    (hb : ∀ z ∈ p, z.1 < n) :
    (∫ u in (0:ℝ)..t, Real.exp (-(n:ℝ)*rho*u)*(rho/2)*exprValue p rho (t-u)) =
      exprValue (liftExpr n p) rho t := by
  induction p with
  | nil => simp [liftExpr]
  | cons z p ih =>
      have hz : z.1 < n := hb z (by simp)
      have hp : ∀ w ∈ p, w.1 < n := fun w hw => hb w (by simp [hw])
      have hn : (n:ℝ) ≠ (z.1:ℝ) := by exact_mod_cast (Nat.ne_of_gt hz)
      have hc : Continuous (fun u : ℝ => exprValue p rho (t-u)) :=
        (exprValue_continuous p rho).comp (continuous_const.sub continuous_id)
      have hf : IntervalIntegrable
          (fun u : ℝ => Real.exp (-(n:ℝ)*rho*u)*(rho/2)*(z.2:ℝ)*
            Real.exp (-(z.1:ℝ)*rho*(t-u))) volume 0 t :=
        (by fun_prop : Continuous _).intervalIntegrable _ _
      have hg : IntervalIntegrable
          (fun u : ℝ => Real.exp (-(n:ℝ)*rho*u)*(rho/2)*exprValue p rho (t-u)) volume 0 t :=
        (((by fun_prop : Continuous (fun u : ℝ => Real.exp (-(n:ℝ)*rho*u)*(rho/2)))).mul hc).intervalIntegrable _ _
      calc
        _ = (∫ u in (0:ℝ)..t, Real.exp (-(n:ℝ)*rho*u)*(rho/2)*(z.2:ℝ)*
              Real.exp (-(z.1:ℝ)*rho*(t-u))) +
            (∫ u in (0:ℝ)..t, Real.exp (-(n:ℝ)*rho*u)*(rho/2)*exprValue p rho (t-u)) := by
          rw [← intervalIntegral.integral_add hf hg]
          apply intervalIntegral.integral_congr
          intro u _
          dsimp only
          rw [exprValue_cons]
          ring
        _ = _ := by
          rw [damped_monomial_integral _ _ _ _ _ hn,ih hp]
          simp only [liftExpr,List.flatMap_cons,exprValue_append,exprValue_liftTerm]

lemma merger_exponent_lt (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (hk : 2 ≤ liveCard s) :
    (liveCard (stepDestination N s (some p))).choose 2 < (liveCard s).choose 2 := by
  have hc := merger_destination_card N s p
  have hj : 0 < liveCard (stepDestination N s (some p)) := by omega
  rw [← hc,Nat.choose_succ_succ,Nat.choose_one_right]
  change (liveCard (stepDestination N s (some p))).choose 2 <
    liveCard (stepDestination N s (some p)) + (liveCard (stepDestination N s (some p))).choose 2
  omega

lemma kernelExpr_bound (N : RootedBinary V E X) {sample : Copy → X}
    (budget : ℕ) (s d : Code N sample) :
    ∀ z ∈ kernelExpr N budget s d, z.1 ≤ (liveCard s).choose 2 := by
  induction budget generalizing s with
  | zero => simp [kernelExpr]
  | succ budget ih =>
      by_cases hk : liveCard s ≤ 1
      · simp [kernelExpr,hk]
      · intro z hz
        simp only [kernelExpr,if_neg hk,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with hz | hz
        · subst z
          exact le_rfl
        · obtain ⟨p,hp,hz⟩ := List.mem_flatMap.mp hz
          obtain ⟨w,hw,hz⟩ := List.mem_flatMap.mp hz
          have hb := ih (stepDestination N s (some p)) w hw
          have he := merger_exponent_lt N s p (by omega)
          simp only [liftTerm,List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with hz | hz
          · subst z
            exact (hb.trans_lt he).le
          · subst z
            exact le_rfl

lemma exprValue_flatMap {A : Type*} (xs : List A) (f : A → Expr) (rho t : ℝ) :
    exprValue (xs.flatMap f) rho t = (xs.map (fun a => exprValue (f a) rho t)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,exprValue_append,List.map_cons,List.sum_cons,ih]

lemma exprValue_finite {A : Type*} [Fintype A] (f : A → Expr) (rho t : ℝ) :
    exprValue (Finset.univ.toList.flatMap f) rho t = ∑ a : A, exprValue (f a) rho t := by
  rw [exprValue_flatMap,Finset.sum_map_toList]

/-- The recursively constructed rational expression is the ACTUAL entire
ancestral source transition row, uniformly in the positive physical rate bank.
No polynomial law or finite-time approximation is supplied as a premise. -/
theorem kernelExpr_actual (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (budget : ℕ) (s d : Code N sample) (t : ℝ≥0)
    (hs : AncestralRoot N s) (hb : liveCard s ≤ budget) :
    exprValue (kernelExpr N budget s d) r.ancestral (t:ℝ) =
      (sourceTimeKernel N r t s d).toReal := by
  induction budget generalizing s t with
  | zero =>
      rw [actual_terminal_epoch N r s d t (by omega)]
      by_cases he : s=d <;> simp [kernelExpr,exprValue,he]
  | succ budget ih =>
      by_cases hk : liveCard s ≤ 1
      · rw [kernelExpr,if_pos hk,actual_terminal_epoch N r s d t hk]
        by_cases he : s=d <;> simp [exprValue,he]
      · have hold : exprValue [((liveCard s).choose 2,if s=d then 1 else 0)]
            r.ancestral (t:ℝ) =
            Real.exp (-(totalRate N r s*(t:ℝ))) * (if s=d then 1 else 0) := by
          rw [actual_ancestral_holding_rate N r s hs]
          by_cases he : s=d
          · simp only [he,if_pos,exprValue_cons,exprValue_nil,Rat.cast_one,one_mul,add_zero,mul_one]
            congr 1
            ring
          · simp [exprValue,he]
        rw [kernelExpr,if_neg hk,exprValue_append,hold,exprValue_finite,
          actual_source_kernel_first_jump]
        congr 1
        symm
        let phi := fun (p : Choice N s) (u : ℝ) =>
          Real.exp (-((liveCard s).choose 2 : ℝ)*r.ancestral*u)*(r.ancestral/2)*
            exprValue (kernelExpr N budget (stepDestination N s (some p)) d)
              r.ancestral ((t:ℝ)-u)
        have hphi (p : Choice N s) : IntervalIntegrable (phi p) volume 0 (t:ℝ) := by
          have hc : Continuous (fun u : ℝ =>
              exprValue (kernelExpr N budget (stepDestination N s (some p)) d)
                r.ancestral ((t:ℝ)-u)) :=
            (exprValue_continuous _ _).comp (continuous_const.sub continuous_id)
          exact ((by fun_prop : Continuous (fun u : ℝ =>
            Real.exp (-((liveCard s).choose 2 : ℝ)*r.ancestral*u)*(r.ancestral/2))).mul hc).intervalIntegrable _ _
        calc
          _ = ∫ u in (0:ℝ)..(t:ℝ), ∑ p : Choice N s, phi p u := by
            apply intervalIntegral.integral_congr
            intro u hu
            dsimp only
            have hut : u ≤ (t:ℝ) := by
              have hh : u ∈ Set.Icc (0:ℝ) (t:ℝ) := by
                simpa only [Set.uIcc_of_le (show (0:ℝ) ≤ (t:ℝ) from t.property)] using hu
              exact hh.2
            have hexp : Real.exp (-(totalRate N r s*u)) =
                Real.exp (-((liveCard s).choose 2 : ℝ)*r.ancestral*u) := by
              rw [actual_ancestral_holding_rate N r s hs]
              congr 1
              ring
            rw [hexp,Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            have hc := merger_destination_card N s p
            have he := ih (stepDestination N s (some p)) (Real.toNNReal ((t:ℝ)-u))
              (ancestral_merger_preserved N s hs p) (by omega)
            rw [Real.coe_toNNReal _ (sub_nonneg.mpr hut)] at he
            rw [← he,ancestral_choice_rate N r s hs p]
            dsimp [phi,pairRate]
            ring
          _ = ∑ p : Choice N s, ∫ u in (0:ℝ)..(t:ℝ), phi p u :=
            intervalIntegral.integral_finsetSum (fun p _ => hphi p)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro p _
            apply integral_exprValue
            intro z hz
            exact (kernelExpr_bound N budget (stepDestination N s (some p)) d z hz).trans_lt
              (merger_exponent_lt N s p (by omega))

@[simp] lemma exprPolynomial_nil : exprPolynomial [] = 0 := rfl

@[simp] lemma exprPolynomial_cons (z : ℕ × ℚ) (p : Expr) :
    exprPolynomial (z::p) = Polynomial.C z.2 * Polynomial.X ^ z.1 + exprPolynomial p := rfl

lemma exprPolynomial_eval (p : Expr) (rho t : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-rho*t)) (exprPolynomial p) =
      exprValue p rho t := by
  have he (n : ℕ) : Real.exp (-rho*t)^n = Real.exp (-(n:ℝ)*rho*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  induction p with
  | nil => simp
  | cons z p ih =>
      simp only [exprPolynomial_cons,Polynomial.eval₂_add,Polynomial.eval₂_mul,
        Polynomial.eval₂_C,Polynomial.eval₂_pow,Polynomial.eval₂_X,exprValue_cons,he,ih]
      rfl

/-- A rational polynomial built from actual source choices and destinations.
Its coefficients contain no physical rates or source-probability fits. -/
noncomputable def ancestralPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) : Polynomial ℚ :=
  exprPolynomial (kernelExpr N (Fintype.card Copy) s d)

/-- Entire actual ancestral transition law, at arbitrary finite positive rate
and nonnegative time, represented by one explicitly constructed rational
polynomial in the physical survival coordinate. -/
theorem actual_ancestral_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (hs : AncestralRoot N s)
    (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-r.ancestral*(t:ℝ)))
      (ancestralPolynomial N s d) = (sourceTimeKernel N r t s d).toReal := by
  rw [ancestralPolynomial,exprPolynomial_eval]
  exact kernelExpr_actual N r _ s d t hs (Finset.card_le_univ s.val.live)

lemma exprPolynomial_degree (p : Expr) (n : ℕ)
    (hb : ∀ z ∈ p, z.1 ≤ n) : (exprPolynomial p).natDegree ≤ n := by
  induction p with
  | nil => simp
  | cons z p ih =>
      rw [exprPolynomial_cons]
      apply Polynomial.natDegree_add_le_of_degree_le
      · rw [Polynomial.C_mul_X_pow_eq_monomial]
        exact (Polynomial.natDegree_monomial_le z.2).trans (hb z (by simp))
      · exact ih (fun w hw => hb w (by simp [hw]))

theorem ancestralPolynomial_degree (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) :
    (ancestralPolynomial N s d).natDegree ≤ (liveCard s).choose 2 :=
  exprPolynomial_degree _ _ (kernelExpr_bound N _ s d)

end GProgram.G7.AncestralPolynomialKernel
