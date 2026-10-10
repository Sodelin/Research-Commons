import G7SinglePopulationPolynomialKernel

/-! Explicit cap-only coefficient mass of the actual source recursion.
Draft G6 consumer of the frozen G7 polynomial source theorem. -/
namespace UnifiedLean.G6.ActualKernelCoefficientBound
open Nanuq.Source
open GProgram.G7.SinglePopulationPolynomialKernel
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteJumpExpansion
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.G6.AncestralRateFree
open scoped Classical BigOperators

def exprMass (p : Expr) : ℚ := (p.map fun z => |z.2|).sum

@[simp] theorem exprMass_nil : exprMass [] = 0 := rfl
@[simp] theorem exprMass_cons (z : ℕ × ℚ) (p : Expr) :
    exprMass (z::p) = |z.2| + exprMass p := rfl
@[simp] theorem exprMass_append (p q : Expr) :
    exprMass (p++q) = exprMass p + exprMass q := by
  simp [exprMass,List.map_append,List.sum_append]

theorem exprMass_nonneg (p : Expr) : 0 ≤ exprMass p := by
  induction p with
  | nil => exact le_rfl
  | cons z p ih => exact add_nonneg (abs_nonneg _) ih

theorem liftTerm_mass (n : ℕ) (z : ℕ × ℚ) (hz : z.1 < n) :
    exprMass (liftTerm n z) ≤ |z.2| := by
  have hd : (1:ℚ) ≤ (n:ℚ)-(z.1:ℚ) := by
    have hc : (z.1:ℚ)+1≤(n:ℚ) := by exact_mod_cast (show z.1+1≤n by omega)
    linarith
  have hd2 : (0:ℚ) < 2*((n:ℚ)-(z.1:ℚ)) := by linarith
  have hh : |z.2 / (2*((n:ℚ)-(z.1:ℚ)))| ≤ |z.2|/2 := by
    rw [abs_div,abs_of_pos hd2]
    apply (div_le_div_iff₀ hd2 (by norm_num : (0:ℚ)<2)).mpr
    nlinarith [abs_nonneg z.2]
  simp only [liftTerm,exprMass_cons,exprMass_nil,abs_neg,add_zero]
  linarith

theorem liftExpr_mass (n : ℕ) (p : Expr) (hp : ∀ z ∈ p, z.1<n) :
    exprMass (liftExpr n p) ≤ exprMass p := by
  induction p with
  | nil => exact le_rfl
  | cons z p ih =>
      simp only [liftExpr,List.flatMap_cons,exprMass_append,exprMass_cons]
      exact add_le_add (liftTerm_mass n z (hp z (by simp)))
        (ih (fun w hw => hp w (by simp [hw])))

theorem flatMap_mass {A : Type*} (xs : List A) (f : A → Expr) :
    exprMass (xs.flatMap f) = (xs.map fun a => exprMass (f a)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.flatMap_cons,ih]

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def rowMass (N : RootedBinary V E X) {sample : Copy → X}
    (budget : ℕ) (s : Code N sample) : ℚ :=
  ∑ d : Code N sample, exprMass (kernelExpr N budget s d)

lemma delta_mass (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (n : ℕ) :
    (∑ d : Code N sample, exprMass [(n,if s=d then 1 else 0)]) = 1 := by
  calc
    _ = ∑ d : Code N sample, if d=s then (1:ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases h : s=d
      · subst d
        simp [exprMass]
      · simp [exprMass,h,Ne.symm h]
    _ = 1 := by simp

/-- Entire output-row expression mass, before any duplicate monomials are
collected. The cap-only bound is explicit and independent of physical rates,
source labels, coefficients chosen by classical finite representations, or the
number of irrelevant raw Code representatives. -/
theorem actual_row_mass_bound (N : RootedBinary V E X) {sample : Copy → X}
    (M budget : ℕ) (s : Code N sample) (i : Option E)
    (hs : CoLocated N s i) (hM : liveCard s ≤ M) :
    rowMass N budget s ≤ ((1+M*M : ℕ):ℚ)^budget := by
  induction budget generalizing s with
  | zero => simpa only [rowMass,kernelExpr,pow_zero] using (delta_mass N s 0).le
  | succ budget ih =>
      by_cases hk : liveCard s ≤ 1
      · have hpow : (1:ℚ) ≤ ((1+M*M : ℕ):ℚ)^(budget+1) := by
          apply one_le_pow₀
          exact_mod_cast (show 1≤1+M*M by omega)
        unfold rowMass
        simp only [kernelExpr,if_pos hk,delta_mass]
        exact hpow
      · have hchild (p : Choice N s) :
            rowMass N budget (stepDestination N s (some p)) ≤ ((1+M*M : ℕ):ℚ)^budget := by
          apply ih _ (population_merger_preserved N s i hs p)
          have hc := merger_destination_card N s p
          omega
        have hlift (p : Choice N s) (d : Code N sample) :
            exprMass (liftExpr ((liveCard s).choose 2)
              (kernelExpr N budget (stepDestination N s (some p)) d)) ≤
            exprMass (kernelExpr N budget (stepDestination N s (some p)) d) := by
          apply liftExpr_mass
          intro z hz
          exact (kernelExpr_bound N budget _ d z hz).trans_lt
            (merger_exponent_lt N s p (by omega))
        have hcard : (Fintype.card (Choice N s) : ℚ) ≤ (M*M : ℕ) := by
          rw [population_choice_card N s i hs]
          exact_mod_cast Nat.mul_le_mul hM (Nat.le_trans (Nat.sub_le _ _) hM)
        have hpow : (1:ℚ) ≤ ((1+M*M : ℕ):ℚ)^budget := by
          apply one_le_pow₀
          exact_mod_cast (show 1≤1+M*M by omega)
        have hmass : rowMass N (budget+1) s ≤
            1 + (Fintype.card (Choice N s) : ℚ) * ((1+M*M : ℕ):ℚ)^budget := by
          unfold rowMass
          simp only [kernelExpr,if_neg hk,exprMass_append,Finset.sum_add_distrib,
            flatMap_mass,List.map_map,Function.comp_def,Finset.sum_map_toList,delta_mass]
          rw [Finset.sum_comm]
          apply add_le_add le_rfl
          calc
            _ ≤ ∑ p : Choice N s, ∑ d : Code N sample,
                exprMass (kernelExpr N budget (stepDestination N s (some p)) d) := by
              exact Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun d hd => hlift p d
            _ ≤ ∑ _p : Choice N s, ((1+M*M : ℕ):ℚ)^budget :=
              Finset.sum_le_sum fun p hp => hchild p
            _ = _ := by simp
        have hb : ((1+M*M : ℕ):ℚ) = 1+(M*M : ℕ) := by norm_cast
        have hmul := mul_le_mul_of_nonneg_right hcard (le_trans (by norm_num) hpow)
        calc
          rowMass N (budget+1) s ≤ 1 + (M*M : ℕ)*((1+M*M : ℕ):ℚ)^budget :=
            hmass.trans (add_le_add le_rfl hmul)
          _ ≤ ((1+M*M : ℕ):ℚ)^budget * ((1+M*M : ℕ):ℚ) := by
            have heq : ((1+M*M : ℕ):ℚ)^budget * ((1+M*M : ℕ):ℚ) =
                ((1+M*M : ℕ):ℚ)^budget + (M*M : ℕ)*((1+M*M : ℕ):ℚ)^budget := by
              rw [hb]
              ring
            rw [heq]
            exact add_le_add hpow le_rfl
          _ = _ := (pow_succ _ _).symm

end UnifiedLean.G6.ActualKernelCoefficientBound
