import ActualKernelCoefficientBound
import UnifiedLean.G6.FiniteProbability

/-! Explicit source-epoch modulus from the actual rational expression bound.
Draft; verification is recorded separately. -/
namespace UnifiedLean.G6.ActualKernelCoefficientBound
open Nanuq.Source
open GProgram.G7.SinglePopulationPolynomialKernel
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.FiniteProbability
open scoped Classical BigOperators NNReal

lemma unit_power_lipschitz (x y : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤y) (hy1 : y≤1) (k : ℕ) :
    |x^k-y^k| ≤ (k:ℝ)*|x-y| := by
  have hm : max |x| |y| ≤ (1:ℝ) := by
    rw [abs_of_nonneg hx0,abs_of_nonneg hy0]
    exact max_le hx1 hy1
  have hp : (max |x| |y|)^(k-1) ≤ (1:ℝ) :=
    pow_le_one₀ (le_trans (abs_nonneg x) (le_max_left _ _)) hm
  calc
    |x^k-y^k| ≤ |x-y| *k*(max |x| |y|)^(k-1) := abs_pow_sub_pow_le x y k
    _ ≤ |x-y| *k*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem expression_lipschitz (p : Expr) (D : ℕ)
    (hD : ∀ z ∈ p, z.1≤D) (x y : ℝ)
    (hx0 : 0≤x) (hx1 : x≤1) (hy0 : 0≤y) (hy1 : y≤1) :
    |Polynomial.eval₂ (Rat.castHom ℝ) x (exprPolynomial p) -
      Polynomial.eval₂ (Rat.castHom ℝ) y (exprPolynomial p)| ≤
      (D:ℝ)*(exprMass p:ℝ)*|x-y| := by
  induction p with
  | nil => simp
  | cons z p ih =>
      have hz : z.1≤D := hD z (by simp)
      have ht := ih (fun w hw => hD w (by simp [hw]))
      have hzR : (z.1:ℝ)≤D := by exact_mod_cast hz
      have hp := (unit_power_lipschitz x y hx0 hx1 hy0 hy1 z.1).trans
        (mul_le_mul_of_nonneg_right hzR (abs_nonneg _))
      have hc : |(z.2:ℝ)*(x^z.1-y^z.1)| ≤ |(z.2:ℝ)| *((D:ℝ)*|x-y|) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      simp only [exprPolynomial_cons,Polynomial.eval₂_add,Polynomial.eval₂_mul,
        Polynomial.eval₂_C,Polynomial.eval₂_pow,Polynomial.eval₂_X]
      have he : (z.2:ℝ)*x^z.1 + Polynomial.eval₂ (Rat.castHom ℝ) x (exprPolynomial p) -
          ((z.2:ℝ)*y^z.1 + Polynomial.eval₂ (Rat.castHom ℝ) y (exprPolynomial p)) =
          (z.2:ℝ)*(x^z.1-y^z.1) +
          (Polynomial.eval₂ (Rat.castHom ℝ) x (exprPolynomial p) -
            Polynomial.eval₂ (Rat.castHom ℝ) y (exprPolynomial p)) := by ring
      change |(z.2:ℝ)*x^z.1 + Polynomial.eval₂ (Rat.castHom ℝ) x (exprPolynomial p) -
        ((z.2:ℝ)*y^z.1 + Polynomial.eval₂ (Rat.castHom ℝ) y (exprPolynomial p))| ≤ _
      rw [he]
      calc
        _ ≤ |(z.2:ℝ)*(x^z.1-y^z.1)| +
            |Polynomial.eval₂ (Rat.castHom ℝ) x (exprPolynomial p) -
              Polynomial.eval₂ (Rat.castHom ℝ) y (exprPolynomial p)| := abs_add_le _ _
        _ ≤ |(z.2:ℝ)| *((D:ℝ)*|x-y|) + (D:ℝ)*(exprMass p:ℝ)*|x-y| := add_le_add hc ht
        _ = _ := by simp only [exprMass_cons,Rat.cast_add,Rat.cast_abs]; ring

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- A fully explicit cap-only modulus for two ACTUAL co-located source epochs.
Other rates may differ; the bound uses only the one physical survival coordinate.
No coefficient extraction, inverse source, or source-law approximation premise. -/
theorem actual_epoch_survival_modulus (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r r' : PositivePairRates E) (t t' : ℝ≥0) :
    pmfTV (sourceTimeKernel N r t s) (sourceTimeKernel N r' t' s) ≤
      ((Fintype.card Copy).choose 2 : ℝ) *
      ((1+(Fintype.card Copy)*(Fintype.card Copy) : ℕ):ℝ)^(Fintype.card Copy) *
      |Real.exp (-(pairRate r i)*(t:ℝ)) - Real.exp (-(pairRate r' i)*(t':ℝ))| / 2 := by
  let M := Fintype.card Copy
  let D := M.choose 2
  let x := Real.exp (-(pairRate r i)*(t:ℝ))
  let y := Real.exp (-(pairRate r' i)*(t':ℝ))
  have hx0 : 0≤x := (Real.exp_pos _).le
  have hy0 : 0≤y := (Real.exp_pos _).le
  have hx1 : x≤1 := Real.exp_le_one_iff.mpr (by nlinarith [pairRate_pos r i,t.coe_nonneg])
  have hy1 : y≤1 := Real.exp_le_one_iff.mpr (by nlinarith [pairRate_pos r' i,t'.coe_nonneg])
  have hM : liveCard s≤M := Finset.card_le_univ _
  have hd (d : Code N sample) : ∀ z ∈ kernelExpr N M s d, z.1≤D :=
    fun z hz => (kernelExpr_bound N M s d z hz).trans (Nat.choose_le_choose 2 hM)
  have hp (d : Code N sample) :
      |(sourceTimeKernel N r t s d).toReal-(sourceTimeKernel N r' t' s d).toReal| ≤
      (D:ℝ)*(exprMass (kernelExpr N M s d):ℝ)*|x-y| := by
    rw [← actual_population_polynomial N s d i hs r t,
      ← actual_population_polynomial N s d i hs r' t']
    exact expression_lipschitz (kernelExpr N M s d) D (hd d) x y hx0 hx1 hy0 hy1
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) => hp d)
  have hm : (rowMass N M s:ℝ) ≤ ((1+M*M:ℕ):ℝ)^M := by
    exact_mod_cast actual_row_mass_bound N M M s i hs hM
  have he : (∑ d : Code N sample, (D:ℝ)*(exprMass (kernelExpr N M s d):ℝ)*|x-y|) =
      (D:ℝ)*(rowMass N M s:ℝ)*|x-y| := by
    simp [rowMass,Finset.mul_sum,Finset.sum_mul]
  rw [he] at hsum
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg D)) (abs_nonneg (x-y))
  unfold pmfTV tv
  change (∑ a, |(sourceTimeKernel N r t s a).toReal-(sourceTimeKernel N r' t' s a).toReal|)/2 ≤
    (D:ℝ)*((1+M*M:ℕ):ℝ)^M*|x-y|/2
  exact div_le_div_of_nonneg_right (hsum.trans hmul) (by norm_num)

end UnifiedLean.G6.ActualKernelCoefficientBound
