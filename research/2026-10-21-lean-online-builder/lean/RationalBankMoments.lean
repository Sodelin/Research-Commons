import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum

namespace Astra.RationalBankMoments

open scoped BigOperators

def rationalMoment {A : Type*} [Fintype A] (weight value : A → ℚ) (k : ℕ) : ℚ :=
  ∑ a, weight a * value a ^ (k.choose 2)

noncomputable def realMoment {A : Type*} [Fintype A]
    (weight value : A → ℝ) (k : ℕ) : ℝ :=
  ∑ a, weight a * value a ^ (k.choose 2)

/-- One fixed rational bank is cast once; changing k changes only its exponent. -/
theorem cast_moment {A : Type*} [Fintype A] (weight value : A → ℚ) (k : ℕ) :
    realMoment (fun a => (weight a : ℝ)) (fun a => (value a : ℝ)) k =
      (rationalMoment weight value k : ℝ) := by
  unfold realMoment rationalMoment
  have h := map_sum (Rat.castHom ℝ)
    (fun a => weight a * value a ^ (k.choose 2)) Finset.univ
  simpa only [Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow] using h.symm

theorem cast_normalized_bank {A : Type*} [Fintype A]
    (weight value : A → ℚ) (hw : ∀ a, 0 ≤ weight a)
    (hx : ∀ a, 0 < value a ∧ value a ≤ 1) (hmass : ∑ a, weight a = 1) :
    (∀ a, (0:ℝ) ≤ weight a) ∧
    (∀ a, (0:ℝ) < value a ∧ (value a : ℝ) ≤ 1) ∧
    (∑ a, (weight a : ℝ)) = 1 ∧
    ∀ k, realMoment (fun a => (weight a : ℝ)) (fun a => (value a : ℝ)) k =
      (rationalMoment weight value k : ℝ) := by
  refine ⟨?_,?_,?_,cast_moment weight value⟩
  · intro a
    exact_mod_cast hw a
  · intro a
    constructor
    · exact_mod_cast (hx a).1
    · exact_mod_cast (hx a).2
  · calc
      _ = ((∑ a, weight a : ℚ) : ℝ) := (map_sum (Rat.castHom ℝ) weight Finset.univ).symm
      _ = 1 := by rw [hmass]; norm_num

end Astra.RationalBankMoments
