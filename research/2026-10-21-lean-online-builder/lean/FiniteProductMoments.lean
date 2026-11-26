import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace FiniteProductMoments

open scoped BigOperators

variable {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]

noncomputable def productWeight (w : J → A → ℝ) (z : J → A) : ℝ := ∏ j, w j (z j)

theorem factor (f : J → A → ℝ) :
    (∑ z : J → A, ∏ j, f j (z j)) = ∏ j, ∑ a, f j a :=
  (Fintype.prod_sum f).symm

theorem normalized (w : J → A → ℝ) (hw : ∀ j, ∑ a, w j a = 1) :
    (∑ z : J → A, productWeight w z) = 1 := by
  unfold productWeight
  rw [factor]
  simp only [hw, Finset.prod_const_one]

theorem nonnegative (w : J → A → ℝ) (hw : ∀ j a, 0 ≤ w j a) (z : J → A) :
    0 ≤ productWeight w z := Finset.prod_nonneg (fun j _ => hw j (z j))

theorem coordinate_mean (w : J → A → ℝ) (hw : ∀ j, ∑ a, w j a = 1)
    (i : J) (f : A → ℝ) :
    (∑ z : J → A, productWeight w z * f (z i)) = ∑ a, w i a*f a := by
  have hleft (z : J → A) :
      (∏ j, w j (z j) * (if j=i then f (z j) else 1)) = productWeight w z*f (z i) := by
    rw [Finset.prod_mul_distrib]
    simp [productWeight]
  have hright (j : J) :
      (∑ a, w j a * (if j=i then f a else 1)) = if j=i then (∑ a, w i a*f a) else 1 := by
    by_cases hji : j=i
    · subst j
      simp
    · simp [hji,hw]
  calc
    _ = ∑ z : J → A, ∏ j, w j (z j)*(if j=i then f (z j) else 1) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (hleft z).symm
    _ = _ := by
      rw [factor (fun j a => w j a*(if j=i then f a else 1))]
      simp only [hright]
      simp

theorem two_coordinate_mean (w : J → A → ℝ) (hw : ∀ j, ∑ a, w j a = 1)
    (i j : J) (hij : i ≠ j) (f g : A → ℝ) :
    (∑ z : J → A, productWeight w z * (f (z i)*g (z j))) =
      (∑ a, w i a*f a)*(∑ a, w j a*g a) := by
  have hleft (z : J → A) :
      (∏ k, w k (z k)*((if k=i then f (z k) else 1)*(if k=j then g (z k) else 1))) =
        productWeight w z*(f (z i)*g (z j)) := by
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    simp [productWeight]
  have hright (k : J) :
      (∑ a, w k a*((if k=i then f a else 1)*(if k=j then g a else 1))) =
        (if k=i then (∑ a, w i a*f a) else 1)*
        (if k=j then (∑ a, w j a*g a) else 1) := by
    by_cases hki : k=i
    · subst k
      simp [hij]
    · by_cases hkj : k=j
      · subst k
        simp [Ne.symm hij]
      · simp [hki,hkj,hw]
  calc
    _ = ∑ z : J → A, ∏ k, w k (z k)*
        ((if k=i then f (z k) else 1)*(if k=j then g (z k) else 1)) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (hleft z).symm
    _ = _ := by
      rw [factor (fun k a => w k a*((if k=i then f a else 1)*(if k=j then g a else 1)))]
      simp only [hright,Finset.prod_mul_distrib]
      simp

/-- Explicit finite product law: centered cross terms vanish by factorization,
with no physical independence axiom or probability-space model. -/
theorem sum_mean_and_variance (w u : J → A → ℝ) (d V : J → ℝ)
    (hwnorm : ∀ j, ∑ a, w j a = 1)
    (hmean : ∀ j, ∑ a, w j a*u j a = d j)
    (hvar : ∀ j, ∑ a, w j a*(u j a-d j)^2 = V j) :
    (∑ z : J → A, productWeight w z*(∑ j, u j (z j))) = ∑ j, d j ∧
    (∑ z : J → A, productWeight w z*((∑ j, u j (z j))-(∑ j, d j))^2) =
      ∑ j, V j := by
  let c : J → A → ℝ := fun j a => u j a-d j
  have hc (j : J) : (∑ a, w j a*c j a) = 0 := by
    simp only [c,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hmean,hwnorm,one_mul,sub_self]
  constructor
  · calc
      _ = ∑ j, ∑ z : J → A, productWeight w z*u j (z j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = _ := by simp only [coordinate_mean w hwnorm,hmean]
  · have hcarg (z : J → A) :
        ((∑ j, u j (z j))-(∑ j, d j))^2 = ∑ i, ∑ j, c i (z i)*c j (z j) := by
      rw [← Finset.sum_sub_distrib,pow_two,Finset.sum_mul_sum]
    calc
      _ = ∑ i, ∑ j, ∑ z : J → A, productWeight w z*(c i (z i)*c j (z j)) := by
        simp_rw [hcarg,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ i : J, ∑ j : J, if i=j then V i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i=j
        · subst j
          simpa only [ite_true,← pow_two,c] using
            (coordinate_mean w hwnorm i (fun a => (u i a-d i)^2)).trans (hvar i)
        · rw [two_coordinate_mean w hwnorm i j hij, hc, hc]
          simp [hij]
      _ = _ := by simp

end FiniteProductMoments
