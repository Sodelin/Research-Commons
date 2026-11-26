import P1ScalarStatistic
import FiniteProductMoments
import Mathlib.Algebra.BigOperators.Fin

namespace P1ScalarMoments

open scoped BigOperators

abbrev CountOutcome (n : ℕ) := Fin (n+1) × Fin (n+1)

noncomputable def coordinateWeight (r s : ℝ) (n : ℕ) (a : CountOutcome n) : ℝ :=
  countWeight r n a.1.val * countWeight s n a.2.val

noncomputable def coordinateValue (n : ℕ) (a : CountOutcome n) : ℝ :=
  quadraticStatistic n (2*(a.1.val:ℝ)-(n:ℝ)) (2*(a.2.val:ℝ)-(n:ℝ))

noncomputable def scalarVariance (n : ℕ) (r s : ℝ) : ℝ :=
  4*(r-s)^2*((1-r^2)+(1-s^2))/(n:ℝ) +
  2*((1-r^2)^2+(1-s^2)^2)/((n:ℝ)*((n:ℝ)-1)) +
  4*(1-r^2)*(1-s^2)/(n:ℝ)^2

theorem coordinate_statistics (n : ℕ) (hn : 2 ≤ n) (r s : ℝ)
    (hr : -1 ≤ r ∧ r ≤ 1) (hs : -1 ≤ s ∧ s ≤ 1) :
    (∀ a : CountOutcome n, 0 ≤ coordinateWeight r s n a) ∧
    (∑ a : CountOutcome n, coordinateWeight r s n a) = 1 ∧
    (∑ a : CountOutcome n, coordinateWeight r s n a*coordinateValue n a) = (r-s)^2 ∧
    (∑ a : CountOutcome n, coordinateWeight r s n a*(coordinateValue n a-(r-s)^2)^2) =
      scalarVariance n r s := by
  have h := finite_binomial_quadratic_moments n hn r s hr hs
  refine ⟨fun a => h.1 a.1.val a.2.val, ?_⟩
  have convsum (f : ℕ → ℕ → ℝ) :
      (∑ a : Fin (n+1), ∑ b : Fin (n+1), f a.val b.val) =
        ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), f a b := by
    rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (n+1), f a b.val) (n+1)]
    apply Finset.sum_congr rfl
    intro a ha
    exact Fin.sum_univ_eq_sum_range (fun b => f a b) (n+1)
  change (∑ a : CountOutcome n, countWeight r n a.1.val * countWeight s n a.2.val) = 1 ∧ _
  simp only [Fintype.sum_prod_type,coordinateWeight,coordinateValue,scalarVariance]
  rw [convsum (fun a b => countWeight r n a * countWeight s n b),
    convsum (fun a b => countWeight r n a * countWeight s n b *
      quadraticStatistic n (2*(a:ℝ)-(n:ℝ)) (2*(b:ℝ)-(n:ℝ))),
    convsum (fun a b => countWeight r n a * countWeight s n b *
      (quadraticStatistic n (2*(a:ℝ)-(n:ℝ)) (2*(b:ℝ)-(n:ℝ))-(r-s)^2)^2)]
  exact h.2

theorem bounded_scalar_variance (m d v w : ℝ) (hm : 2 ≤ m) (hd : 0 ≤ d)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    4*d*(v+w)/m + 2*(v^2+w^2)/(m*(m-1)) + 4*v*w/m^2 ≤
      8*d/m + 12/m^2 := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have hv2 : v^2 ≤ 1 := by nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  have hw2 : w^2 ≤ 1 := by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hvw : v*w ≤ 1 := by
    have h := mul_le_mul hv.2 hw.2 hw.1 (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using h
  have hfirst : 4*d*(v+w)/m ≤ 8*d/m :=
    div_le_div_of_nonneg_right (by nlinarith) hm0.le
  have hsecond : 2*(v^2+w^2)/(m*(m-1)) ≤ 8/m^2 := by
    calc
      _ ≤ 4/(m*(m-1)) := div_le_div_of_nonneg_right (by linarith) (mul_pos hm0 hm1).le
      _ ≤ _ := by
        apply (div_le_div_iff₀ (mul_pos hm0 hm1) (pow_pos hm0 2)).mpr
        nlinarith
  have hthird : 4*v*w/m^2 ≤ 4/m^2 :=
    div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg m)
  calc
    _ ≤ 8*d/m + 8/m^2 + 4/m^2 :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by ring

/-- The requested finite product experiment. Physical measurement/product-state
semantics are separate; this theorem uses exactly the displayed product W. -/
theorem finite_product_quadratic_moments {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (hn : 2 ≤ n) (r s : J → ℝ)
    (hr : ∀ j, -1 ≤ r j ∧ r j ≤ 1) (hs : ∀ j, -1 ≤ s j ∧ s j ≤ 1) :
    let W := FiniteProductMoments.productWeight (fun j => coordinateWeight (r j) (s j) n)
    let U := fun z : J → CountOutcome n => ∑ j, coordinateValue n (z j)
    let S := ∑ j, (r j-s j)^2
    (∀ z, 0 ≤ W z) ∧ (∑ z, W z) = 1 ∧
    (∑ z, W z*U z) = S ∧
    (∑ z, W z*(U z-S)^2) = (∑ j, scalarVariance n (r j) (s j)) ∧
    (∑ j, scalarVariance n (r j) (s j)) ≤ 8*S/(n:ℝ)+12*(Fintype.card J:ℝ)/(n:ℝ)^2 := by
  dsimp only
  have hcoord (j : J) := coordinate_statistics n hn (r j) (s j) (hr j) (hs j)
  have hprod := FiniteProductMoments.sum_mean_and_variance
    (fun j => coordinateWeight (r j) (s j) n) (fun _ => coordinateValue n)
    (fun j => (r j-s j)^2) (fun j => scalarVariance n (r j) (s j))
    (fun j => (hcoord j).2.1) (fun j => (hcoord j).2.2.1) (fun j => (hcoord j).2.2.2)
  refine ⟨FiniteProductMoments.nonnegative _ (fun j a => (hcoord j).1 a),
    FiniteProductMoments.normalized _ (fun j => (hcoord j).2.1), hprod.1,hprod.2,?_⟩
  have hb (j : J) : scalarVariance n (r j) (s j) ≤
      8*(r j-s j)^2/(n:ℝ)+12/(n:ℝ)^2 := by
    have hv : 0 ≤ 1-(r j)^2 ∧ 1-(r j)^2 ≤ 1 := by
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr (hr j).2) (by linarith [(hr j).1] : 0 ≤ 1+r j)]
      · nlinarith [sq_nonneg (r j)]
    have hw : 0 ≤ 1-(s j)^2 ∧ 1-(s j)^2 ≤ 1 := by
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr (hs j).2) (by linarith [(hs j).1] : 0 ≤ 1+s j)]
      · nlinarith [sq_nonneg (s j)]
    exact bounded_scalar_variance (n:ℝ) _ _ _ (by exact_mod_cast hn) (sq_nonneg _) hv hw
  calc
    _ ≤ ∑ j, (8*(r j-s j)^2/(n:ℝ)+12/(n:ℝ)^2) := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by
      simp only [Finset.sum_add_distrib,div_eq_mul_inv,← Finset.sum_mul,← Finset.mul_sum,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end P1ScalarMoments
