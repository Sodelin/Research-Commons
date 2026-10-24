import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import P1ProductStatistic

namespace P1FiniteThreshold

open scoped BigOperators

noncomputable def mass {Omega : Type*} [Fintype Omega]
    (w : Omega → ℝ) (bad : Omega → Prop) [DecidablePred bad] : ℝ :=
  ∑ x ∈ Finset.univ.filter bad, w x

theorem weighted_bad_mass {Omega : Type*} [Fintype Omega]
    (w f : Omega → ℝ) (bad : Omega → Prop) [DecidablePred bad] (b : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x)
    (hbad : ∀ x, bad x → b ≤ f x) :
    b * mass w bad ≤ ∑ x, w x*f x := by
  unfold mass
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ x ∈ Finset.univ.filter bad, w x*f x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [mul_comm b (w x)]
      exact mul_le_mul_of_nonneg_left (hbad x (Finset.mem_filter.mp hx).2) (hw x)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => mul_nonneg (hw x) (hf x))

theorem centered_bad_mass {Omega : Type*} [Fintype Omega]
    (w U : Omega → ℝ) (bad : Omega → Prop) [DecidablePred bad] (S b : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hb : 0 < b)
    (hbad : ∀ x, bad x → b ≤ (U x-S)^2) :
    mass w bad ≤ (∑ x, w x*(U x-S)^2)/b := by
  apply (le_div_iff₀ hb).mpr
  rw [mul_comm]
  exact weighted_bad_mass w (fun x => (U x-S)^2) bad b hw (fun x => sq_nonneg _) hbad

theorem sample_budget_bounds (m N a q : ℝ) (hm : 0 < m) (ha : 0 < a)
    (hma : 128 ≤ m*a) (hbudget : 16384*N ≤ (m*a)^2) (haq : a ≤ q) :
    32/(m*q) ≤ 1/4 ∧ 144*N/(m^2*q^2) ≤ 9/1024 := by
  have hq : 0 < q := lt_of_lt_of_le ha haq
  have hmq : 0 < m*q := mul_pos hm hq
  have hcomp : m*a ≤ m*q := mul_le_mul_of_nonneg_left haq hm.le
  have hsq : (m*a)^2 ≤ (m*q)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcomp) (by positivity : 0 ≤ m*q+m*a)]
  constructor
  · apply (div_le_iff₀ hmq).mpr
    linarith
  · apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hm) (sq_pos_of_pos hq))).mpr
    have heq : (m*q)^2 = m^2*q^2 := by ring
    rw [heq] at hsq
    nlinarith

/-- The literal strict-accept/non-strict-reject finite experiment. Physical
Born/product laws, entropy separation and sqrt/ceil copy budgets are separate. -/
theorem finite_threshold_errors {Omega : Type*} [Fintype Omega]
    (w U : Omega → ℝ) (m N : ℕ) (a S : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hnorm : ∑ x, w x = 1)
    (hmean : ∑ x, w x*U x = S)
    (hvar : (∑ x, w x*(U x-S)^2) ≤ 8*S/(m:ℝ)+36*(N:ℝ)/(m:ℝ)^2)
    (hm : 2 ≤ m) (ha : 0 < a) (hma : 128 ≤ (m:ℝ)*a)
    (hbudget : 16384*(N:ℝ) ≤ ((m:ℝ)*a)^2) :
    (S = 0 → mass w (fun x => a/2 ≤ U x) ≤ 9/1024) ∧
    (a ≤ S → mass w (fun x => U x < a/2) ≤ 265/1024) ∧
    (265/1024 : ℝ) < 1/3 := by
  classical
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have ha2 : 0 < (a/2)^2 := sq_pos_of_pos (by linarith)
  refine ⟨?_,?_,by norm_num⟩
  · intro hS
    have hbad := centered_bad_mass w U (fun x => a/2 ≤ U x) S ((a/2)^2) hw ha2 (by
      intro x hx
      rw [hS]
      nlinarith [mul_nonneg (by linarith : 0 ≤ U x-a/2) (by linarith : 0 ≤ U x+a/2)])
    have hb := (sample_budget_bounds (m:ℝ) (N:ℝ) a a hmpos ha hma hbudget le_rfl).2
    calc
      _ ≤ (8*S/(m:ℝ)+36*(N:ℝ)/(m:ℝ)^2)/((a/2)^2) :=
        hbad.trans (div_le_div_of_nonneg_right hvar ha2.le)
      _ = 144*(N:ℝ)/((m:ℝ)^2*a^2) := by rw [hS]; field_simp; ring
      _ ≤ _ := hb
  · intro hSa
    have hSpos : 0 < S := lt_of_lt_of_le ha hSa
    have hS2 : 0 < (S/2)^2 := sq_pos_of_pos (by linarith)
    have hbad := centered_bad_mass w U (fun x => U x < a/2) S ((S/2)^2) hw hS2 (by
      intro x hx
      nlinarith [mul_nonneg (by linarith : 0 ≤ S-U x-S/2)
        (by linarith : 0 ≤ S-U x+S/2)])
    have hb := sample_budget_bounds (m:ℝ) (N:ℝ) a S hmpos ha hma hbudget hSa
    calc
      _ ≤ (8*S/(m:ℝ)+36*(N:ℝ)/(m:ℝ)^2)/((S/2)^2) :=
        hbad.trans (div_le_div_of_nonneg_right hvar hS2.le)
      _ = 32/((m:ℝ)*S)+144*(N:ℝ)/((m:ℝ)^2*S^2) := by
        field_simp [ne_of_gt hmpos,ne_of_gt hSpos]
        ring
      _ ≤ 1/4+9/1024 := add_le_add hb.1 hb.2
      _ = _ := by norm_num

/-- Direct finite assembly for 3N product coordinates. The actual physical
experiment and its 6m total-copy interpretation are still separate suppliers. -/
theorem finite_product_threshold_errors (m N : ℕ) (a : ℝ)
    (r s : Fin (3*N) → ℝ) (hm : 2 ≤ m) (ha : 0 < a)
    (hr : ∀ j, -1 ≤ r j ∧ r j ≤ 1) (hs : ∀ j, -1 ≤ s j ∧ s j ≤ 1)
    (hma : 128 ≤ (m:ℝ)*a) (hbudget : 16384*(N:ℝ) ≤ ((m:ℝ)*a)^2) :
    let W := FiniteProductMoments.productWeight
      (fun j => P1ScalarMoments.coordinateWeight (r j) (s j) m)
    let U := fun z : Fin (3*N) → P1ScalarMoments.CountOutcome m =>
      ∑ j, P1ScalarMoments.coordinateValue m (z j)
    let S := ∑ j, (r j-s j)^2
    (S = 0 → mass W (fun z => a/2 ≤ U z) ≤ 9/1024) ∧
    (a ≤ S → mass W (fun z => U z < a/2) ≤ 265/1024) ∧
    (265/1024 : ℝ) < 1/3 := by
  dsimp only
  have h := P1ScalarMoments.finite_product_quadratic_moments m hm r s hr hs
  dsimp only at h
  apply finite_threshold_errors _ _ m N a _ h.1 h.2.1 h.2.2.1 _ hm ha hma hbudget
  rw [h.2.2.2.1]
  calc
    _ ≤ _ := h.2.2.2.2
    _ = _ := by simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]; ring

end P1FiniteThreshold
