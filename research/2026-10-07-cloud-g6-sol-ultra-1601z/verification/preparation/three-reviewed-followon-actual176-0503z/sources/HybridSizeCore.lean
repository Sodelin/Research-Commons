import Mathlib.Tactic

/-!
UNCHECKED scalar prototype from the accepted corrected hybrid-size hand proof.
No compiler has run for these bytes. The definitions are scalar polynomials and
a finite recurrence. They do not define a biological source or assume its law.
Source ancestry/projectivity, physical positive realization, the algebraic
minimum m, finite-source extraction and general G3 recognition are separate.
-/

namespace CloudG3.HybridSizeCore

def cellT (p q u v : ℝ) : ℝ :=
  (2 / 3 : ℝ) * (q * u ^ 3 + p * v ^ 3 - 3 * p * q * (u - v) ^ 2)

theorem drop_v_identity (p q u v : ℝ) :
    cellT p q u v - cellT p q u 0 =
      (2 / 3 : ℝ) * p * v * (v ^ 2 + 3 * q * (2 * u - v)) := by
  unfold cellT
  ring

/-- The corrected identity, with no square factorization of `p-u`. -/
theorem push_u_identity (p q u : ℝ) :
    cellT p q u 0 - cellT p q p 0 =
      (2 / 3 : ℝ) * q * (p - u) * (2 * p ^ 2 + 2 * p * u - u ^ 2) := by
  unfold cellT
  ring

theorem quartic_gap_identity (p : ℝ) :
    (27 / 256 : ℝ) - p ^ 3 * (1 - p) =
      (p - 3 / 4) ^ 2 * (p ^ 2 + p / 2 + 3 / 16) := by
  ring

/-- This scalar inequality is valid for every real p; source admission is separate. -/
theorem cubic_product_le (p : ℝ) : p ^ 3 * (1 - p) ≤ (27 / 256 : ℝ) := by
  have hquad : 0 ≤ p ^ 2 + p / 2 + (3 / 16 : ℝ) := by
    nlinarith [sq_nonneg (p + (1 / 4 : ℝ))]
  have hprod := mul_nonneg (sq_nonneg (p - (3 / 4 : ℝ))) hquad
  rw [← quartic_gap_identity p] at hprod
  linarith

theorem drop_v_le (p q u v : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hv : 0 ≤ v) (hvu : v ≤ u) :
    cellT p q u 0 ≤ cellT p q u v := by
  have hlast : 0 ≤ v ^ 2 + 3 * q * (2 * u - v) := by
    have htwo : 0 ≤ 2 * u - v := by linarith
    exact add_nonneg (sq_nonneg v)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hq) htwo)
  have hprod : 0 ≤ (2 / 3 : ℝ) * p * v *
      (v ^ 2 + 3 * q * (2 * u - v)) := by positivity
  rw [← drop_v_identity p q u v] at hprod
  linarith

theorem push_u_le (p q u : ℝ)
    (hq : 0 ≤ q) (hu : 0 ≤ u) (hup : u ≤ p) :
    cellT p q p 0 ≤ cellT p q u 0 := by
  have hgap : 0 ≤ p - u := sub_nonneg.mpr hup
  have htwo : 0 ≤ 2 * p - u := by linarith
  have hlast : 0 ≤ 2 * p ^ 2 + 2 * p * u - u ^ 2 := by
    nlinarith [sq_nonneg p, mul_nonneg hu htwo]
  have hprod : 0 ≤ (2 / 3 : ℝ) * q * (p - u) *
      (2 * p ^ 2 + 2 * p * u - u ^ 2) := by positivity
  rw [← push_u_identity p q u] at hprod
  linarith

theorem cell_swap (p q u v : ℝ) : cellT p q u v = cellT q p v u := by
  unfold cellT
  ring

theorem boundary_identity (p q : ℝ) :
    cellT p q p 0 = -(4 / 3 : ℝ) * p ^ 3 * q := by
  unfold cellT
  ring

/-- The full scalar routing/coalescence cube, including all boundary points. -/
theorem complete_cube_cell_lower (p q u v : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hsum : p + q = 1)
    (hu : 0 ≤ u) (hup : u ≤ p) (hv : 0 ≤ v) (hvq : v ≤ q) :
    -(9 / 64 : ℝ) ≤ cellT p q u v := by
  rcases le_total v u with hvu | huv
  · have hqeq : q = 1 - p := by linarith
    have hpoly : p ^ 3 * q ≤ (27 / 256 : ℝ) := by
      rw [hqeq]
      exact cubic_product_le p
    calc
      -(9 / 64 : ℝ) ≤ cellT p q p 0 := by
        rw [boundary_identity]
        nlinarith
      _ ≤ cellT p q u 0 := push_u_le p q u hq hu hup
      _ ≤ cellT p q u v := drop_v_le p q u v hp hq hv hvu
  · have hpeq : p = 1 - q := by linarith
    have hpoly : q ^ 3 * p ≤ (27 / 256 : ℝ) := by
      rw [hpeq]
      exact cubic_product_le q
    calc
      -(9 / 64 : ℝ) ≤ cellT q p q 0 := by
        rw [boundary_identity]
        nlinarith
      _ ≤ cellT q p v 0 := push_u_le q p v hp hv hvq
      _ ≤ cellT q p v u := drop_v_le q p v u hq hp hu huv
      _ = cellT p q u v := (cell_swap p q u v).symm

theorem corner_contrast :
    cellT (3 / 4) (1 / 4) (3 / 4) 0 = -(9 / 64 : ℝ) := by
  norm_num [cellT]

theorem constant_residual_budget (b t c e : ℝ)
    (hb : (4 / 27 : ℝ) ≤ b) (ht : -(9 / 64 : ℝ) ≤ t)
    (heq : e = t + b * (1 - c)) :
    (13 / 256 : ℝ) * b ≤ e + c * b := by
  nlinarith

theorem pow_unit_interval (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    0 ≤ a ^ k ∧ a ^ k ≤ 1 := by
  constructor
  · exact pow_nonneg ha k
  · induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact le_trans (mul_le_mul_of_nonneg_right ih ha) (by simpa using ha1)

/-- No upper bound on G is assumed; positive tails are retained. -/
theorem discounted_step (b a c e G : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hbudget : a * b ≤ e + c * b) (htail : b * a ^ k ≤ G) :
    b * a ^ (k + 1) ≤ e + c * G := by
  obtain ⟨hak, hak1⟩ := pow_unit_interval a ha ha1 k
  have hscale : a ^ k * e ≤ e := by
    simpa using mul_le_mul_of_nonneg_right hak1 he
  have htailmul := mul_le_mul_of_nonneg_left htail hc
  calc
    b * a ^ (k + 1) = a ^ k * (a * b) := by rw [pow_succ]; ring
    _ ≤ a ^ k * (e + c * b) := mul_le_mul_of_nonneg_left hbudget hak
    _ ≤ e + c * G := by nlinarith

/-- An ordinary passage consumes no hybrid count in this scalar recurrence. -/
theorem ordinary_step (b a c G : ℝ) (k : ℕ)
    (hb : 0 ≤ b) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (htail : b * a ^ k ≤ G) :
    b * a ^ k ≤ b * (1 - c) + c * G := by
  have hbase : b * a ^ k ≤ b := by
    simpa using mul_le_mul_of_nonneg_left (pow_unit_interval a ha ha1 k).2 hb
  have hgap := mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hbase)
  have htailmul := mul_le_mul_of_nonneg_left htail hc
  nlinarith

def discountGap (b : ℝ) (c e : ℕ → ℝ) : ℕ → ℝ
  | 0 => b
  | k + 1 => e k + c k * discountGap b c e k

/-- Abstract finite induction; the source must separately prove each row's premises. -/
theorem finite_discounted_lower (b a : ℝ) (c e : ℕ → ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hc : ∀ k, 0 ≤ c k) (he : ∀ k, 0 ≤ e k)
    (hbudget : ∀ k, a * b ≤ e k + c k * b) (n : ℕ) :
    b * a ^ n ≤ discountGap b c e n := by
  induction n with
  | zero => simp [discountGap]
  | succ n ih =>
    simpa only [discountGap] using
      discounted_step b a (c n) (e n) (discountGap b c e n) n
        ha ha1 (hc n) (he n) (hbudget n) ih

end CloudG3.HybridSizeCore
