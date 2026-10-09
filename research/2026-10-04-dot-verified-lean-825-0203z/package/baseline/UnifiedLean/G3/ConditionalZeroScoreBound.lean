import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Conditional consumer of the reviewed whole-fibre zero-score certificate.
The rational computation is executable. Actual source reduction, score production,
whole-fibre coverage and the source pair law are provider obligations, not results
about the original source grammar. No certificate producer or general G3 decision
algorithm is asserted here. In particular the COMMON coverage obstruction does
not invalidate a supplied restricted equal-arm INDEPENDENT/BOTH certificate.
-/

namespace UnifiedLean.G3.ConditionalZeroScore

open scoped BigOperators

/-- Exactly rational numeric inputs; no positive lower coin bound. -/
structure NumericData where
  b : ℚ
  epsilon : ℚ
  sigma : ℚ
  M : ℚ
  b_pos : 0 < b
  epsilon_pos : 0 < epsilon
  sigma_pos : 0 < sigma
  M_nonneg : 0 ≤ M

def NumericData.delta (d : NumericData) : ℚ :=
  min d.epsilon (d.sigma / (2 * (d.M + 1)))

def NumericData.loss (d : NumericData) : ℚ := d.delta / (2 * (1 + d.delta))

def NumericData.independentBound (d : NumericData) : ℕ :=
  Nat.ceil (2 * (1 + d.delta) / (d.b * d.delta))

theorem delta_pos (d : NumericData) : 0 < d.delta := by
  apply lt_min_iff.mpr
  refine ⟨d.epsilon_pos, ?_⟩
  exact div_pos d.sigma_pos (by linarith [d.M_nonneg])

theorem delta_le_epsilon (d : NumericData) : d.delta ≤ d.epsilon := min_le_left _ _

theorem modulus_margin (d : NumericData) : d.M * d.delta ≤ d.sigma / 2 := by
  have h := min_le_right d.epsilon (d.sigma / (2 * (d.M + 1)))
  have hden : 0 < 2 * (d.M + 1) := by linarith [d.M_nonneg]
  have hscaled : d.delta * (2 * (d.M + 1)) ≤ d.sigma :=
    (le_div_iff₀ hden).mp h
  nlinarith [delta_pos d]

theorem loss_pos (d : NumericData) : 0 < d.loss :=
  div_pos (delta_pos d) (by linarith [delta_pos d])

theorem loss_lt_half (d : NumericData) : d.loss < 1 / 2 := by
  unfold NumericData.loss
  apply (div_lt_iff₀ (by linarith [delta_pos d])).mpr
  linarith

theorem bound_reciprocal (d : NumericData) :
    1 / (d.b * d.loss) = 2 * (1 + d.delta) / (d.b * d.delta) := by
  unfold NumericData.loss
  field_simp

theorem rational_count_ceiling (d : NumericData) (n : ℕ)
    (h : (n : ℚ) ≤ 2 * (1 + d.delta) / (d.b * d.delta)) :
    n ≤ d.independentBound := by
  exact_mod_cast h.trans (Nat.le_ceil _)

theorem expression_le_ceiling (d : NumericData) :
    2 * (1 + d.delta) / (d.b * d.delta) ≤ (d.independentBound : ℚ) :=
  Nat.le_ceil _

theorem ceiling_le_iff (d : NumericData) (n : ℕ) :
    d.independentBound ≤ n ↔ 2 * (1 + d.delta) / (d.b * d.delta) ≤ (n : ℚ) :=
  Nat.ceil_le

theorem zero_length (d : NumericData) : 0 ≤ d.independentBound := Nat.zero_le _

/-- Finite nonnegative cells cannot cancel under positive slot weights. -/
theorem cells_zero_of_weighted_endpoint_zero
    {S : Type*} [Fintype S] (L : S → ℕ)
    (weight : S → ℝ) (score : (j : S) → Fin (L j) → ℝ)
    (hw : ∀ j, 0 < weight j) (hn : ∀ j i, 0 ≤ score j i)
    (hz : ∑ j, weight j * ∑ i, score j i = 0) :
    ∀ j i, score j i = 0 := by
  have hs : ∀ j, 0 ≤ ∑ i, score j i := fun j => Finset.sum_nonneg (by
    intro i hi
    exact hn j i)
  have hall : ∀ j, weight j * ∑ i, score j i = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (by
      intro j hj
      exact mul_nonneg (hw j).le (hs j))).mp hz
    exact fun j => h j (Finset.mem_univ j)
  intro j i
  have hslot : ∑ i, score j i = 0 :=
    (mul_eq_zero.mp (hall j)).resolve_left (ne_of_gt (hw j))
  exact (Finset.sum_eq_zero_iff_of_nonneg (by
    intro k hk
    exact hn j k)).mp hslot i (Finset.mem_univ i)

/-- Only arithmetic consequences of the uniform weak-cell modulus are used. -/
theorem weak_cell_score_positive (d : NumericData) {p t G G0 F : ℝ}
    (hp : 0 < p) (ht : 0 < t) (htd : t ≤ (d.delta : ℝ))
    (h0 : (d.sigma : ℝ) ≤ G0)
    (hmod : |G - G0| ≤ (d.M : ℝ) * t)
    (hF : F = p * t * G) : 0 < F := by
  have hM : (0 : ℝ) ≤ d.M := by exact_mod_cast d.M_nonneg
  have hmargin : (d.M : ℝ) * (d.delta : ℝ) ≤ (d.sigma : ℝ) / 2 := by
    exact_mod_cast modulus_margin d
  have hs : (0 : ℝ) < d.sigma := by exact_mod_cast d.sigma_pos
  have hosc := (abs_le.mp hmod).1
  have hmt := mul_le_mul_of_nonneg_left htd hM
  have hG : 0 < G := by linarith
  rw [hF]
  exact mul_pos (mul_pos hp ht) hG

theorem zero_score_duration_gap (d : NumericData) {p t G G0 F : ℝ}
    (hp : 0 < p) (ht : 0 < t)
    (h0 : (d.sigma : ℝ) ≤ G0)
    (hmod : t ≤ (d.epsilon : ℝ) → |G - G0| ≤ (d.M : ℝ) * t)
    (hF : F = p * t * G) (hz : F = 0) : (d.delta : ℝ) < t := by
  by_contra hn
  have htd : t ≤ (d.delta : ℝ) := le_of_not_gt hn
  have heps : (d.delta : ℝ) ≤ (d.epsilon : ℝ) := by
    exact_mod_cast delta_le_epsilon d
  have := weak_cell_score_positive d hp ht htd h0 (hmod (htd.trans heps)) hF
  linarith

/-- Arithmetic part of the actual equal-arm factor estimate.
`(1+delta)*q ≤ 1` is the separately supplied exp-duration estimate.
-/
theorem equal_arm_pair_loss (d : NumericData) {p q beta : ℝ}
    (hp : p ≤ 1 / 4) (hq : q ≤ 1)
    (hqdelta : (1 + (d.delta : ℝ)) * q ≤ 1)
    (hbeta : beta = q + 2 * p * (1 - q)) :
    beta ≤ 1 - (d.loss : ℝ) := by
  have hd : (0 : ℝ) < d.delta := by exact_mod_cast delta_pos d
  have hmid : beta ≤ (1 + q) / 2 := by
    rw [hbeta]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq)]
  have hden : (0 : ℝ) < 2 * (1 + (d.delta : ℝ)) := by linarith
  have hloss : (d.loss : ℝ) = (d.delta : ℝ) / (2 * (1 + (d.delta : ℝ))) := by
    simp only [NumericData.loss, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_add, Rat.cast_one]
  rw [hloss]
  apply (mul_le_mul_iff_right₀ hden).mp
  have hscaled := mul_le_mul_of_nonneg_right hmid hden.le
  have hid : (1 - (d.delta : ℝ) / (2 * (1 + (d.delta : ℝ)))) *
      (2 * (1 + (d.delta : ℝ))) = 2 + (d.delta : ℝ) := by
    field_simp <;> ring
  nlinarith

/-- A purely algebraic replacement for the hand proof's logarithmic budget. -/
theorem geometric_budget (a : ℝ) (_ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    (1 - a) ^ n * (1 + (n : ℝ) * a) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hstep : (1 - a) * (1 + ((n : ℝ) + 1) * a) ≤ 1 + (n : ℝ) * a := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1) (sq_nonneg a)]
    have hpow : 0 ≤ (1 - a) ^ n := pow_nonneg (by linarith) _
    have h := mul_le_mul_of_nonneg_left hstep hpow
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem independent_product_count (d : NumericData) (L : ℕ)
    (beta : Fin L → ℝ) (s Z : ℝ)
    (hn : ∀ i, 0 ≤ beta i) (hl : ∀ i, beta i ≤ 1 - (d.loss : ℝ))
    (hZ : Z ≤ 1) (hs : s = Z * ∏ i, beta i) (hb : (d.b : ℝ) ≤ s) :
    L ≤ d.independentBound := by
  have ha : (0 : ℝ) < d.loss := by exact_mod_cast loss_pos d
  have ha1 : (d.loss : ℝ) ≤ 1 := by
    have hhalf : (d.loss : ℝ) < 1 / 2 := by
      have hcast : (d.loss : ℝ) < ((1 / 2 : ℚ) : ℝ) := by
        exact_mod_cast loss_lt_half d
      norm_num at hcast ⊢
      exact hcast
    linarith
  have hp : 0 ≤ ∏ i, beta i := Finset.prod_nonneg (by
    intro i hi
    exact hn i)
  have hprod : (∏ i, beta i) ≤ (1 - (d.loss : ℝ)) ^ L := by
    have h := Finset.prod_le_prod (s := Finset.univ) (f := beta)
      (g := fun _ => 1 - (d.loss : ℝ)) (by intro i hi; exact hn i)
      (by intro i hi; exact hl i)
    simpa using h
  have hsp : s ≤ ∏ i, beta i := by rw [hs]; nlinarith
  have hbs : (d.b : ℝ) ≤ (1 - (d.loss : ℝ)) ^ L := hb.trans (hsp.trans hprod)
  have hbudget := geometric_budget (d.loss : ℝ) ha.le ha1 L
  have hf : (0 : ℝ) ≤ 1 + (L : ℝ) * (d.loss : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hbs hf
  have hbpos : (0 : ℝ) < d.b := by exact_mod_cast d.b_pos
  have hcount : (L : ℝ) ≤ 1 / ((d.b : ℝ) * (d.loss : ℝ)) := by
    apply (le_div_iff₀ (mul_pos hbpos ha)).mpr
    nlinarith
  have hrat : (L : ℚ) ≤ 1 / (d.b * d.loss) := by exact_mod_cast hcount
  rw [bound_reciprocal] at hrat
  exact rational_count_ceiling d L hrat

end UnifiedLean.G3.ConditionalZeroScore
