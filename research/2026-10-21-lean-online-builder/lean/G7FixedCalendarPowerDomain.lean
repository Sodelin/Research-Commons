import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A mathematical receiver for the correlated positive-power domain.
It does not identify native parser values, targets, row registries or readouts. -/

namespace Astra.FixedCalendarPowerDomain

noncomputable def rate (x duration : ℝ) : ℝ := -Real.log x / duration

theorem rate_pos {x duration : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hD : 0 < duration) : 0 < rate x duration := by
  exact div_pos (neg_pos.mpr (Real.log_neg hx hx1)) hD

theorem rate_survival {x duration : ℝ} (hx : 0 < x) (hD : 0 < duration) :
    Real.exp (-(rate x duration) * duration) = x := by
  have h : -(rate x duration) * duration = Real.log x := by
    unfold rate
    field_simp [hD.ne']
  rw [h, Real.exp_log hx]

theorem power_eq_iff_log_eq {x z : ℝ} (hx : 0 < x) (hz : 0 < z)
    (p q : ℕ) : z ^ q = x ^ p ↔
      (q : ℝ) * Real.log z = (p : ℝ) * Real.log x := by
  constructor
  · intro h
    simpa only [Real.log_pow] using congrArg Real.log h
  · intro h
    simpa only [← Real.log_pow, Real.exp_log (pow_pos hz q),
      Real.exp_log (pow_pos hx p)] using congrArg Real.exp h

theorem positive_power_iff_exp {x z d D : ℝ} (hx : 0 < x) (hz : 0 < z)
    (hD : 0 < D) (p q : ℕ) (hq : 0 < q)
    (htime : (q : ℝ) * d = (p : ℝ) * D) :
    z ^ q = x ^ p ↔ z = Real.exp (-(rate x D) * d) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hratio : ((q : ℝ) * d) / D = (p : ℝ) :=
    (div_eq_iff hD.ne').mpr htime
  have hcoef : (q : ℝ) * (-(rate x D) * d) =
      (p : ℝ) * Real.log x := by
    unfold rate
    calc
      (q : ℝ) * (-(-Real.log x / D) * d) =
          (((q : ℝ) * d) / D) * Real.log x := by ring
      _ = (p : ℝ) * Real.log x := by rw [hratio]
  rw [power_eq_iff_log_eq hx hz p q]
  constructor
  · intro h
    have hzlog : Real.log z = -(rate x D) * d := by
      apply mul_left_cancel₀ hq0
      exact h.trans hcoef.symm
    calc
      z = Real.exp (Real.log z) := (Real.exp_log hz).symm
      _ = Real.exp (-(rate x D) * d) := by rw [hzlog]
  · intro h
    rw [h, Real.log_exp]
    exact hcoef

theorem slot_survival_mem {x d D : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hD : 0 < D) (hd : 0 < d) :
    0 < Real.exp (-(rate x D) * d) ∧ Real.exp (-(rate x D) * d) < 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (rate_pos hx hx1 hD)) hd

theorem correlated_slots_exists_unique {Pop Slot : Type*}
    (X duration : Pop → ℝ) (elapsed : Slot → ℝ)
    (p q : Slot → Pop → ℕ)
    (hX : ∀ i, 0 < X i ∧ X i < 1)
    (hD : ∀ i, 0 < duration i) (hd : ∀ j, 0 < elapsed j)
    (hq : ∀ j i, 0 < q j i)
    (htime : ∀ j i, (q j i : ℝ) * elapsed j = (p j i : ℝ) * duration i) :
    ∃! Z : Slot → Pop → ℝ,
      (∀ j i, 0 < Z j i ∧ Z j i < 1) ∧
      (∀ j i, Z j i ^ q j i = X i ^ p j i) := by
  let Z : Slot → Pop → ℝ := fun j i => Real.exp (-(rate (X i) (duration i)) * elapsed j)
  have hZ : ∀ j i, 0 < Z j i ∧ Z j i < 1 := by
    intro j i
    exact slot_survival_mem (hX i).1 (hX i).2 (hD i) (hd j)
  refine ⟨Z, ⟨hZ, ?_⟩, ?_⟩
  · intro j i
    exact (positive_power_iff_exp (hX i).1 (hZ j i).1 (hD i)
      (p j i) (q j i) (hq j i) (htime j i)).mpr rfl
  · intro Z' hZ'
    funext j i
    exact (positive_power_iff_exp (hX i).1 (hZ'.1 j i).1 (hD i)
      (p j i) (q j i) (hq j i) (htime j i)).mp (hZ'.2 j i)

end Astra.FixedCalendarPowerDomain
