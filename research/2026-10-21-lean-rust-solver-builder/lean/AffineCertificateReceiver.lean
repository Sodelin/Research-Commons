import G6RationalAffineWitness

/-! Source candidate for the existing native AFFINE certificates.
Reuses the original Row and rational-witness theorem; no solver is implemented.
The finite rational matrix is supplied. Native parsing, source-chart admission
and all-size source exclusion are separate obligations. Not checked yet. -/

namespace Astra.NativeAffineCertificates

open scoped BigOperators
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness

variable {n m : ℕ}

/-- Ordered original rows may repeat; witness checking uses the same finite set. -/
def rowsSet (R : Fin m → Row n) : Finset (Row n) :=
  Finset.univ.image R

/-- Reuse the existing positive checker and rational-to-real theorem. -/
theorem checked_witness_real (R : Fin m → Row n) (q : Fin n → ℚ)
    (h : checkRationalWitness (rowsSet R) q = true) :
    ∀ a, (R a).Holds (fun j => (q j : ℝ)) := by
  have hr := rationalWitness_real (rowsSet R) q
    ((checkRationalWitness_correct (rowsSet R) q).mp h)
  intro a
  exact hr (R a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

/-- Exact finite predicate used by the existing Rust check_exclusion:
a zero multiplier on a strict row cannot supply a strict contradiction. -/
def checkFarkas (R : Fin m → Row n) (w : Fin m → ℚ) : Bool :=
  decide ((∀ a, 0 ≤ w a) ∧
    (∀ j, (∑ a, w a * (R a).coeff j) = 0) ∧
    ((∑ a, w a * (R a).bound) < 0 ∨
      ((∑ a, w a * (R a).bound) = 0 ∧
        ∃ a, 0 < w a ∧ (R a).strict = true)))

theorem weighted_eval_zero (R : Fin m → Row n) (w : Fin m → ℚ)
    (hc : ∀ j, (∑ a, w a * (R a).coeff j) = 0)
    (x : Fin n → ℝ) :
    (∑ a, (w a : ℝ) * (R a).eval x) = 0 := by
  have hcR (j : Fin n) :
      (∑ a, (w a : ℝ) * ((R a).coeff j : ℝ)) = 0 := by
    exact_mod_cast hc j
  calc
    (∑ a, (w a : ℝ) * (R a).eval x) =
        ∑ a, ∑ j, ((w a : ℝ) * ((R a).coeff j : ℝ)) * x j := by
      simp only [Row.eval, Finset.mul_sum, mul_assoc]
    _ = ∑ j, ∑ a, ((w a : ℝ) * ((R a).coeff j : ℝ)) * x j := Finset.sum_comm
    _ = ∑ j, (∑ a, (w a : ℝ) * ((R a).coeff j : ℝ)) * x j := by
      simp only [Finset.sum_mul]
    _ = 0 := by simp only [hcR, zero_mul, Finset.sum_const_zero]

/-- Soundness concerns this exact finite matrix over the reals. It needs no
claim about the native elimination trajectory or the origin of the rows. -/
theorem farkas_infeasible (R : Fin m → Row n) (w : Fin m → ℚ)
    (hw : ∀ a, 0 ≤ w a)
    (hc : ∀ j, (∑ a, w a * (R a).coeff j) = 0)
    (hb : (∑ a, w a * (R a).bound) < 0 ∨
      ((∑ a, w a * (R a).bound) = 0 ∧
        ∃ a, 0 < w a ∧ (R a).strict = true)) :
    ¬ ∃ x : Fin n → ℝ, ∀ a, (R a).Holds x := by
  rintro ⟨x, hx⟩
  have hwR (a : Fin m) : 0 ≤ (w a : ℝ) := by exact_mod_cast hw a
  have hle (a : Fin m) :
      (w a : ℝ) * (R a).eval x ≤ (w a : ℝ) * ((R a).bound : ℝ) :=
    mul_le_mul_of_nonneg_left (rel_le (hx a)) (hwR a)
  have hz := weighted_eval_zero R w hc x
  rcases hb with hneg | ⟨heq, a, hwa, hsa⟩
  · have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin m))) => hle a)
    have hbR : (∑ a, (w a : ℝ) * ((R a).bound : ℝ)) < 0 := by
      exact_mod_cast hneg
    linarith
  · have ha : (R a).eval x < ((R a).bound : ℝ) := by
      simpa [Row.Holds, UnifiedLean.G6.StrictAffineElimination.Rel, hsa] using hx a
    have hwaR : 0 < (w a : ℝ) := by exact_mod_cast hwa
    have hlt := mul_lt_mul_of_pos_left ha hwaR
    have hsum : (∑ a, (w a : ℝ) * (R a).eval x) <
        ∑ a, (w a : ℝ) * ((R a).bound : ℝ) :=
      Finset.sum_lt_sum (fun a _ => hle a) ⟨a, Finset.mem_univ a, hlt⟩
    have hbR : (∑ a, (w a : ℝ) * ((R a).bound : ℝ)) = 0 := by
      exact_mod_cast heq
    linarith

theorem checked_farkas_infeasible (R : Fin m → Row n) (w : Fin m → ℚ)
    (h : checkFarkas R w = true) :
    ¬ ∃ x : Fin n → ℝ, ∀ a, (R a).Holds x := by
  simp only [checkFarkas, decide_eq_true_eq] at h
  exact farkas_infeasible R w h.1 h.2.1 h.2.2

end Astra.NativeAffineCertificates
