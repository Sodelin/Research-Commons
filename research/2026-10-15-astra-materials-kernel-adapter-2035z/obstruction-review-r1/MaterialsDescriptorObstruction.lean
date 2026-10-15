import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Source-only adapter for a descriptor-fibre obstruction

UNCOMPILED source proposal. No elaboration, kernel or axiom output is supplied.
The exact materials witness and homometric construction are inherited from the
materials transfer/counterexample owner. The finite-state obstruction principle
is classical lumpability, in the accepted G2 row orientation K * P = P * B.

This file proves the row-certificate implication and the stated 12-period field
facts as Lean source. It does NOT instantiate the full periodic 12^3
configuration/offset/Fourier/mixed-kernel definitions. That physical-source
binding remains explicit in the accompanying independent hand review.
No statement about block powers or scheduled observations is inferred.
-/

namespace Astra.MaterialsDescriptorObstruction

open scoped BigOperators

section FibreCertificate

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

def descriptorProjection (D : X → Y) : Matrix X Y ℝ :=
  fun s y => if D s = y then 1 else 0

def fibreMass (K : Matrix X X ℝ) (D : X → Y) (s : X) (y : Y) : ℝ :=
  ∑ t : X, if D t = y then K s t else 0

theorem kernel_mul_projection (K : Matrix X X ℝ) (D : X → Y)
    (s : X) (y : Y) :
    (K * descriptorProjection D) s y = fibreMass K D s y := by
  classical
  simp [Matrix.mul_apply, descriptorProjection, fibreMass, mul_ite]

theorem projection_mul (B : Matrix Y Y ℝ) (D : X → Y)
    (s : X) (y : Y) :
    (descriptorProjection D * B) s y = B (D s) y := by
  classical
  simp [Matrix.mul_apply, descriptorProjection, ite_mul]

theorem fibreMass_eq_of_intertwining (K : Matrix X X ℝ) (D : X → Y)
    (B : Matrix Y Y ℝ)
    (h : K * descriptorProjection D = descriptorProjection D * B)
    {a b : X} (hab : D a = D b) (y : Y) :
    fibreMass K D a y = fibreMass K D b y := by
  have ha : fibreMass K D a y = B (D a) y := by
    rw [← kernel_mul_projection K D a y, h, projection_mul]
  have hb : fibreMass K D b y = B (D b) y := by
    rw [← kernel_mul_projection K D b y, h, projection_mul]
  rw [ha, hb, hab]

theorem fibreMass_zero_of_pointwise (K : Matrix X X ℝ) (D : X → Y)
    (a : X) (y : Y) (hz : ∀ t, D t = y → K a t = 0) :
    fibreMass K D a y = 0 := by
  classical
  unfold fibreMass
  apply Finset.sum_eq_zero
  intro t _ht
  by_cases h : D t = y
  · simp [h, hz t h]
  · simp [h]

theorem fibreMass_pos_of_entry (K : Matrix X X ℝ) (D : X → Y)
    (b z : X) (hnonneg : ∀ t, 0 ≤ K b t) (hpos : 0 < K b z) :
    0 < fibreMass K D b (D z) := by
  classical
  have hle : (if D z = D z then K b z else 0) ≤
      ∑ t : X, if D t = D z then K b t else 0 := by
    apply Finset.single_le_sum
    · intro t _ht
      by_cases h : D t = D z
      · simpa [h] using hnonneg t
      · simp [h]
    · exact Finset.mem_univ z
  have hle' : K b z ≤ fibreMass K D b (D z) := by
    simpa [fibreMass] using hle
  exact lt_of_lt_of_le hpos hle'

/-- Complete zero-fibre evidence and one positive entry suffice. The conclusion
excludes every real reduced matrix, hence also every stochastic one. -/
theorem no_quotient_of_zero_fibre_and_positive_entry
    (K : Matrix X X ℝ) (D : X → Y) (a b z : X)
    (hab : D a = D b)
    (hz : ∀ t, D t = D z → K a t = 0)
    (hnonneg : ∀ t, 0 ≤ K b t) (hpos : 0 < K b z) :
    ¬ ∃ B : Matrix Y Y ℝ,
      K * descriptorProjection D = descriptorProjection D * B := by
  have hzero := fibreMass_zero_of_pointwise K D a (D z) hz
  have hpositive := fibreMass_pos_of_entry K D b z hnonneg hpos
  rintro ⟨B, hB⟩
  have heq := fibreMass_eq_of_intertwining K D B hB hab (D z)
  rw [hzero] at heq
  exact (ne_of_gt hpositive) heq.symm

/-- Every finite positive temperature is retained. This is a one-step result;
the source contains no inference about powers K^n or coarsely sampled words. -/
theorem no_quotient_at_every_positive_temperature
    (K : ℝ → Matrix X X ℝ) (D : X → Y) (a b z : X)
    (hab : D a = D b)
    (hz : ∀ T, 0 < T → ∀ t, D t = D z → K T a t = 0)
    (hnonneg : ∀ T, 0 < T → ∀ t, 0 ≤ K T b t)
    (hpos : ∀ T, 0 < T → 0 < K T b z) :
    ∀ T, 0 < T →
      ¬ ∃ B : Matrix Y Y ℝ,
        K T * descriptorProjection D = descriptorProjection D * B := by
  intro T hT
  exact no_quotient_of_zero_fibre_and_positive_entry
    (K T) D a b z hab (hz T hT) (hnonneg T hT) (hpos T hT)

end FibreCertificate

section PeriodTwelveFields

/-- Integer stripe values; offsets are reduced modulo 12. -/
def stripeA (u : ℕ) : ℤ :=
  if u % 12 = 0 ∨ u % 12 = 1 ∨ u % 12 = 4 ∨ u % 12 = 6
  then 1 else -1

def stripeB (u : ℕ) : ℤ :=
  if u % 12 = 0 ∨ u % 12 = 1 ∨ u % 12 = 3 ∨ u % 12 = 7
  then 1 else -1

def fieldOne (a : ℕ → ℤ) (u : Fin 12) : ℤ :=
  2 + a u.val * (a (u.val + 11) + a (u.val + 1))

def fieldThree (a : ℕ → ℤ) (u : Fin 12) : ℤ :=
  2 + a u.val * (a (u.val + 10) + a (u.val + 2))

theorem fieldsA_nonnegative (u : Fin 12) :
    0 ≤ fieldOne stripeA u ∧ 0 ≤ fieldThree stripeA u := by
  fin_cases u <;> norm_num [fieldOne, fieldThree, stripeA]

theorem fieldsA_not_joint_zero (u : Fin 12) :
    ¬ (fieldOne stripeA u = 0 ∧ fieldThree stripeA u = 0) := by
  fin_cases u <;> norm_num [fieldOne, fieldThree, stripeA]

theorem fieldsB_seven_zero :
    fieldOne stripeB (7 : Fin 12) = 0 ∧
      fieldThree stripeB (7 : Fin 12) = 0 := by
  norm_num [fieldOne, fieldThree, stripeB]

/-- Given the actual reciprocal-graph swap-delta formula, the A field facts
exclude a swap leaving both retained coordinates unchanged. The theorem does
not itself establish that formula for a newly defined physical graph. -/
theorem A_swap_deltas_not_both_zero (u v : Fin 12) (mOne mThree : ℤ)
    (hmOne : 0 ≤ mOne) (hmThree : 0 ≤ mThree) :
    ¬ ((-2 * fieldOne stripeA u - 2 * fieldOne stripeA v - 4 * mOne = 0) ∧
       (-2 * fieldThree stripeA u - 2 * fieldThree stripeA v - 4 * mThree = 0)) := by
  intro h
  have huOne := (fieldsA_nonnegative u).1
  have hvOne := (fieldsA_nonnegative v).1
  have huThree := (fieldsA_nonnegative u).2
  have hvThree := (fieldsA_nonnegative v).2
  have hOne : fieldOne stripeA u = 0 := by linarith [h.1]
  have hThree : fieldThree stripeA u = 0 := by linarith [h.2]
  exact fieldsA_not_joint_zero u ⟨hOne, hThree⟩

end PeriodTwelveFields

section FixedFitPositivity

def fittedKB : ℝ := 6209443018827293 / 72057594037927936

/-- Exact binary64 rational lifts: 4 V_ap + 16 V_ip2 - 8 V_c2; V_ip4=0. -/
def fittedVerticalMoveCost : ℝ :=
  4 * (3254063363298789 / 140737488355328) +
  16 * (4814043477715793 / 1125899906842624) -
  8 * (4160251384624691 / 2251799813685248)

theorem fittedKB_pos : 0 < fittedKB := by
  norm_num [fittedKB]

theorem fittedVerticalMoveCost_exact :
    fittedVerticalMoveCost = 41128429432628793 / 281474976710656 := by
  norm_num [fittedVerticalMoveCost]

theorem fittedVerticalMoveCost_pos : 0 < fittedVerticalMoveCost := by
  rw [fittedVerticalMoveCost_exact]
  norm_num

def idealAcceptance (d kb T : ℝ) : ℝ :=
  if d ≤ 0 then 1 else Real.exp (-d / (kb * T))

/-- Pure algebraic positivity. Actual source use separately requires kb,T>0. -/
theorem idealAcceptance_pos (d kb T : ℝ) :
    0 < idealAcceptance d kb T := by
  by_cases h : d ≤ 0
  · simp [idealAcceptance, h]
  · simpa [idealAcceptance, h] using Real.exp_pos (-d / (kb * T))

theorem named_mixture_lower_bound_pos (T : ℝ) :
    0 < idealAcceptance fittedVerticalMoveCost fittedKB T / (1728 : ℝ)^2 := by
  exact div_pos (idealAcceptance_pos _ _ _) (by norm_num)

end FixedFitPositivity

-- Requests for a future admitted audit, not executed audit output.
#check no_quotient_at_every_positive_temperature
#print axioms no_quotient_of_zero_fibre_and_positive_entry
#print axioms no_quotient_at_every_positive_temperature
#print axioms A_swap_deltas_not_both_zero
#print axioms fittedVerticalMoveCost_exact

end Astra.MaterialsDescriptorObstruction
