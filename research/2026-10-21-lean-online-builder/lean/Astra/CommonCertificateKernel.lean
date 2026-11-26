import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum.Ineq

/-!
Exact semantic kernel for the executable rational certificate slice.

This new component proves the mathematical weighted-square and finite-support
steps. It is not the unavailable physical representative provider, and does not
claim a refinement proof of Python/Rust parsing, arithmetic or source admission.
The selected1613 providers remain authoritative for their stronger actual-source
and sparse positive-root cardinality statements.
-/

namespace Astra.CommonCertificateKernel

open scoped BigOperators

def evalPolynomial : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: rest, x => a + x * evalPolynomial rest x

structure SquareTerm where
  weight : ℝ
  left : Bool
  right : Bool
  square : List ℝ

def SquareTerm.eval (t : SquareTerm) (x : ℝ) : ℝ :=
  t.weight * (if t.left then x else 1) * (if t.right then 1-x else 1) *
    (evalPolynomial t.square x)^2

theorem squareTerm_nonnegative (t : SquareTerm) (hw : 0 ≤ t.weight)
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ t.eval x := by
  unfold SquareTerm.eval
  apply mul_nonneg
  · apply mul_nonneg
    · exact mul_nonneg hw (by split; exact hx; exact zero_le_one)
    · split
      · exact sub_nonneg.mpr hx1
      · exact zero_le_one
  · exact sq_nonneg _

theorem square_identity_nonnegative {T : Type*} [Fintype T]
    (terms : T → SquareTerm) (hw : ∀ t, 0 ≤ (terms t).weight)
    (p : ℝ → ℝ) (identity : ∀ x, p x = ∑ t, (terms t).eval x)
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ p x := by
  rw [identity]
  exact Finset.sum_nonneg (fun t _ => squareTerm_nonnegative (terms t) (hw t) x hx hx1)

/-- One supported atom is forced to an exact root. Zero mass atoms need no
extra observation and are not incorrectly constrained by zero expectation. -/
theorem supported_atom_is_root {A : Type*} [Fintype A]
    (weight value : A → ℝ) (p : ℝ → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hp : ∀ a, 0 ≤ p (value a))
    (hz : ∑ a, weight a * p (value a) = 0)
    (a : A) (ha : 0 < weight a) : p (value a) = 0 := by
  have hsum := (Finset.sum_eq_zero_iff_of_nonneg
    (fun b (_ : b ∈ (Finset.univ : Finset A)) => mul_nonneg (hw b) (hp b))).mp hz
  have hproduct := hsum a (Finset.mem_univ a)
  exact (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt ha)

/-- The complete joint configuration is retained. Independence of its internal
coordinates is not an input. Every bank of every positive-mass configuration
is constrained by the same supplied certificate. -/
theorem joint_supported_bank_is_root {C B T : Type*}
    [Fintype C] [Fintype B] [Fintype T]
    (configWeight : C → ℝ) (bankWeight : B → ℝ) (value : C × B → ℝ)
    (hc : ∀ c, 0 ≤ configWeight c) (hb : ∀ b, 0 < bankWeight b)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (terms : T → SquareTerm) (ht : ∀ t, 0 ≤ (terms t).weight)
    (p : ℝ → ℝ) (identity : ∀ x, p x = ∑ t, (terms t).eval x)
    (hz : ∑ a : C × B, (configWeight a.1 * bankWeight a.2) * p (value a) = 0)
    (c : C) (hpositive : 0 < configWeight c) (b : B) :
    p (value (c,b)) = 0 ∧ value (c,b) ∈ Set.Ioc (0 : ℝ) 1 := by
  refine ⟨supported_atom_is_root _ value p ?_ ?_ hz (c,b) ?_, hv (c,b)⟩
  · intro a
    exact mul_nonneg (hc a.1) (hb a.2).le
  · intro a
    exact square_identity_nonnegative terms ht p identity _ (hv a).1.le (hv a).2
  · exact mul_pos hpositive (hb b)

/-- The deterministic generator uses only the supplied first and cubic moments.
This is a bounded sufficient acquisition rule, not universal acquisition. -/
theorem singleton_generator_identity (a x : ℝ) :
    2*a^3 - 3*a^2*x + x^3 = 2*a*(x-a)^2 + x*(x-a)^2 := by
  ring

theorem singleton_generator_nonnegative (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    0 ≤ 2*a^3 - 3*a^2*x + x^3 := by
  rw [singleton_generator_identity]
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha) (sq_nonneg _))
    (mul_nonneg hx (sq_nonneg _))

theorem singleton_generator_annihilates (a : ℝ) :
    (2*a^3)*1 + (-3*a^2)*a + 1*a^3 = 0 := by
  ring

theorem singleton_generator_nonzero (a : ℝ) (ha : 0 < a) :
    (fun x : ℝ => 2*a^3 - 3*a^2*x + x^3) ≠ (fun _ => 0) := by
  intro h
  have hzero := congrFun h 0
  have hpositive : 0 < 2*a^3 := mul_pos (by norm_num) (pow_pos ha 3)
  simp only [mul_zero, sub_zero, zero_pow (by decide : 3 ≠ 0), add_zero] at hzero
  exact (ne_of_gt hpositive) hzero

#print axioms squareTerm_nonnegative
#print axioms square_identity_nonnegative
#print axioms supported_atom_is_root
#print axioms joint_supported_bank_is_root
#print axioms singleton_generator_identity
#print axioms singleton_generator_nonnegative
#print axioms singleton_generator_annihilates
#print axioms singleton_generator_nonzero

end Astra.CommonCertificateKernel
