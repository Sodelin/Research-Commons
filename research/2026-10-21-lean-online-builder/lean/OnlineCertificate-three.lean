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


/- Exact certificate SHA256: e49c1e3d6bffee594b99574d3364e700e8f25342933fe31add2aa6129729bc6b. Generation is not compilation. -/
namespace Astra.Generated.Certificate_e49c1e3d6bffee594b99574d3364e700e8f25342933fe31add2aa6129729bc6b
open Astra.CommonCertificateKernel
open scoped BigOperators

noncomputable def polynomial (x : ℝ) : ℝ := (((15694924948152899715 : ℝ) / 318782149412549765890048) * (x)^0 + ((-101589877798659355833 : ℝ) / 318782149412549765890048) * (x)^1 + ((175777975580685893075 : ℝ) / 79695537353137441472512) * (x)^3 + ((-5275629367498209825 : ℝ) / 311310692785693130752) * (x)^6 + ((141906319413452685 : ℝ) / 1216057393694113792) * (x)^10 + ((-2372523878540265 : ℝ) / 4750224194117632) * (x)^15 + ((1 : ℝ) / 1) * (x)^21)

theorem nonnegative (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ polynomial x := by
  have h0 := squareTerm_nonnegative ({ weight := ((1743880549794766635 : ℝ) / 311310692785693130752), left := false, right := false, square := [((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h1 := squareTerm_nonnegative ({ weight := ((14289150530472204443 : ℝ) / 311310692785693130752), left := true, right := false, square := [((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h2 := squareTerm_nonnegative ({ weight := ((937312648577727681 : ℝ) / 4864229574776455168), left := false, right := false, square := [((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h3 := squareTerm_nonnegative ({ weight := ((5584047689965234439 : ℝ) / 9728459149552910336), left := true, right := false, square := [((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h4 := squareTerm_nonnegative ({ weight := ((808418472841702755 : ℝ) / 608028696847056896), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h5 := squareTerm_nonnegative ({ weight := ((3131982692780642601 : ℝ) / 1216057393694113792), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h6 := squareTerm_nonnegative ({ weight := ((163176933700717179 : ℝ) / 38001793552941056), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h7 := squareTerm_nonnegative ({ weight := ((118511173301522279 : ℝ) / 19000896776470528), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h8 := squareTerm_nonnegative ({ weight := ((38529113979728325 : ℝ) / 4750224194117632), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h9 := squareTerm_nonnegative ({ weight := ((44934884648424199 : ℝ) / 4750224194117632), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h10 := squareTerm_nonnegative ({ weight := ((2511 : ℝ) / 256), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h11 := squareTerm_nonnegative ({ weight := ((2307 : ℝ) / 256), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h12 := squareTerm_nonnegative ({ weight := ((15 : ℝ) / 2), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h13 := squareTerm_nonnegative ({ weight := ((43 : ℝ) / 8), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h14 := squareTerm_nonnegative ({ weight := ((3 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have h15 := squareTerm_nonnegative ({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm) (by norm_num) x hx hx1
  have hsum : 0 ≤ ((({ weight := ((1743880549794766635 : ℝ) / 311310692785693130752), left := false, right := false, square := [((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((14289150530472204443 : ℝ) / 311310692785693130752), left := true, right := false, square := [((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((937312648577727681 : ℝ) / 4864229574776455168), left := false, right := false, square := [((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((5584047689965234439 : ℝ) / 9728459149552910336), left := true, right := false, square := [((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((808418472841702755 : ℝ) / 608028696847056896), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((3131982692780642601 : ℝ) / 1216057393694113792), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((163176933700717179 : ℝ) / 38001793552941056), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((118511173301522279 : ℝ) / 19000896776470528), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((38529113979728325 : ℝ) / 4750224194117632), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((44934884648424199 : ℝ) / 4750224194117632), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((2511 : ℝ) / 256), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((2307 : ℝ) / 256), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((15 : ℝ) / 2), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((43 : ℝ) / 8), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((3 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15)
  have identity : polynomial x = ((({ weight := ((1743880549794766635 : ℝ) / 311310692785693130752), left := false, right := false, square := [((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((14289150530472204443 : ℝ) / 311310692785693130752), left := true, right := false, square := [((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((937312648577727681 : ℝ) / 4864229574776455168), left := false, right := false, square := [((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((5584047689965234439 : ℝ) / 9728459149552910336), left := true, right := false, square := [((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((808418472841702755 : ℝ) / 608028696847056896), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((3131982692780642601 : ℝ) / 1216057393694113792), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((163176933700717179 : ℝ) / 38001793552941056), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((118511173301522279 : ℝ) / 19000896776470528), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((38529113979728325 : ℝ) / 4750224194117632), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((44934884648424199 : ℝ) / 4750224194117632), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((2511 : ℝ) / 256), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((2307 : ℝ) / 256), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((15 : ℝ) / 2), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((43 : ℝ) / 8), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((3 : ℝ) / 1), left := false, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x + (({ weight := ((1 : ℝ) / 1), left := true, right := false, square := [((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((0 : ℝ) / 1), ((-3 : ℝ) / 32), ((11 : ℝ) / 16), ((-3 : ℝ) / 2), ((1 : ℝ) / 1)] } : SquareTerm)).eval x) := by
    dsimp [polynomial, SquareTerm.eval, evalPolynomial]
    ring
  rw [identity]
  exact hsum

theorem nonzero_value : polynomial 0 ≠ 0 := by
  norm_num [polynomial]

theorem annihilation : (((15694924948152899715 : ℝ) / 318782149412549765890048) * ((1 : ℝ) / 1) + ((-101589877798659355833 : ℝ) / 318782149412549765890048) * ((1 : ℝ) / 2) + ((175777975580685893075 : ℝ) / 79695537353137441472512) * ((3 : ℝ) / 16) + ((-5275629367498209825 : ℝ) / 311310692785693130752) * ((397 : ℝ) / 6144) + ((141906319413452685 : ℝ) / 1216057393694113792) * ((30037 : ℝ) / 1572864) + ((-2372523878540265 : ℝ) / 4750224194117632) * ((1198473 : ℝ) / 268435456) + ((1 : ℝ) / 1) * ((871870863 : ℝ) / 1099511627776)) = 0 := by
  norm_num

theorem finite_supported_bank {A : Type*} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 2))
    (moment2 : ∑ a, weight a * (value a)^3 = ((3 : ℝ) / 16))
    (moment3 : ∑ a, weight a * (value a)^6 = ((397 : ℝ) / 6144))
    (moment4 : ∑ a, weight a * (value a)^10 = ((30037 : ℝ) / 1572864))
    (moment5 : ∑ a, weight a * (value a)^15 = ((1198473 : ℝ) / 268435456))
    (moment6 : ∑ a, weight a * (value a)^21 = ((871870863 : ℝ) / 1099511627776))
    (a : A) (ha : 0 < weight a) :
    polynomial (value a) = 0 ∧ value a ∈ Set.Ioc (0 : ℝ) 1 := by
  have zero : ∑ b, weight b * polynomial (value b) = 0 := by
    calc
      _ = ∑ b, (((15694924948152899715 : ℝ) / 318782149412549765890048) * (weight b * (value b)^0) + ((-101589877798659355833 : ℝ) / 318782149412549765890048) * (weight b * (value b)^1) + ((175777975580685893075 : ℝ) / 79695537353137441472512) * (weight b * (value b)^3) + ((-5275629367498209825 : ℝ) / 311310692785693130752) * (weight b * (value b)^6) + ((141906319413452685 : ℝ) / 1216057393694113792) * (weight b * (value b)^10) + ((-2372523878540265 : ℝ) / 4750224194117632) * (weight b * (value b)^15) + ((1 : ℝ) / 1) * (weight b * (value b)^21)) := by
        apply Finset.sum_congr rfl
        intro b _
        dsimp [polynomial]
        ring
      _ = (((15694924948152899715 : ℝ) / 318782149412549765890048) * (∑ b, weight b * (value b)^0) + ((-101589877798659355833 : ℝ) / 318782149412549765890048) * (∑ b, weight b * (value b)^1) + ((175777975580685893075 : ℝ) / 79695537353137441472512) * (∑ b, weight b * (value b)^3) + ((-5275629367498209825 : ℝ) / 311310692785693130752) * (∑ b, weight b * (value b)^6) + ((141906319413452685 : ℝ) / 1216057393694113792) * (∑ b, weight b * (value b)^10) + ((-2372523878540265 : ℝ) / 4750224194117632) * (∑ b, weight b * (value b)^15) + ((1 : ℝ) / 1) * (∑ b, weight b * (value b)^21)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 0 := by
        rw [moment0, moment1, moment2, moment3, moment4, moment5, moment6]
        norm_num
  exact ⟨supported_atom_is_root weight value polynomial hw
    (fun b => nonnegative (value b) (hv b).1.le (hv b).2) zero a ha, hv a⟩

#print axioms nonnegative
#print axioms nonzero_value
#print axioms annihilation
#print axioms finite_supported_bank

end Astra.Generated.Certificate_e49c1e3d6bffee594b99574d3364e700e8f25342933fe31add2aa6129729bc6b
