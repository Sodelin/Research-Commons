import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-! SOURCE-ONLY EXACT DEFINITION/PROOF PROJECTION. Complete context UNELABORATED.
This selects the original Expr/polynomial declarations and the already authored
finite coefficient sublemma. It does not include source Codes, merger support,
table soundness, sourceTimeKernel or an actual population law. Do not co-import
this virtual-document projection with its full original declaration modules.
No checker, compiler, #eval, native_decide, new axiom or job was run. -/

namespace GProgram.G7.SinglePopulationPolynomialKernel
set_option backward.isDefEq.respectTransparency false

abbrev Expr := List (ℕ × ℚ)

noncomputable def exprPolynomial (p : Expr) : Polynomial ℚ :=
  (p.map (fun z => Polynomial.C z.2 * Polynomial.X ^ z.1)).sum


@[simp] lemma exprPolynomial_cons (z : ℕ × ℚ) (p : Expr) :
    exprPolynomial (z::p) = Polynomial.C z.2 * Polynomial.X ^ z.1 + exprPolynomial p := rfl


end GProgram.G7.SinglePopulationPolynomialKernel

namespace Astra.NativePopulationTableCertificate
open GProgram.G7.SinglePopulationPolynomialKernel

def coefficient (p : Expr) (k : Nat) : ℚ :=
  (p.map fun z => if z.1 = k then z.2 else 0).sum

def checkExpr (p q : Expr) : Bool :=
  ((p.map Prod.fst ++ q.map Prod.fst).dedup).all fun k =>
    decide (coefficient p k = coefficient q k)

lemma polynomial_coefficient (p : Expr) (k : Nat) :
    (exprPolynomial p).coeff k = coefficient p k := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      rw [exprPolynomial_cons, Polynomial.coeff_add, ih]
      by_cases hz : z.1 = k <;>
        simp [coefficient, Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.coeff_monomial, hz, eq_comm]

lemma coefficient_zero_of_absent (p : Expr) (k : Nat)
    (hk : k ∉ p.map Prod.fst) : coefficient p k = 0 := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      have hz : z.1 ≠ k := by
        intro h
        apply hk
        simp [h]
      have hp : k ∉ p.map Prod.fst := by
        intro h
        apply hk
        simp [h]
      change (if z.1 = k then z.2 else 0) + coefficient p k = 0
      rw [if_neg hz, zero_add]
      exact ih hp

/-- Finite coefficient comparison is sound for every real evaluation. The
checker compares rational sums, not samples or floating-point values. -/
theorem checkExpr_sound (p q : Expr) (h : checkExpr p q = true) :
    exprPolynomial p = exprPolynomial q := by
  apply Polynomial.ext
  intro k
  rw [polynomial_coefficient, polynomial_coefficient]
  by_cases hk : k ∈ (p.map Prod.fst ++ q.map Prod.fst).dedup
  · have hall := List.all_eq_true.mp h
    exact of_decide_eq_true (hall k hk)
  · have hn : k ∉ p.map Prod.fst ∧ k ∉ q.map Prod.fst := by
      simpa only [List.mem_dedup, List.mem_append, not_or] using hk
    rw [coefficient_zero_of_absent p k hn.1,
      coefficient_zero_of_absent q k hn.2]

end Astra.NativePopulationTableCertificate
