import G7EffectiveCoefficientSupport

/-! SOURCE PROPOSAL. The complete imported context has NOT been elaborated.
This checks a supplied finite native population table against the EXISTING
literal merger recurrence. It is not a Rust/parser proof or a new kernel.
No #eval, native_decide, new axiom, external process or runtime writer occurs. -/

namespace Astra.NativePopulationTableCertificate

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveCoefficientSupport
open scoped NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- Native destinations are actual supplied admitted Codes, not validator flags.
Repeated destinations and raw duplicate/zero monomials are permitted. -/
abbrev Table (N : RootedBinary V E X) (sample : Copy → X) :=
  List (Code N sample × Expr)

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
      by_cases hz : z.1 = k
      · simp [coefficient, Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.coeff_monomial, hz]
      · have hkz : k ≠ z.1 := Ne.symm hz
        simp [coefficient, Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.coeff_monomial, hz, hkz]

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

/-- Complete coefficient of one Code; duplicate native entries are summed. -/
def collect {N : RootedBinary V E X} {sample : Copy → X}
    (rows : Table N sample) (d : Code N sample) : Expr :=
  rows.flatMap fun row => if row.1 = d then row.2 else []

lemma collect_empty_of_absent {N : RootedBinary V E X} {sample : Copy → X}
    (rows : Table N sample) (d : Code N sample)
    (hd : d ∉ rows.map Prod.fst) : collect rows d = [] := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hr : row.1 ≠ d := by
        intro h
        apply hd
        simp [h]
      have ht : d ∉ rows.map Prod.fst := by
        intro h
        apply hd
        simp [h]
      change (if row.1 = d then row.2 else []) ++ collect rows d = []
      rw [if_neg hr, List.nil_append]
      exact ih ht

/-- This uses merger support plus supplied destinations, never all Code states.
A spurious nonzero native destination therefore cannot hide outside support. -/
def carrier (N : RootedBinary V E X) {sample : Copy → X} (fuel : Nat)
    (s : Code N sample) (rows : Table N sample) : List (Code N sample) :=
  (destinations N fuel s ++ rows.map Prod.fst).dedup

def check (N : RootedBinary V E X) {sample : Copy → X} (fuel : Nat)
    (s : Code N sample) (rows : Table N sample) : Bool :=
  (carrier N fuel s rows).all fun d =>
    checkExpr (collect rows d) (coefficients N fuel s d)

/-- The conclusion includes EVERY admitted destination, including zero on
all omitted destinations. It assumes no final row-polynomial equality. -/
theorem check_sound (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : Nat) (s : Code N sample) (rows : Table N sample)
    (h : check N fuel s rows = true) (d : Code N sample) :
    exprPolynomial (collect rows d) =
      exprPolynomial (coefficients N fuel s d) := by
  by_cases hd : d ∈ carrier N fuel s rows
  · have hall := List.all_eq_true.mp h
    exact checkExpr_sound _ _ (hall d hd)
  · have hn : d ∉ destinations N fuel s ∧ d ∉ rows.map Prod.fst := by
      simpa only [carrier, List.mem_dedup, List.mem_append, not_or] using hd
    calc
      exprPolynomial (collect rows d) = 0 := by
        rw [collect_empty_of_absent rows d hn.2]
        rfl
      _ = exprPolynomial (coefficients N fuel s d) :=
        (coefficients_polynomial_zero_of_not_mem N fuel s d hn.1).symm

/-- Actual co-located population semantics, using the original positive rates
and copy-cardinality fuel. No completed-calendar or source-census claim. -/
theorem checked_actual_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (rows : Table N sample)
    (h : check N (Fintype.card Copy) s rows = true)
    (d : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-pairRate r i * (t : ℝ)))
      (exprPolynomial (collect rows d)) =
        (sourceTimeKernel N r t s d).toReal := by
  rw [check_sound N (Fintype.card Copy) s rows h d]
  exact actual_population_coefficients N s d i hs r t

end Astra.NativePopulationTableCertificate
