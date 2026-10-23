import G7SparseRowProducts
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

/-! Exact finite coefficient/fibre checking for the EXISTING sparse-row type.
The original epoch/word recurrence and source laws are reused unchanged.
This compares complete finite rational sums, never sampled evaluations.
A Boolean result is usable only through the checked soundness theorems below.
Current-context elaboration and an actual native epoch caller remain separate. -/
set_option backward.isDefEq.respectTransparency false
namespace Astra.NativeSparseTableCertificate
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.SparseRowProducts
open scoped BigOperators

variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Computational key: repeated variable occurrences ADD their exponents.
No sorting, polynomial normalizer or complete state carrier is enumerated. -/
def powerKey (m : List (I × Nat)) : I → Nat :=
  fun i => (m.map fun a => if a.1 = i then a.2 else 0).sum

@[simp] lemma powerKey_cons (a : I × Nat) (m : List (I × Nat)) (i : I) :
    powerKey (a :: m) i = (if a.1 = i then a.2 else 0) + powerKey m i := rfl

private lemma raw_product (m : List (I × Nat)) :
    (m.map fun a => (MvPolynomial.X a.1 : MvPolynomial I ℚ) ^ a.2).prod =
      ∏ i : I, MvPolynomial.X i ^ powerKey m i := by
  induction m with
  | nil => simp [powerKey]
  | cons a m ih =>
      have hsingle :
          (∏ i : I, (MvPolynomial.X i : MvPolynomial I ℚ) ^
            (if a.1 = i then a.2 else 0)) = MvPolynomial.X a.1 ^ a.2 := by
        apply Finset.prod_eq_single a.1
        · intro b _ hne
          simp [Ne.symm hne]
        · intro h
          simp at h
      rw [List.map_cons, List.prod_cons, ih]
      simp_rw [powerKey_cons, pow_add]
      rw [Finset.prod_mul_distrib, hsingle]

private lemma indicator_key_iff (d : I →₀ Nat) (k : I → Nat) :
    d = Finsupp.indicator Finset.univ (fun i _ => k i) ↔ (fun i => d i) = k := by
  constructor
  · intro h
    funext i
    simpa [Finsupp.indicator] using congrArg (fun x : I →₀ Nat => x i) h
  · intro h
    ext i
    simpa [Finsupp.indicator] using congrFun h i

def coefficient (p : Sparse I) (k : I → Nat) : ℚ :=
  (p.map fun z => if powerKey z.1 = k then z.2 else 0).sum

lemma polynomial_coefficient (p : Sparse I) (d : I →₀ Nat) :
    MvPolynomial.coeff d (polynomial p) = coefficient p (fun i => d i) := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      rw [polynomial_cons, MvPolynomial.coeff_add, ih,
        MvPolynomial.coeff_C_mul, raw_product, MvPolynomial.coeff_prod_X_pow]
      simp_rw [indicator_key_iff]
      change z.2 * (if (fun i => d i) = powerKey z.1 then 1 else 0) +
          coefficient p (fun i => d i) =
        (if powerKey z.1 = (fun i => d i) then z.2 else 0) +
          coefficient p (fun i => d i)
      by_cases h : powerKey z.1 = (fun i => d i) <;> simp [h, eq_comm]

def monomialKeys (p : Sparse I) : List (I → Nat) := p.map fun z => powerKey z.1

def checkSparse (p q : Sparse I) : Bool :=
  ((monomialKeys p ++ monomialKeys q).dedup).all fun k =>
    decide (coefficient p k = coefficient q k)

lemma coefficient_zero_of_absent (p : Sparse I) (k : I → Nat)
    (hk : k ∉ monomialKeys p) : coefficient p k = 0 := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      have hz : powerKey z.1 ≠ k := by
        intro h
        apply hk
        simp [monomialKeys, h]
      have hp : k ∉ monomialKeys p := by
        intro h
        apply hk
        simp [monomialKeys, h]
      change (if powerKey z.1 = k then z.2 else 0) + coefficient p k = 0
      rw [if_neg hz, zero_add]
      exact ih hp

/-- Equality on the COMPLETE union of finite exponent keys proves the entire
multivariate polynomial identity; absent coefficients are proved zero. -/
theorem checkSparse_sound (p q : Sparse I) (h : checkSparse p q = true) :
    polynomial p = polynomial q := by
  apply MvPolynomial.ext
  intro d
  rw [polynomial_coefficient, polynomial_coefficient]
  by_cases hk : (fun i => d i) ∈ (monomialKeys p ++ monomialKeys q).dedup
  · exact of_decide_eq_true ((List.all_eq_true.mp h) _ hk)
  · have hn : (fun i => d i) ∉ monomialKeys p ∧
        (fun i => d i) ∉ monomialKeys q := by
      simpa only [List.mem_dedup, List.mem_append, not_or] using hk
    rw [coefficient_zero_of_absent p _ hn.1, coefficient_zero_of_absent q _ hn.2]

def rowKeys {A K : Type*} (key : A → K) (rows : Rows I A) : List K :=
  rows.map fun r => key r.1

lemma readRows_empty_of_absent {A K : Type*} [DecidableEq K]
    (key : A → K) (rows : Rows I A) (k : K) (hk : k ∉ rowKeys key rows) :
    readRows key rows k = [] := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      have hr : key r.1 ≠ k := by
        intro h
        apply hk
        simp [rowKeys, h]
      have ht : k ∉ rowKeys key rows := by
        intro h
        apply hk
        simp [rowKeys, h]
      change (if key r.1 = k then r.2 else []) ++ readRows key rows k = []
      rw [if_neg hr, List.nil_append]
      exact ih ht

/-- Both reference AND supplied destination keys are checked. Duplicate rows
contribute their full sums. A spurious nonzero supplied key cannot hide. -/
def checkRows {A K : Type*} [DecidableEq K] (key : A → K)
    (reference supplied : Rows I A) : Bool :=
  ((rowKeys key reference ++ rowKeys key supplied).dedup).all fun k =>
    checkSparse (readRows key reference k) (readRows key supplied k)

theorem checkRows_sound {A K : Type*} [DecidableEq K] (key : A → K)
    (reference supplied : Rows I A) (h : checkRows key reference supplied = true) :
    ∀ k, polynomial (readRows key reference k) =
      polynomial (readRows key supplied k) := by
  intro k
  by_cases hk : k ∈ (rowKeys key reference ++ rowKeys key supplied).dedup
  · exact checkSparse_sound _ _ ((List.all_eq_true.mp h) k hk)
  · have hn : k ∉ rowKeys key reference ∧ k ∉ rowKeys key supplied := by
      simpa only [List.mem_dedup, List.mem_append, not_or] using hk
    rw [readRows_empty_of_absent key reference k hn.1,
      readRows_empty_of_absent key supplied k hn.2]

/-- Repeated variable occurrences and duplicate monomials are literal inputs,
not a promise that native syntax is already normalized. -/
example : checkSparse (I := Fin 2)
    [([(0,1),(0,1)],1/2), ([(0,2)],1/2)] [([(0,2)],1)] = true := by
  decide +kernel

/-- A foreign nonzero destination is rejected even when every original key
agrees. The check uses the union rather than only the reference support. -/
example : checkRows (I := Fin 2) (id : Fin 2 → Fin 2)
    [(0,[([],1)])] [(0,[([],1)]),(1,[([],1)])] = false := by
  decide +kernel

end Astra.NativeSparseTableCertificate
