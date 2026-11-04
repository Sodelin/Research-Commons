import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
Algebra for one complete successful native trace step. Only inputs actually
present in the entering row require a conditional-row certificate. Unknown or
refused native calls supply no such certificate. This does not construct the
native decoder, prove a BTreeMap operation, admit a physical source or discharge
raw completion support. The coefficient semiring may be the existing rational
multivariate polynomial ring after its exact native decoding is supplied.
-/
namespace Astra.G7SuccessfulTraceRows
open scoped BigOperators

variable {A K C : Type*} [DecidableEq K] [Semiring C]

abbrev Rows (A C : Type*) := List (A × C)

def fibre (key : A → K) (rows : Rows A C) (b : K) : C :=
  (rows.map fun a => if key a.1 = b then a.2 else 0).sum

def scale (q : C) (rows : Rows A C) : Rows A C :=
  rows.map fun a => (a.1, q * a.2)

def bindRows (rows : Rows A C) (next : A → Rows A C) : Rows A C :=
  rows.flatMap fun a => scale a.2 (next a.1)

lemma fibre_append (key : A → K) (left right : Rows A C) (b : K) :
    fibre key (left ++ right) b = fibre key left b + fibre key right b := by
  simp [fibre, List.map_append, List.sum_append]

lemma fibre_scale (key : A → K) (q : C) (rows : Rows A C) (b : K) :
    fibre key (scale q rows) b = q * fibre key rows b := by
  induction rows with
  | nil => simp [fibre, scale]
  | cons a rows ih =>
      by_cases h : key a.1 = b <;>
        simp [fibre, scale, h, mul_add] at ih ⊢ <;> exact ih

theorem fibre_bind (key : A → K) (rows : Rows A C)
    (next : A → Rows A C) (b : K) :
    fibre key (bindRows rows next) b =
      (rows.map fun a => a.2 * fibre key (next a.1) b).sum := by
  induction rows with
  | nil => simp [bindRows, fibre]
  | cons a rows ih =>
      change fibre key (scale a.2 (next a.1) ++ bindRows rows next) b = _
      rw [fibre_append, fibre_scale, ih]
      rfl

lemma sum_by_fibres [Fintype K] (key : A → K) (rows : Rows A C)
    (g : K → C) :
    (rows.map fun a => a.2 * g (key a.1)).sum =
      ∑ k : K, fibre key rows k * g k := by
  induction rows with
  | nil => simp [fibre]
  | cons a rows ih =>
      simp only [List.map_cons, List.sum_cons]
      simp only [fibre, List.map_cons, List.sum_cons, add_mul,
        Finset.sum_add_distrib] at ih ⊢
      rw [ih]
      congr 1
      simp [ite_mul, eq_comm]

/-- The conditional identity is required only for the ACTUAL entering rows,
but for EVERY output key, including omitted destinations. -/
theorem queried_bind_matrix [Fintype K] (key : A → K)
    (rows : Rows A C) (next : A → Rows A C) (table : K → K → C)
    (hqueried : ∀ a ∈ rows, ∀ b, fibre key (next a.1) b = table (key a.1) b)
    (b : K) :
    fibre key (bindRows rows next) b =
      ∑ k : K, fibre key rows k * table k b := by
  rw [fibre_bind]
  calc
    (rows.map fun a => a.2 * fibre key (next a.1) b).sum =
        (rows.map fun a => a.2 * table (key a.1) b).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      rw [hqueried a ha b]
    _ = ∑ k : K, fibre key rows k * table k b :=
      sum_by_fibres key rows (fun k => table k b)

/-- A compressed output is accepted only through its COMPLETE fibre equality.
The theorem does not assume that a successful native map operation proves it. -/
theorem compressed_step [Fintype K] (key : A → K)
    (rows compressed : Rows A C) (next : A → Rows A C)
    (table : K → K → C) (prefix : K → C)
    (hqueried : ∀ a ∈ rows, ∀ b, fibre key (next a.1) b = table (key a.1) b)
    (hprefix : ∀ k, fibre key rows k = prefix k)
    (hcompressed : ∀ b, fibre key compressed b = fibre key (bindRows rows next) b)
    (b : K) :
    fibre key compressed b = ∑ k : K, prefix k * table k b := by
  rw [hcompressed, queried_bind_matrix key rows next table hqueried]
  simp_rw [hprefix]

end Astra.G7SuccessfulTraceRows
