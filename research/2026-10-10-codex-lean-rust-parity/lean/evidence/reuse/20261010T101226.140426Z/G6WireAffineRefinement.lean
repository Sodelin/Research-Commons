import G6RationalAffineWitness
import GParity.Affine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# The executable wire witness checks the inherited affine semantics

Contributor: Codex / lean_reuse, 10 October 2026.
Arbitrary row/vector lists are not presumed to be typed vectors. The mapping
requires the parser's exact row lengths, and successful witness checking also
checks the returned vector length. Ordered duplicates are preserved in the
wire list and forgotten only in the semantic finite set.

This module proves certificate semantics. It does not assume a bounded solver
always returns an answer: the executable may return UNKNOWN at its projection
cap. Rust/Lean byte correspondence and original source/chart admission are
separate consumers of this mathematical checker contract.
-/
namespace UnifiedLean.G6.WireAffineRefinement

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open scoped BigOperators

def decodeVector (n : ℕ) (x : List Rat) : Fin n → ℚ :=
  fun i => x[i.val]?.getD 0

def decodeRow (n : ℕ) (r : GParity.Affine.Row) : Row n :=
  ⟨decodeVector n r.coeff, r.bound, r.strict⟩

def decodeRows (n : ℕ) (rs : List GParity.Affine.Row) : List (Row n) :=
  rs.map (decodeRow n)

def RowsWellFormed (n : ℕ) (rs : List GParity.Affine.Row) : Prop :=
  ∀ r ∈ rs, r.coeff.length = n

theorem ofFn_decodeVector (n : ℕ) (x : List Rat) (hx : x.length = n) :
    List.ofFn (decodeVector n x) = x := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · have hix : i < x.length := by omega
    simp [List.getElem?_ofFn, hi, decodeVector, List.getElem?_eq_getElem hix]
  · have hix : x.length ≤ i := by omega
    simp [List.getElem?_ofFn, hi, List.getElem?_eq_none hix]

theorem zipWith_ofFn {n : ℕ} (a x : Fin n → Rat) :
    (List.ofFn a).zipWith (· * ·) (List.ofFn x) = List.ofFn (fun i => a i * x i) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n <;>
    simp [List.getElem?_zipWith, List.getElem?_ofFn, hi]

theorem dot_ofFn {n : ℕ} (a x : Fin n → Rat) :
    GParity.Rational.dot (List.ofFn a) (List.ofFn x) = ∑ i, a i * x i := by
  rw [GParity.Rational.dot, zipWith_ofFn, ← List.sum_eq_foldl, List.sum_ofFn]

theorem decodeRow_eval (n : ℕ) (r : GParity.Affine.Row) (x : List Rat)
    (hr : r.coeff.length = n) (hx : x.length = n) :
    (decodeRow n r).eval (decodeVector n x) = r.eval x := by
  change (∑ i, (decodeVector n r.coeff i : ℚ) * decodeVector n x i) =
    GParity.Rational.dot r.coeff x
  rw [← ofFn_decodeVector n r.coeff hr, ← ofFn_decodeVector n x hx, dot_ofFn]
  simp only [Rat.cast_id]

theorem decodeRow_holds (n : ℕ) (r : GParity.Affine.Row) (x : List Rat)
    (hr : r.coeff.length = n) (hx : x.length = n) :
    r.holds x = true ↔ (decodeRow n r).Holds (decodeVector n x) := by
  have he := decodeRow_eval n r x hr hx
  cases hs : r.strict <;>
    simp [GParity.Affine.Row.holds, Row.Holds, decodeRow, Rel, hs, he]

/-- The runtime's positive-output checker has precisely the typed affine
meaning, including the exact returned dimension. -/
theorem checkWitness_correct (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (x : List Rat) :
    GParity.Affine.checkWitness n rows x = true ↔
      x.length = n ∧ ∀ r ∈ (decodeRows n rows).toFinset, r.Holds (decodeVector n x) := by
  have hshape : rows.all (fun r => r.coeff.length == n) = true := by
    simp only [List.all_eq_true, beq_iff_eq]
    exact hrows
  simp only [GParity.Affine.checkWitness, hshape, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true]
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨hx, ?_⟩
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact (decodeRow_holds n r x (hrows r hr) hx).mp (hs r hr)
  · rintro ⟨hx, hs⟩
    refine ⟨hx, ?_⟩
    intro r hr
    apply (decodeRow_holds n r x (hrows r hr) hx).mpr
    exact hs (decodeRow n r) (List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩))

/-- A checked wire certificate is a real witness for the inherited rows. -/
theorem checkedWireWitness_real (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (x : List Rat)
    (hx : GParity.Affine.checkWitness n rows x = true) :
    ∀ r ∈ (decodeRows n rows).toFinset,
      r.Holds (fun i => (decodeVector n x i : ℝ)) :=
  rationalWitness_real _ _ ((checkWitness_correct n rows hrows x).mp hx).2

theorem checkedWireWitness_feasible (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (x : List Rat)
    (hx : GParity.Affine.checkWitness n rows x = true) :
    Feasible ℝ (decodeRows n rows).toFinset :=
  ⟨fun i => (decodeVector n x i : ℝ), checkedWireWitness_real n rows hrows x hx⟩

#print axioms ofFn_decodeVector
#print axioms dot_ofFn
#print axioms decodeRow_eval
#print axioms decodeRow_holds
#print axioms checkWitness_correct
#print axioms checkedWireWitness_real
#print axioms checkedWireWitness_feasible

end UnifiedLean.G6.WireAffineRefinement
