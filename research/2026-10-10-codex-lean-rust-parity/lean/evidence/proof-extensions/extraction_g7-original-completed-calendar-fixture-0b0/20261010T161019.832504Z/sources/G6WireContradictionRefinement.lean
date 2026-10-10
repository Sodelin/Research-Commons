import G6WireAffineRefinement
import G6AffineContradictionCertificate

/-!
# Native contradiction checking refines the proved original-row certificate

Contributor: Codex / lean_reuse_recovery, 10 October 2026.
One multiplier per original row and exact coefficient lengths are explicit.
The proof checks the native list/fold/Boolean program, not a replacement
certificate predicate. No projection-cap completeness or source admission is
assumed: an accepted certificate excludes the supplied matrix only.
-/
namespace UnifiedLean.G6.WireContradictionRefinement

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.G6.AffineContradictionCertificate
open scoped BigOperators

def indexedRows (n : ℕ) (rows : List GParity.Affine.Row) : Fin rows.length → Row n :=
  fun i => decodeRow n (rows.get i)

def indexedWeights (rows : List GParity.Affine.Row) (weights : List Rat) :
    Fin rows.length → ℚ := decodeVector rows.length weights

theorem zip_ofFn {α β : Type*} {m : ℕ} (a : Fin m → α) (b : Fin m → β) :
    (List.ofFn a).zip (List.ofFn b) = List.ofFn (fun i => (a i, b i)) := by
  rw [List.zip_eq_zipWith]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < m <;>
    simp [List.getElem?_zipWith, List.getElem?_ofFn, hi]

theorem zipRows_eq_ofFn (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) :
    rows.zip weights = List.ofFn (fun i : Fin rows.length =>
      (rows.get i, indexedWeights rows weights i)) := by
  calc
    rows.zip weights = (List.ofFn rows.get).zip
        (List.ofFn (decodeVector rows.length weights)) := by
      rw [List.ofFn_get, ofFn_decodeVector rows.length weights hw]
    _ = _ := zip_ofFn _ _

theorem foldl_ofFn_sum {α : Type*} {m : ℕ} (a : Fin m → α) (f : α → Rat) :
    (List.ofFn a).foldl (fun z x => z + f x) 0 = ∑ i, f (a i) := by
  calc
    _ = ((List.ofFn a).map f).foldl (· + ·) 0 := by rw [List.foldl_map]
    _ = (List.ofFn (fun i => f (a i))).sum := by
      rw [← List.sum_eq_foldl, List.map_ofFn]
      rfl
    _ = _ := by rw [List.sum_ofFn]

theorem weightedFold_eq (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) (f : GParity.Affine.Row → Rat) :
    (rows.zip weights).foldl (fun z rw => z + rw.2 * f rw.1) 0 =
      ∑ i, indexedWeights rows weights i * f (rows.get i) := by
  rw [zipRows_eq_ofFn rows weights hw]
  exact foldl_ofFn_sum _ _

theorem nativeBound_eq (n : ℕ) (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) :
    (rows.zip weights).foldl (fun z rw => z + rw.2 * rw.1.bound) 0 =
      weightedBound (indexedRows n rows) (indexedWeights rows weights) := by
  exact weightedFold_eq rows weights hw GParity.Affine.Row.bound

theorem nativeCoeff_eq (n : ℕ) (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) (j : Fin n) :
    (rows.zip weights).foldl (fun z rw => z + rw.2 * (rw.1.coeff[j.val]?.getD 0)) 0 =
      weightedCoeff (indexedRows n rows) (indexedWeights rows weights) j := by
  exact weightedFold_eq rows weights hw (fun r => r.coeff[j.val]?.getD 0)

theorem nativeNonnegative_iff (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) :
    weights.all (fun w => decide (0 ≤ w)) = true ↔
      ∀ i, 0 ≤ indexedWeights rows weights i := by
  have ha :
      (List.ofFn (decodeVector rows.length weights)).all (fun w => decide (0 ≤ w)) =
        weights.all (fun w => decide (0 ≤ w)) := by
    rw [ofFn_decodeVector rows.length weights hw]
  rw [← ha]
  simp only [List.all_eq_true, decide_eq_true_eq, List.forall_mem_ofFn_iff]
  rfl

theorem nativeStrictUsed_iff (n : ℕ) (rows : List GParity.Affine.Row)
    (weights : List Rat) (hw : weights.length = rows.length) :
    (rows.zip weights).any (fun rw => rw.1.strict && decide (0 < rw.2)) = true ↔
      StrictUsed (indexedRows n rows) (indexedWeights rows weights) := by
  rw [zipRows_eq_ofFn rows weights hw]
  simp only [List.any_eq_true, List.mem_ofFn, Bool.and_eq_true, decide_eq_true_eq,
    StrictUsed, indexedRows, decodeRow]
  constructor
  · rintro ⟨p, ⟨i, rfl⟩, hs, hi⟩
    exact ⟨i, hi, hs⟩
  · rintro ⟨i, hi, hs⟩
    exact ⟨(rows.get i, indexedWeights rows weights i), ⟨i, rfl⟩, hs, hi⟩

/-- With exact input dimensions, the actual native Boolean checker is exactly
the proved rational original-row certificate predicate. -/
theorem checkContradiction_correct (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (weights : List Rat)
    (hw : weights.length = rows.length) :
    GParity.Affine.checkContradiction n rows weights = true ↔
      Valid (indexedRows n rows) (indexedWeights rows weights) := by
  have hshape : rows.all (fun r => r.coeff.length == n) = true := by
    simp only [List.all_eq_true, beq_iff_eq]
    exact hrows
  have hzero :
      (List.range n).all (fun j =>
        (rows.zip weights).foldl (fun z rw => z + rw.2 * (rw.1.coeff[j]?.getD 0)) 0 == 0) = true ↔
        ∀ j, weightedCoeff (indexedRows n rows) (indexedWeights rows weights) j = 0 := by
    simp only [List.all_eq_true, beq_iff_eq, List.mem_range]
    constructor
    · intro h j
      rw [← nativeCoeff_eq n rows weights hw j]
      exact h j.val j.isLt
    · intro h j hj
      exact (nativeCoeff_eq n rows weights hw ⟨j, hj⟩).trans (h ⟨j, hj⟩)
  simp only [GParity.Affine.checkContradiction, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, hw, hshape, true_and, and_true, decide_eq_true_eq,
    nativeNonnegative_iff rows weights hw, hzero, nativeBound_eq n rows weights hw,
    nativeStrictUsed_iff n rows weights hw, Valid, and_assoc]

theorem indexedRows_holds_iff (n : ℕ) (rows : List GParity.Affine.Row)
    (x : Fin n → ℝ) :
    (∀ i, (indexedRows n rows i).Holds x) ↔
      ∀ r ∈ (decodeRows n rows).toFinset, r.Holds x := by
  constructor
  · intro h q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
    simpa only [indexedRows, hi] using h i
  · intro h i
    apply h
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨rows.get i, List.get_mem _ _, rfl⟩

/-- A successful native negative certificate excludes every real vector of
the supplied matrix. The runtime may still return UNKNOWN at a cap. -/
theorem checkedWireContradiction_excludes_real (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (weights : List Rat)
    (hw : weights.length = rows.length)
    (h : GParity.Affine.checkContradiction n rows weights = true) :
    ¬ Feasible ℝ (decodeRows n rows).toFinset := by
  intro hf
  obtain ⟨x, hx⟩ := hf
  apply valid_excludes_real (indexedRows n rows) (indexedWeights rows weights)
    ((checkContradiction_correct n rows hrows weights hw).mp h)
  exact ⟨x, (indexedRows_holds_iff n rows x).mpr hx⟩

#print axioms zipRows_eq_ofFn
#print axioms weightedFold_eq
#print axioms checkContradiction_correct
#print axioms checkedWireContradiction_excludes_real

end UnifiedLean.G6.WireContradictionRefinement
