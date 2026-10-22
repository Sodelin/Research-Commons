/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Natural-prefix observations tied EXACTLY to the original Fin-indexed
block list and C0 sum. These are proof helpers, not replacement programs.
-/
import PolytomyOriginalOuterBodyMeaning

namespace PolytomyReductionModel

def originalRealBlockBitsAt (R : RawMSSCRecord) (n : ℕ) : List Bool :=
  if h : n < R.rows.length then rawRowBlockBits R (some ⟨n, h⟩) else []

def originalRealBlockCostAt (R : RawMSSCRecord) (n : ℕ) : ℕ :=
  if h : n < R.rows.length then
    combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R (some ⟨n, h⟩)).length - 1) else 0

def originalRealBlocksBits (R : RawMSSCRecord) (n : ℕ) : List Bool :=
  (List.range n).flatMap (originalRealBlockBitsAt R)

def originalRealBlocksCost (R : RawMSSCRecord) (n : ℕ) : ℕ :=
  ((List.range n).map (originalRealBlockCostAt R)).sum

theorem originalRealBlocksBits_succ (R : RawMSSCRecord) (n : ℕ) :
    originalRealBlocksBits R (n + 1) = originalRealBlocksBits R n ++ originalRealBlockBitsAt R n := by
  simp [originalRealBlocksBits, List.range_succ, List.flatMap_append]

theorem originalRealBlocksCost_succ (R : RawMSSCRecord) (n : ℕ) :
    originalRealBlocksCost R (n + 1) = originalRealBlocksCost R n + originalRealBlockCostAt R n := by
  simp [originalRealBlocksCost, List.range_succ, List.map_append, List.sum_append]

theorem original_finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ_last, List.map_append, List.map_map, List.range_succ]
      change (List.finRange n).map Fin.val ++ [n] = List.range n ++ [n]
      rw [ih]

theorem originalRealBlocksBits_full (R : RawMSSCRecord) :
    originalRealBlocksBits R R.rows.length = (List.finRange R.rows.length).flatMap (fun i => rawRowBlockBits R (some i)) := by
  unfold originalRealBlocksBits
  rw [← original_finRange_values, List.flatMap_map]
  have h : (fun i : Fin R.rows.length => originalRealBlockBitsAt R i.val) =
      (fun i => rawRowBlockBits R (some i)) := by
    funext i; simp [originalRealBlockBitsAt, i.isLt]
  change (List.finRange R.rows.length).flatMap (fun i => originalRealBlockBitsAt R i.val) = _
  rw [h]

theorem originalRealBlocksCost_full (R : RawMSSCRecord) :
    originalRealBlocksCost R R.rows.length = ((List.finRange R.rows.length).map
      (fun i => combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R (some i)).length - 1))).sum := by
  unfold originalRealBlocksCost
  rw [← original_finRange_values, List.map_map]
  have h : (fun i : Fin R.rows.length => originalRealBlockCostAt R i.val) =
      (fun i => combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R (some i)).length - 1)) := by
    funext i; simp [originalRealBlockCostAt, i.isLt]
  change ((List.finRange R.rows.length).map (fun i => originalRealBlockCostAt R i.val)).sum = _
  rw [h]

theorem originalBlockList_bits (R : RawMSSCRecord) :
    (blockIndexList R.rows.length).flatMap (rawRowBlockBits R) =
      rawRowBlockBits R none ++ originalRealBlocksBits R R.rows.length := by
  rw [originalRealBlocksBits_full]
  simp [blockIndexList, List.flatMap_map]

theorem originalFixedCost_parts (R : RawMSSCRecord) :
    rawRowFixedCost R = combTailCost (rawRowAlphabet R) 1 ((rawRowCodes R none).length - 1) +
      originalRealBlocksCost R R.rows.length := by
  rw [originalRealBlocksCost_full]
  simp [rawRowFixedCost, blockIndexList, List.map_map]

/- The finRange_succ_last API was read directly at Lean 4.33.1; the
range/flatMap/map APIs were inspected at the pinned source versions.
This establishes original list ORDER and exact original fixed cost,
not merely equality of a block set or an unrelated label-count score.
-/

end PolytomyReductionModel
