/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact semantic positions of the original legal-node mask. Every index is
bounded by the mask length; the full ordered suffix list is precisely the
actual subtree-view list. This is the specification for a physical cursor,
not an assumption of cost-free random access or an already emitted loop.
-/
import PolytomyRawTreeNodeMask

namespace PolytomyReductionModel

def rawMaskIndices : List Bool → List ℕ
  | [] => []
  | mark :: mask =>
      if mark then 0 :: (rawMaskIndices mask).map Nat.succ
      else (rawMaskIndices mask).map Nat.succ

theorem rawMaskIndices_bound (mask : List Bool) (i : ℕ) :
    i ∈ rawMaskIndices mask → i < mask.length := by
  induction mask generalizing i with
  | nil => simp [rawMaskIndices]
  | cons mark mask ih =>
      cases mark with
      | false =>
          simp only [rawMaskIndices, Bool.false_eq_true, ↓reduceIte, List.mem_map]
          rintro ⟨j, hj, rfl⟩
          exact Nat.succ_lt_succ (ih j hj)
      | true =>
          simp only [rawMaskIndices, Bool.true_eq_true, ↓reduceIte, List.mem_cons, List.mem_map]
          rintro (rfl | ⟨j, hj, rfl⟩)
          · simp
          · exact Nat.succ_lt_succ (ih j hj)

theorem rawMarkedSuffixes_indices (mask bits : List Bool) (h : mask.length ≤ bits.length) :
    rawMarkedSuffixes bits mask = (rawMaskIndices mask).map (fun i => bits.drop i) := by
  induction mask generalizing bits with
  | nil => simp [rawMarkedSuffixes, rawMaskIndices]
  | cons mark mask ih =>
      cases bits with
      | nil => simp at h
      | cons b bits =>
          have ht : mask.length ≤ bits.length := by simpa using h
          cases mark <;>
            simp [rawMarkedSuffixes, rawMaskIndices, ih bits ht, List.map_map, Function.comp_def]

theorem rawMaskIndices_views (T : BTree (ℕ × ℕ)) (rest : List Bool) :
    (rawMaskIndices (rawNodeMask T)).map (fun i => (rawCellTreeBits T ++ rest).drop i) =
      (rawNodeViews T rest).map rawViewSuffix := by
  have hlen : (rawNodeMask T).length ≤ (rawCellTreeBits T ++ rest).length := by
    rw [rawNodeMask_length, List.length_append]
    omega
  rw [← rawMarkedSuffixes_indices (rawNodeMask T) (rawCellTreeBits T ++ rest) hlen]
  simpa [rawMarkedSuffixes] using rawMarkedSuffixes_tree T rest []

theorem rawForestMaskParse_one (T : BTree (ℕ × ℕ)) (rest : List Bool) :
    rawForestMaskParse (rawCellTreeBits T ++ rest).length 1 (rawCellTreeBits T ++ rest) =
      some (rest, rawNodeMask T) := by
  apply (rawForestMaskParse_all_words (rawCellTreeBits T ++ rest) rest (rawNodeMask T) 1).mpr
  exact ⟨[T], rfl, by simp [rawForestWord], by simp [rawForestNodeMask]⟩

theorem rawForestMaskParse_one_sound (bits rest mask : List Bool)
    (h : rawForestMaskParse bits.length 1 bits = some (rest, mask)) :
    ∃ T : BTree (ℕ × ℕ), bits = rawCellTreeBits T ++ rest ∧ mask = rawNodeMask T := by
  obtain ⟨ts, hlen, hbits, hmask⟩ := (rawForestMaskParse_all_words bits rest mask 1).mp h
  cases ts with
  | nil => simp at hlen
  | cons t ts =>
      cases ts with
      | nil => exact ⟨t, by simpa [rawForestWord] using hbits, by simpa [rawForestNodeMask] using hmask⟩
      | cons u us => simp at hlen

def rawIndexedSubtree (bits : List Bool) (i : ℕ) : Option (List Bool × List Bool) :=
  rawForestMaskParse (bits.drop i).length 1 (bits.drop i)

theorem rawIndexedSubtree_views (T : BTree (ℕ × ℕ)) (rest : List Bool) :
    (rawMaskIndices (rawNodeMask T)).map (rawIndexedSubtree (rawCellTreeBits T ++ rest)) =
      (rawNodeViews T rest).map (fun v => some (v.2, rawNodeMask v.1)) := by
  have h := congrArg (List.map (fun bits : List Bool => rawForestMaskParse bits.length 1 bits))
    (rawMaskIndices_views T rest)
  simpa only [List.map_map, Function.comp_def, rawIndexedSubtree, rawViewSuffix,
    rawForestMaskParse_one] using h

theorem rawMaskIndex_is_real_node (T : BTree (ℕ × ℕ)) (rest : List Bool) (i : ℕ)
    (hi : i ∈ rawMaskIndices (rawNodeMask T)) :
    ∃ v ∈ rawNodeViews T rest, (rawCellTreeBits T ++ rest).drop i = rawViewSuffix v := by
  have hm : (rawCellTreeBits T ++ rest).drop i ∈
      (rawMaskIndices (rawNodeMask T)).map (fun j => (rawCellTreeBits T ++ rest).drop j) :=
    List.mem_map.mpr ⟨i, hi, rfl⟩
  rw [rawMaskIndices_views] at hm
  obtain ⟨v, hv, he⟩ := List.mem_map.mp hm
  exact ⟨v, hv, he.symm⟩

/- The exact LIST identity, rather than only sound membership, retains
all original fixed-tree clades, including arbitrary composite children.
The physical cursor still has to enumerate these bounded positions with
charged increments and execute the actual replay/query bodies. -/

end PolytomyReductionModel
