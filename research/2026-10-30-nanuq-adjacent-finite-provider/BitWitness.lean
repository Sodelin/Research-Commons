import TreeEdgeSemantics
set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate

theorem fold_or_bit {α : Type} (xs : List α) (f : α → Nat) (acc k : Nat) :
    ((xs.foldl (fun z x => z ||| f x) acc).testBit k) =
      (acc.testBit k || xs.any (fun x => (f x).testBit k)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons]
    cases acc.testBit k <;> cases (f x).testBit k <;> cases xs.any (fun x => (f x).testBit k) <;> rfl

theorem fold_cond_bit {α : Type} (xs : List α) (f : α → Nat) (b : α → Bool) (acc k : Nat) :
    ((xs.foldl (fun z x => if b x then z ||| f x else z) acc).testBit k) =
      (acc.testBit k || xs.any (fun x => b x && (f x).testBit k)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split <;> simp_all only [ih, Nat.testBit_or, List.any_cons, Bool.true_and, Bool.false_and]
    · cases acc.testBit k <;> cases (f x).testBit k <;> cases xs.any (fun x => b x && (f x).testBit k) <;> rfl
    · rfl

theorem one_shift_bit (i k : Nat) : (1 <<< i).testBit k = decide (i = k) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : k ≥ i
  · simp only [h, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [Nat.testBit_one_eq_true_iff_self_eq_zero, decide_eq_true_eq]
    omega
  · simp only [h, decide_false, Bool.false_and]
    have : i ≠ k := by omega
    simp [this]

theorem nested_witness_bit (tips : List Nat) (lo len : Nat)
    (entries : List (Quartet × Nat)) (acc k : Nat) :
    ((entries.foldl (fun acc qi =>
      (List.range 3).foldl (fun acc r =>
        if edgeWitness tips lo len qi.1 r then acc ||| (1 <<< (3*qi.2+r)) else acc) acc) acc).testBit k) =
    (acc.testBit k || entries.any (fun qi => (List.range 3).any
      (fun r => edgeWitness tips lo len qi.1 r && decide (3*qi.2+r=k)))) := by
  induction entries generalizing acc with
  | nil => simp
  | cons qi entries ih =>
    simp only [List.foldl_cons, ih, fold_cond_bit, one_shift_bit, List.any_cons]
    cases acc.testBit k <;>
      cases (List.range 3).any (fun r => edgeWitness tips lo len qi.1 r && decide (3*qi.2+r=k)) <;>
      cases entries.any (fun qi => (List.range 3).any (fun r => edgeWitness tips lo len qi.1 r && decide (3*qi.2+r=k))) <;> rfl

theorem edgeContribution_bit (tips : List Nat) (qs : List Quartet) (lo len k : Nat) :
    (edgeContribution tips qs lo len).testBit k =
    qs.zipIdx.any (fun qi => (List.range 3).any
      (fun r => edgeWitness tips lo len qi.1 r && decide (3*qi.2+r=k))) := by
  simp only [edgeContribution, nested_witness_bit, Nat.zero_testBit, Bool.false_or]

theorem Tree.physical_witness_iff (t : Tree) (tips : List Nat) (qs : List Quartet) (lo k : Nat) :
    (t.summary (edgeContribution tips qs) lo).testBit k = true ↔
      ∃ e ∈ t.internalIntervals lo, ∃ qi ∈ qs.zipIdx, ∃ r ∈ List.range 3,
        edgeWitness tips e.1 e.2 qi.1 r = true ∧ 3*qi.2+r=k := by
  simp only [Tree.summary_bit, edgeContribution_bit, List.any_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
theorem code_bit (pattern qi r : Nat) (hr : r < 3) :
    (code pattern qi).testBit r = pattern.testBit (3*qi+r) := by
  unfold code
  change ((pattern >>> (3*qi)) % 2^3).testBit r = _
  rw [Nat.testBit_mod_two_pow]
  simp only [hr, decide_true, Bool.true_and, Nat.testBit_shiftRight]

theorem Tree.code_physical_iff (t : Tree) (tips : List Nat) (qs : List Quartet)
    (lo idx r : Nat) (hr : r < 3) :
    (code (t.summary (edgeContribution tips qs) lo) idx).testBit r = true ↔
      ∃ e ∈ t.internalIntervals lo, ∃ qi ∈ qs.zipIdx,
        qi.2 = idx ∧ edgeWitness tips e.1 e.2 qi.1 r = true := by
  rw [code_bit _ _ _ hr, t.physical_witness_iff]
  constructor
  · rintro ⟨e,he,qi,hqi,r',hr',hw,hidx⟩
    have hrange := List.mem_range.mp hr'
    have hri : r'=r := by omega
    have hqiidx : qi.2=idx := by omega
    exact ⟨e,he,qi,hqi,hqiidx,hri ▸ hw⟩
  · rintro ⟨e,he,qi,hqi,hidx,hw⟩
    exact ⟨e,he,qi,hqi,r,List.mem_range.mpr hr,hw,by omega⟩
#print axioms Tree.code_physical_iff
end Nanuq.AdjacentCertificate
