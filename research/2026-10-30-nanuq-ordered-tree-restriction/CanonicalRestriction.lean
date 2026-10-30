import Relabel
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

def retained (n : Nat) (keep : Nat → Bool) : List Nat := (List.range n).filter keep

/-- Arbitrary-size adjacent-copy tree syntax restricts to ONE canonical
adjacent-copy mask preserving all retained quartet cut witnesses exactly.
No bound on the original n or duplication count is assumed. -/
theorem canonical_restriction (n mask : Nat) (keep : Nat → Bool) (t : LTree)
    (hleaves : t.leaves = Nanuq.AdjacentCertificate.occurrenceLabels n mask)
    (hcount : 2 ≤ (retained n keep).length) :
    ∃ x rest newMask,
      newMask < 2^(retained n keep).length ∧ rest.Full ∧
      Nanuq.AdjacentCertificate.occurrenceLabels (retained n keep).length newMask = x :: rest.leaves ∧
      ∀ a b c d, a∈retained n keep → b∈retained n keep → c∈retained n keep → d∈retained n keep →
        ((LTree.fork (.tip x) rest).Witness []
          ((retained n keep).idxOf a) ((retained n keep).idxOf b)
          ((retained n keep).idxOf c) ((retained n keep).idxOf d) ↔ t.Witness [] a b c d) := by
  let P := retained n keep
  have hnodup : P.Nodup := (List.nodup_range (n := n)).filter keep
  have hf : t.leaves.filter keep = blocks P mask.testBit := by
    rw [hleaves]
    exact blocks_filter (List.range n) mask.testBit keep
  have hsize : 2 ≤ (t.leaves.filter keep).length := by
    rw [hf]
    exact Nat.le_trans hcount (blocks_length_le P mask.testBit)
  obtain ⟨x,rest,hrest,hl,hw⟩ := restriction_representation keep t hsize
  refine ⟨P.idxOf x,rest.map P.idxOf,restrictedMask P mask.testBit,
    restrictedMask_bound P mask.testBit,full_map P.idxOf rest hrest,?_,?_⟩
  · calc
      Nanuq.AdjacentCertificate.occurrenceLabels P.length (restrictedMask P mask.testBit) =
          (blocks P mask.testBit).map P.idxOf := (restricted_blocks_canonical P hnodup mask.testBit).symm
      _ = (t.leaves.filter keep).map P.idxOf := congrArg (List.map P.idxOf) hf.symm
      _ = (x :: rest.leaves).map P.idxOf := congrArg (List.map P.idxOf) hl
      _ = P.idxOf x :: (rest.map P.idxOf).leaves := by simp only [List.map_cons,leaves_map]
  · intro a b c d ha hb hc hd
    have hka := (List.mem_filter.mp ha).2
    have hkb := (List.mem_filter.mp hb).2
    have hkc := (List.mem_filter.mp hc).2
    have hkd := (List.mem_filter.mp hd).2
    have hm := witness_map_rank P (LTree.fork (.tip x) rest) [] a b c d ha hb hc hd
    simp only [LTree.map,List.map_nil] at hm
    exact hm.trans (hw a b c d hka hkb hkc hkd)

#print axioms canonical_restriction
end Nanuq.Restriction
