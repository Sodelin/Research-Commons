import FiniteEdgeBridge
import FiniteProvider
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

/-- Actual integration with the frozen finite provider. The returned Tree
and mask are constructed from pruning/re-rooting; its exact edge-witness
semantics and finite checker success are proved, not supplied as premises. -/
theorem finite_restriction (n mask : Nat) (keep : Nat → Bool) (t : LTree)
    (hleaves : t.leaves = occurrenceLabels n mask)
    (hcount : 3 ≤ (retained n keep).length ∧ (retained n keep).length ≤ 6) :
    ∃ (newMask : Nat) (T : Tree),
      newMask < 2^(retained n keep).length ∧
      T.size = (occurrenceLabels (retained n keep).length newMask).length - 1 ∧
      checkPattern (retained n keep).length (quartets (retained n keep).length)
        (T.summary (edgeContribution (occurrenceLabels (retained n keep).length newMask)
          (quartets (retained n keep).length)) 1) = true ∧
      ∀ a b c d, a∈retained n keep → b∈retained n keep → c∈retained n keep → d∈retained n keep →
        a≠b → c≠d → ∀ (q : Quartet) r,
        q.parts r = ((retained n keep).idxOf a,(retained n keep).idxOf b,
          (retained n keep).idxOf c,(retained n keep).idxOf d) →
        ((∃ e∈T.internalIntervals 1,
          edgeWitness (occurrenceLabels (retained n keep).length newMask) e.1 e.2 q r = true) ↔
          t.Witness [] a b c d) := by
  let P := retained n keep
  obtain ⟨x,rest,newMask,hbound,hfull,hl,hw⟩ :=
    canonical_restriction n mask keep t hleaves (by omega)
  have hsize : rest.erase.size = (occurrenceLabels P.length newMask).length-1 := by
    rw [erase_size rest hfull]
    change rest.leaves.length = (occurrenceLabels (retained n keep).length newMask).length-1
    rw [hl,List.length_cons]
    omega
  refine ⟨newMask,rest.erase,hbound,hsize,
    all_adjacent_copy_trees P.length newMask hcount hbound rest.erase hsize,?_⟩
  intro a b c d ha hb hc hd hab hcd q r hparts
  have hab' : P.idxOf a ≠ P.idxOf b := by intro h; exact hab ((List.idxOf_inj ha).mp h)
  have hcd' : P.idxOf c ≠ P.idxOf d := by intro h; exact hcd ((List.idxOf_inj hc).mp h)
  have hf := whole_first_edgeWitness x rest hfull q r
    (P.idxOf a) (P.idxOf b) (P.idxOf c) (P.idxOf d) hparts hab' hcd'
  rw [hl]
  exact hf.symm.trans (hw a b c d ha hb hc hd)

#print axioms finite_restriction
end Nanuq.Restriction
