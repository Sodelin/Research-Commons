import Decorate
import QueryTransport
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

theorem occurrence_length_ge (n mask : Nat) : n ≤ (occurrenceLabels n mask).length := by
  simpa only [List.length_range,blocks,occurrenceLabels] using blocks_length_le (List.range n) mask.testBit

/-- No supplied transport certificate: pruning, whole-root rotations, rank
relabeling and the interval bridge construct and prove the entire transport. -/
theorem construct_transport (n mask : Nat) (keep : Nat → Bool) (T : Tree)
    (hn : 1≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (hcount : 3≤(retained n keep).length ∧ (retained n keep).length≤6) :
    ∃ (newMask : Nat) (U : Tree),
      newMask<2^(retained n keep).length ∧
      U.size=(occurrenceLabels (retained n keep).length newMask).length-1 ∧
      checkPattern (retained n keep).length (quartets (retained n keep).length)
        (codedPattern U (occurrenceLabels (retained n keep).length newMask) (retained n keep).length)=true ∧
      EdgeTransport n keep T U (occurrenceLabels n mask)
        (occurrenceLabels (retained n keep).length newMask) := by
  let tips := occurrenceLabels n mask
  let P := retained n keep
  have hlen : 1≤tips.length := Nat.le_trans hn (occurrence_length_ge n mask)
  obtain ⟨newMask,U,hbound,hsize,hcheck,hphysical⟩ := finite_restriction n mask keep
    (wholeDecorate T tips) (wholeDecorate_leaves T tips hlen hs) hcount
  refine ⟨newMask,U,hbound,hsize,hcheck,?_⟩
  intro q hq hqP r hr
  rcases hparts : q.parts r with ⟨a,b,c,d⟩
  have hv := ordered_parts q ((mem_quartets_iff n q).mp hq).1 r a b c d hparts
  have hp' := relabel_parts P.idxOf q r a b c d hparts
  have hnew := hphysical a b c d (hqP a hv.1) (hqP b hv.2.1) (hqP c hv.2.2.1)
    (hqP d hv.2.2.2.1) hv.2.2.2.2.1 hv.2.2.2.2.2 (relabelQuartet P.idxOf q) r hp'
  have hold := wholeDecorate_edgeWitness T tips hlen hs q r a b c d hparts
    hv.2.2.2.2.1 hv.2.2.2.2.2
  exact hold.symm.trans hnew.symm

#print axioms construct_transport
end Nanuq.Restriction
