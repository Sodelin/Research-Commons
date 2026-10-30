import MaskDispatch_3
import MaskDispatch_4
import MaskDispatch_5
import MaskDispatch_6
import QueryCertificates
set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate
theorem all_adjacent_copy_trees (n mask : Nat) (hn : 3 ≤ n ∧ n ≤ 6) (hm : mask < 2^n)
    (t : Tree) (hs : t.size = (occurrenceLabels n mask).length - 1) :
    checkPattern n (quartets n) (t.summary (edgeContribution (occurrenceLabels n mask) (quartets n)) 1) = true := by
  rcases hn with ⟨hlo,hhi⟩
  interval_cases n
  · exact all_masks_3 mask hm t hs
  · exact all_masks_4 mask hm t hs
  · exact all_masks_5 mask hm t hs
  · exact all_masks_6 mask hm t hs
#print axioms all_adjacent_copy_trees
end Nanuq.AdjacentCertificate
