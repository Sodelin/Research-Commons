import StoredMeanCoordinates
import RestrictionEndpoints

/-! UNCOMPILED. Exact original DISTINCT mean for a query in its literal
coordinate order, despite storage at the sorted quartet index. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualFinite
open Nanuq.AdjacentCertificate Nanuq.Restriction Nanuq.Quartet

theorem sorted_query_mean (n mask : Nat) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1) (q : Fin 4 ↪ Fin n) :
    (twiceMean (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      (q 0).val (q 1).val (q 2).val (q 3).val : ℚ)=
      2 * distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
        (coordinateQuartet (fun i => (q i).val))) := by
  obtain ⟨v,σ,hσ,hlookup⟩ := sorted_query_coordinates n q
  have hn (i j : Fin 4) (hij : i≠j) : (q i).val≠(q j).val := by
    intro h
    exact hij (q.injective (Fin.ext h))
  have hex := all_size_mean_exact n mask T hs
    (q 0).val (q 1).val (q 2).val (q 3).val
    (q 0).isLt (q 1).isLt (q 2).isLt (q 3).isLt
    (hn 0 1 (by decide)) (hn 0 2 (by decide)) (hn 0 3 (by decide))
    (hn 1 2 (by decide)) (hn 1 3 (by decide)) (hn 2 3 (by decide))
  have hat : quartetAt (quartets n) (q 0).val (q 1).val (q 2).val (q 3).val=
      coordinateQuartet v := by simp [quartetAt,hlookup]
  have hfun : (fun i => (q i).val)=(fun i => v (σ i)) := funext hσ
  have hm := finite_distinctMean_permutation T (occurrenceLabels n mask) v σ
  have hc := indexedPairMean_code T (occurrenceLabels n mask) (quartets n)
    (quartetIndex (quartets n) (q 0).val (q 1).val (q 2).val (q 3).val)
    v hlookup (σ 0) (σ 1)
  rw [← hσ 0,← hσ 1] at hc
  rw [hfun,hm,hc]
  rw [hat] at hex
  simpa only [codedPattern,mul_div_assoc] using hex

#print axioms sorted_query_mean
end Nanuq.ActualFinite
