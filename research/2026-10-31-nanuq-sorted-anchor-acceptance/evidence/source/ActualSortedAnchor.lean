import SortedQueryMean
import ActualCanonicalDistinctReceiver
import NanuqActualFullAnchor

/-! UNCOMPILED source-facing use of the exact sorted-query comparison.
The displayed-resolution hypothesis below is discharged by the qualified
actual canonical receiver, not a new original-network premise. Anchor
comparison requires distinct anchors; the source diagonal is separately 0. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualFinite
open Nanuq.Source Nanuq.Quartet Nanuq.AdjacentCertificate Nanuq.Restriction
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
variable (hs : T.size=(occurrenceLabels n mask).length-1)
variable (hm : ∀ q : Fin 4 ↪ X,
  N.rawQuartetMean q=distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
    (coordinateQuartet (fun i => (rank (q i)).val))))

include hs hm in
theorem actual_sorted_query_mean (q : Fin 4 ↪ X) :
    (twiceMean (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      (rank (q 0)).val (rank (q 1)).val (rank (q 2)).val (rank (q 3)).val : ℚ)=
      2*N.rawQuartetMean q := by
  rw [hm q]
  exact sorted_query_mean n mask T hs (q.trans rank.toEmbedding)

include hs hm in
theorem actual_sorted_anchor (v : Fin 4 → X) (hpq : v 2≠v 3) :
    (anchor (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      (rank (v 2)).val (rank (v 3)).val (rank (v 0)).val (rank (v 1)).val : ℚ)=
      N.actualTupleAnchor v := by
  classical
  have he (i j : Fin 4) : (rank (v i)).val=(rank (v j)).val ↔ v i=v j := by
    constructor
    · exact fun h => rank.injective (Fin.ext h)
    · exact fun h => congrArg (fun x => (rank x).val) h
  by_cases h01 : v 0=v 1
  · simp [anchor,RootedBinary.actualTupleAnchor,Nanuq.PortPatterns.tupleAnchor,he,h01]
  by_cases h02 : v 0=v 2
  · by_cases h13 : v 1=v 3 <;>
      simp_all [anchor,RootedBinary.actualTupleAnchor,Nanuq.PortPatterns.tupleAnchor,he,eq_comm]
  by_cases h03 : v 0=v 3
  · by_cases h12 : v 1=v 2 <;>
      simp_all [anchor,RootedBinary.actualTupleAnchor,Nanuq.PortPatterns.tupleAnchor,he,eq_comm]
  by_cases h12 : v 1=v 2
  · simp_all [anchor,RootedBinary.actualTupleAnchor,Nanuq.PortPatterns.tupleAnchor,he,eq_comm]
  by_cases h13 : v 1=v 3
  · simp_all [anchor,RootedBinary.actualTupleAnchor,Nanuq.PortPatterns.tupleAnchor,he,eq_comm]
  have hi : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hx := actual_sorted_query_mean N n mask rank T hs hm ⟨v,hi⟩
  simpa [anchor,RootedBinary.actualTupleAnchor,RootedBinary.actualTupleMean,
    Nanuq.PortPatterns.tupleAnchor,he,h01,h02,h03,h12,h13,hpq,hi] using hx

theorem actual_diagonal_anchor (v : Fin 4 → X) (hpq : v 2=v 3) :
    N.actualTupleAnchor v=0 := by
  classical
  simp [RootedBinary.actualTupleAnchor,Nanuq.PortPatterns.tupleAnchor,hpq]

#print axioms actual_sorted_query_mean
#print axioms actual_sorted_anchor
end Nanuq.ActualFinite
