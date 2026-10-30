import AnchorTransport
import ConstructTransport
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

theorem coefficient_transport (n : Nat) (keep : Nat → Bool) (T U : Tree) (tips tips' : List Nat)
    (ht : EdgeTransport n keep T U tips tips') (p q i j : Nat)
    (hn : 2≤n) (hi : i<n) (hj : j<n) (hpq : p≠q)
    (hp : p∈retained n keep) (hq : q∈retained n keep)
    (ha : i∈retained n keep) (hb : (i+1)%n∈retained n keep)
    (hc : j∈retained n keep) (hd : (j+1)%n∈retained n keep) :
    alpha n (quartets n) (codedPattern T tips n) p q i j =
      alpha (retained n keep).length (quartets (retained n keep).length)
        (codedPattern U tips' (retained n keep).length)
        ((retained n keep).idxOf p) ((retained n keep).idxOf q)
        ((retained n keep).idxOf i) ((retained n keep).idxOf j) := by
  have hbg := retained_gap_next n keep i ((i+1)%n) (range_gap n i hn hi)
    (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2
  have hdg := retained_gap_next n keep j ((j+1)%n) (range_gap n j hn hj)
    (List.mem_filter.mp hc).2 (List.mem_filter.mp hd).2
  have hac := anchor_transport n keep T U tips tips' ht p q i j hp hq ha hc hpq
  have hbd := anchor_transport n keep T U tips tips' ht p q ((i+1)%n) ((j+1)%n) hp hq hb hd hpq
  have had := anchor_transport n keep T U tips tips' ht p q i ((j+1)%n) hp hq ha hd hpq
  have hbc := anchor_transport n keep T U tips tips' ht p q ((i+1)%n) j hp hq hb hc hpq
  simp only [alpha]
  rw [← hbg,← hdg,← hac,← hbd,← had,← hbc]

theorem all_size_anchor_nonnegative (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (p q i j : Nat) (hp : p<n) (hq : q<n) (hi : i<n) (hj : j<n) (hpq : p<q) (hij : i<j) :
    0≤alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n) p q i j := by
  let keep := queryKeep i ((i+1)%n) j ((j+1)%n) p q
  have hcount : 3≤(retained n keep).length ∧ (retained n keep).length≤6 :=
    ⟨retained_boundary_ge_three n i j p q hn hi hj hij,
      retained_query_le_six n i ((i+1)%n) j ((j+1)%n) p q⟩
  obtain ⟨newMask,U,hbound,hsize,hcheck,ht⟩ := construct_transport n mask keep T (by omega) hs hcount
  have hn0 : 0<n := by omega
  have hA : i∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hi (by simp)
  have hB : (i+1)%n∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ (Nat.mod_lt _ hn0) (by simp)
  have hC : j∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hj (by simp)
  have hD : (j+1)%n∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ (Nat.mod_lt _ hn0) (by simp)
  have hP : p∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hp (by simp)
  have hQ : q∈retained n keep := retained_query_mem _ _ _ _ _ _ _ _ hq (by simp)
  rw [coefficient_transport n keep T U (occurrenceLabels n mask)
    (occurrenceLabels (retained n keep).length newMask) ht p q i j (by omega) hi hj
    (by omega) hP hQ hA hB hC hD]
  exact nonneg_of_check _ _ _ hcheck _ _ _ _
    (List.idxOf_lt_length_iff.mpr hP) (List.idxOf_lt_length_iff.mpr hQ)
    (List.idxOf_lt_length_iff.mpr hA) (List.idxOf_lt_length_iff.mpr hC)
    (retained_rank_strict n keep p q hP hQ hpq) (retained_rank_strict n keep i j hA hC hij)

#print axioms coefficient_transport
#print axioms all_size_anchor_nonnegative
end Nanuq.Restriction
