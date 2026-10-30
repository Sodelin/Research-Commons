import SixLabels
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

theorem retained_rank_strict (n : Nat) (keep : Nat → Bool) (a b : Nat)
    (ha : a∈retained n keep) (hb : b∈retained n keep) (hab : a<b) :
    (retained n keep).idxOf a < (retained n keep).idxOf b := by
  let P := retained n keep
  have hsorted : P.Pairwise (· < ·) := (List.pairwise_lt_range (n:=n)).filter keep
  have hai : P.idxOf a<P.length := List.idxOf_lt_length_iff.mpr ha
  have hbi : P.idxOf b<P.length := List.idxOf_lt_length_iff.mpr hb
  change P.idxOf a < P.idxOf b
  by_contra h
  have hne : P.idxOf a≠P.idxOf b := by intro he; have := (List.idxOf_inj ha).mp he; omega
  have hba : P.idxOf b<P.idxOf a := by omega
  have ht := List.pairwise_iff_getElem.mp hsorted _ _ hbi hai hba
  simp only [List.getElem_idxOf] at ht
  omega

#print axioms retained_rank_strict
end Nanuq.Restriction
