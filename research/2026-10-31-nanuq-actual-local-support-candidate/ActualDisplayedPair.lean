import ActualCanonicalSortedAnchor

/-! UNCOMPILED exact arbitrary-coordinate pair support bridge. The closed
three-resolution identity uses the ORIGINAL uniform DISTINCT mean; empty
sets are explicitly excluded by the actual source theorem. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualFinite
open Nanuq.Source Nanuq.Quartet Nanuq.AdjacentCertificate Nanuq.Restriction

/-- Eight finite subsets, with the empty case guarded. Kernel reduction only. -/
theorem distinctMean_lt_one_iff_first : ∀ R : Finset Resolution,
    R.Nonempty → (distinctMean R < 1 ↔ Resolution.xy_zw ∈ R) := by
  decide +kernel

open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem actual_displayedPair_iff (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hm : ∀ q : Fin 4 ↪ X,
      N.rawQuartetMean q=distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
        (coordinateQuartet (fun i => (rank (q i)).val))))
    (q : Fin 4 ↪ X) :
    displayedPair (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      (rank (q 0)).val (rank (q 1)).val (rank (q 2)).val (rank (q 3)).val=true ↔
      Resolution.xy_zw ∈ N.rawDisplayedQuartets q := by
  have hn (a b : Fin 4) (hab : a≠b) : (rank (q a)).val≠(rank (q b)).val := by
    intro he
    exact hab (q.injective (rank.injective (Fin.ext he)))
  have hv := all_size_query_code_valid n mask T hs
    (rank (q 0)).val (rank (q 1)).val (rank (q 2)).val (rank (q 3)).val
    (rank (q 0)).isLt (rank (q 1)).isLt (rank (q 2)).isLt (rank (q 3)).isLt
    (hn 0 1 (by decide)) (hn 0 2 (by decide)) (hn 0 3 (by decide))
    (hn 1 2 (by decide)) (hn 1 3 (by decide)) (hn 2 3 (by decide))
  rw [←twiceMean_lt_two_iff _ _ _ _ _ _ hv]
  have he := actual_sorted_query_mean N n mask rank T hs hm q
  have hr : N.rawQuartetMean q<1 ↔ Resolution.xy_zw ∈ N.rawDisplayedQuartets q :=
    distinctMean_lt_one_iff_first _ (N.rawDisplayedQuartets_nonempty q)
  rw [←hr]
  constructor
  · intro h
    have hc : (twiceMean (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      (rank (q 0)).val (rank (q 1)).val (rank (q 2)).val (rank (q 3)).val : ℚ)<2 := by
      exact_mod_cast h
    rw [he] at hc
    linarith
  · intro h
    have hc : (twiceMean (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      (rank (q 0)).val (rank (q 1)).val (rank (q 2)).val (rank (q 3)).val : ℚ)<2 := by
      rw [he]
      linarith
    exact_mod_cast hc

end Nanuq.ActualFinite
