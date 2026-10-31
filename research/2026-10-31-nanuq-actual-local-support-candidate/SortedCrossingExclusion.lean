import ActualCanonicalSortedAnchor

/-! UNCOMPILED all-size crossing exclusion at the EXACT sorted coordinates.
The source set equality below is the qualified actual receiver's output,
not a new admissibility hypothesis at the final source-facing endpoint. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualFinite
open Nanuq.AdjacentCertificate Nanuq.Restriction Nanuq.Quartet Nanuq.Source
open scoped Classical

theorem finite_sorted_crossing_absent (n mask : Nat) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (a b c d : Nat) (hab : a<b) (hbc : b<c) (hcd : c<d) (hd : d<n) :
    Resolution.xz_yw ∉ finiteResolutionSet T (occurrenceLabels n mask) ⟨a,b,c,d⟩ := by
  have hmem : (⟨a,b,c,d⟩ : Quartet) ∈ quartets n :=
    (mem_quartets_iff n _).mpr ⟨⟨hab,hbc,hcd⟩,hd⟩
  have hlook := query_lookup n a b c d ⟨a,b,c,d⟩ hmem (by
    intro z
    rfl)
  have hvalid := all_size_query_code_valid n mask T hs a b c d
    (by omega) (by omega) (by omega) hd
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  intro hc
  have hbit := (finiteResolutionSet_code T (occurrenceLabels n mask) (quartets n)
    (quartetIndex (quartets n) a b c d) ⟨a,b,c,d⟩ hlook Resolution.xz_yw).mp hc
  change (code (codedPattern T (occurrenceLabels n mask) n)
    (quartetIndex (quartets n) a b c d)).testBit 1=true at hbit
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hvalid
  rcases hvalid with h | h | h <;> rw [h] at hbit <;> norm_num at hbit

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem actual_sorted_crossing_absent (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (q : Fin 4 ↪ X)
    (h01 : (rank (q 0)).val<(rank (q 1)).val)
    (h12 : (rank (q 1)).val<(rank (q 2)).val)
    (h23 : (rank (q 2)).val<(rank (q 3)).val) :
    Resolution.xz_yw ∉ N.rawDisplayedQuartets q := by
  rw [hsets q]
  exact finite_sorted_crossing_absent n mask T hs _ _ _ _ h01 h12 h23 (rank (q 3)).isLt

end Nanuq.ActualFinite
