import ResolutionMeanCoordinates
import QueryExists

/-! UNCOMPILED finite coordinate bijection derived from the actual query
set. This is not a new geometric order or arbitrary taxon permutation. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualFinite
open Nanuq.Restriction Nanuq.AdjacentCertificate
open scoped Classical

theorem tuple_range_iff (v : Fin 4 → Nat) (z : Nat) :
    (∃ i, v i=z) ↔ z∈[v 0,v 1,v 2,v 3] := by
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · intro hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with h | h | h | h
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
    · exact ⟨3,h.symm⟩

theorem equal_range_permutation (v w : Fin 4 ↪ Nat)
    (h : ∀ z, (∃ i, v i=z) ↔ ∃ j, w j=z) :
    ∃ σ : Equiv.Perm (Fin 4), ∀ i, v i=w (σ i) := by
  let f : Fin 4 → Fin 4 := fun i => Classical.choose ((h (v i)).mp ⟨i,rfl⟩)
  have hf (i : Fin 4) : w (f i)=v i := Classical.choose_spec ((h (v i)).mp ⟨i,rfl⟩)
  have hi : Function.Injective f := by
    intro i j hij
    exact v.injective ((hf i).symm.trans ((congrArg w hij).trans (hf j)))
  have hs : Function.Surjective f := by
    intro j
    obtain ⟨i,hi⟩ := (h (w j)).mpr ⟨j,rfl⟩
    exact ⟨i,w.injective ((hf i).trans hi)⟩
  exact ⟨Equiv.ofBijective f ⟨hi,hs⟩,fun i => (hf i).symm⟩

theorem sorted_query_coordinates (n : Nat) (q : Fin 4 ↪ Fin n) :
    ∃ (v : Fin 4 ↪ Nat) (σ : Equiv.Perm (Fin 4)),
      (∀ i, (q i).val=v (σ i)) ∧
      (quartets n)[quartetIndex (quartets n) (q 0).val (q 1).val (q 2).val (q 3).val]?=
        some (coordinateQuartet v) := by
  let query : Fin 4 ↪ Nat := ⟨fun i => (q i).val,fun _ _ h => q.injective (Fin.ext h)⟩
  have hn (i j : Fin 4) (hij : i≠j) : query i≠query j := fun h => hij (query.injective h)
  obtain ⟨Q,hQ,hset⟩ := query_quartet_exists n (query 0) (query 1) (query 2) (query 3)
    (q 0).isLt (q 1).isLt (q 2).isLt (q 3).isLt
    (hn 0 1 (by decide)) (hn 0 2 (by decide)) (hn 0 3 (by decide))
    (hn 1 2 (by decide)) (hn 1 3 (by decide)) (hn 2 3 (by decide))
  have ho := ((mem_quartets_iff n Q).mp hQ).1
  have hi : Function.Injective (![Q.a,Q.b,Q.c,Q.d] : Fin 4 → Nat) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [QuartetOrdered] <;> omega
  let v : Fin 4 ↪ Nat := ⟨![Q.a,Q.b,Q.c,Q.d],hi⟩
  have hr : ∀ z, (∃ i, query i=z) ↔ ∃ j, v j=z := by
    intro z
    rw [tuple_range_iff,tuple_range_iff]
    exact (hset z).symm
  obtain ⟨σ,hσ⟩ := equal_range_permutation query v hr
  exact ⟨v,σ,hσ,query_lookup n (query 0) (query 1) (query 2) (query 3) Q hQ hset⟩

#print axioms sorted_query_coordinates
end Nanuq.ActualFinite
