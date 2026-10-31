import VertexDeletion
namespace Nanuq.RawBlock
open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem binary_degree_sum_le (N : RootedBinary V E X) (v : V) :
    N.graph.inDegree v + N.graph.outDegree v ≤ 3 := by
  by_cases hr : v = N.root
  · subst v
    rw [N.root_degrees.1,N.root_degrees.2]
    omega
  by_cases hl : ∃ x, N.leaf x = v
  · obtain ⟨x,rfl⟩ := hl
    rw [(N.leaf_degrees x).1,(N.leaf_degrees x).2]
    omega
  have hi := N.internal_degrees v hr (fun x hx => hl ⟨x,hx⟩)
  rcases hi with ⟨hi,ho⟩ | ⟨hi,ho⟩ <;> rw [hi,ho] <;> omega

/-- Distinct original incident edge IDs; no simple-graph projection. -/
theorem binary_incidence_bound (N : RootedBinary V E X) (v : V) :
    Set.ncard {e | N.graph.source e = v ∨ N.graph.target e = v} ≤ 3 := by
  classical
  have hu := Set.ncard_union_le {e | N.graph.source e = v} {e | N.graph.target e = v}
  have hs : Set.ncard {e | N.graph.source e = v} = N.graph.outDegree v := by
    have hset : {e | N.graph.source e = v} =
        (↑(Finset.univ.filter (fun e => N.graph.source e = v)) : Set E) := by
      ext e
      simp
    rw [hset,Set.ncard_coe_finset]
    rfl
  have ht : Set.ncard {e | N.graph.target e = v} = N.graph.inDegree v := by
    have hset : {e | N.graph.target e = v} =
        (↑(Finset.univ.filter (fun e => N.graph.target e = v)) : Set E) := by
      ext e
      simp
    rw [hset,Set.ncard_coe_finset]
    rfl
  rw [hs,ht] at hu
  exact hu.trans (by simpa [Nat.add_comm] using binary_degree_sum_le N v)
#print axioms binary_incidence_bound
end Nanuq.RawBlock
