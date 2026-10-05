import G1SharpCoreCombLSA

/-! Actual RootedBinary admission and exact hybrid census for EVERY n≥4.
No graph-size or sharpness predicate is supplied to the construction. -/
namespace G1SharpCoreCombAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition G1SharpCoreCombDegrees G1SharpCoreCombRootedness G1SharpCoreCombLSA
open scoped Classical

def network (n : Nat) (hn : 4 ≤ n) : RootedBinary (Vertex n) (Edge n) (Fin n) where
  graph := graph n
  root := root n hn
  leaf := taxon n
  at_least_two_taxa := by simp; omega
  root_degrees := by
    change (graph n).inDegree (.inl (⟨0,by omega⟩,0)) = 0 ∧ (graph n).outDegree (.inl (⟨0,by omega⟩,0)) = 2
    rw [module_indegree,module_outdegree]
    simp
  leaf_degrees := leaf_degrees n hn
  internal_degrees := by
    intro v hr hl
    cases v with
    | inr x => exact False.elim (hl x rfl)
    | inl pair =>
      rcases pair with ⟨i,k⟩
      have hi : i.val ≠ 0 ∨ k.val ≠ 0 := by
        by_contra h
        push_neg at h
        apply hr
        simp only [root,Sum.inl.injEq,Prod.mk.injEq,Fin.ext_iff,Fin.val_mk,Fin.val_zero]
        exact h
      change ((graph n).inDegree (.inl (i,k)) = 1 ∧ (graph n).outDegree (.inl (i,k)) = 2) ∨
        ((graph n).inDegree (.inl (i,k)) = 2 ∧ (graph n).outDegree (.inl (i,k)) = 1)
      rw [module_indegree,module_outdegree]
      fin_cases k <;> simp_all
  acyclic := graph_acyclic n
  rooted := original_rooted n hn
  least_stable := original_least_stable n hn

theorem original_module_hybrid (n : Nat) (hn : 4 ≤ n) (i : Module n) (k : LocalVertex) :
    (network n hn).graph.IsHybrid (.inl (i,k)) ↔ k = 3 ∨ k = 4 := by
  change ((graph n).inDegree (.inl (i,k)) = 2 ∧ (graph n).outDegree (.inl (i,k)) = 1) ↔ _
  rw [module_indegree,module_outdegree]
  fin_cases k <;> simp

theorem exact_hybrid_count (n : Nat) (hn : 4 ≤ n) :
    (G1ReducedCoreCounts.hybrids (network n hn)).card = 2*n-2 := by
  have hv := (G1BinaryCoreBudgets.actual_binary_vertex_edge_census (network n hn)).1
  rw [Fintype.card_fin,exact_vertex_count n hn] at hv
  omega

#print axioms network
#print axioms exact_hybrid_count
end G1SharpCoreCombAdmission
