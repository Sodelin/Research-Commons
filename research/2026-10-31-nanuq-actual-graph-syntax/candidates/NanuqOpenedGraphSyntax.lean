import GraphFrontier
import NanuqActualOpenedRootedAdmission
set_option debug.skipKernelTC false

/-! UNCOMPILED source-specialization candidate. The graph premises below are
supplied by retained actual opened-tree lemmas, not new contour hypotheses.
The child-is-taxon premise is the existing cap interface; it is not asserted
for arbitrary original networks. Geometric leaf order remains open. -/
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

 theorem actual_opened_syntax (N : RootedBinary V E X)
    (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x) :
    ∃ t : BinarySyntax N.OpenedHybridVertex,
      Represents (N.openedHybridGraph hleaf) t (Sum.inl N.rootSkeletonRoot) ∧
      t.nodes.Nodup ∧ (∀ x, x ∈ t.nodes) ∧
      ∀ a b c d, (N.openedHybridGraph hleaf).HasQuartet a b c d ↔ SyntaxQuartet t a b c d := by
  classical
  have hb : ∀ v, (N.openedHybridGraph hleaf).outDegree v = 0 ∨
      (N.openedHybridGraph hleaf).outDegree v = 2 := by
    intro v
    by_cases hv : v = Sum.inl N.rootSkeletonRoot
    · subst v; exact Or.inr (N.opened_root_degrees hleaf).2
    · by_cases ht : ∃ t, N.openedTipVertex t = v
      · obtain ⟨t,rfl⟩ := ht
        exact Or.inl (N.opened_tip_degrees hleaf t).2
      · exact Or.inr (N.opened_internal_degrees hleaf v hv
          (fun t h => ht ⟨t,h⟩)).2
  exact actual_graph_syntax_provider (N.openedHybridGraph hleaf)
    (N.opened_hybrid_acyclic hleaf) (N.opened_hybrid_uniqueIncoming hleaf)
    hb (Sum.inl N.rootSkeletonRoot) (N.opened_hybrid_rooted hleaf)

#print axioms actual_opened_syntax
end Nanuq.GraphSyntax
