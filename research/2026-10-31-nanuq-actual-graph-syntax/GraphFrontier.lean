import GraphQuartet
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

def BinarySyntax.frontier : BinarySyntax V → List V
  | .tip v => [v]
  | .fork _ l r => l.frontier ++ r.frontier

theorem Represents.mem_frontier_iff {G : EdgeGraph V E} {t : BinarySyntax V} {v : V}
    (h : Represents G t v) (x : V) :
    x ∈ t.frontier ↔ x ∈ t.nodes ∧ G.outDegree x = 0 := by
  induction h with
  | tip v hv =>
    simp only [BinarySyntax.frontier,BinarySyntax.nodes,List.mem_singleton]
    exact ⟨fun hx => ⟨hx,hx ▸ hv⟩,fun h => h.1⟩
  | @fork v e f hne he hf hall l r hl hr il ir =>
    have hv : G.outDegree v ≠ 0 := by
      classical
      intro hz
      have hem : e ∈ Finset.univ.filter (fun g => G.source g = v) := by simp [he]
      have hs : Finset.univ.filter (fun g => G.source g = v) = ∅ := Finset.card_eq_zero.mp hz
      rw [hs] at hem
      exact Finset.notMem_empty e hem
    simp only [BinarySyntax.frontier,List.mem_append,il,ir,BinarySyntax.nodes,List.mem_cons]
    constructor
    · rintro (⟨hx,hs⟩ | ⟨hx,hs⟩)
      · exact ⟨Or.inr (Or.inl hx),hs⟩
      · exact ⟨Or.inr (Or.inr hx),hs⟩
    · rintro ⟨hx,hs⟩
      rcases hx with hx | hx | hx
      · subst x; exact False.elim (hv hs)
      · exact Or.inl ⟨hx,hs⟩
      · exact Or.inr ⟨hx,hs⟩

/-- Every original terminal occurrence appears at a syntax tip; no extra tips. -/
theorem Represents.frontier_iff_reachable_sink {G : EdgeGraph V E}
    {t : BinarySyntax V} {v : V} (h : Represents G t v) (x : V) :
    x ∈ t.frontier ↔ G.DReach v x ∧ G.outDegree x = 0 := by
  rw [h.mem_frontier_iff,h.mem_nodes_iff]

/-- Exact partitions restricted to actual terminal occurrences, ready for a
separate label map. No injectivity of the eventual taxon label map is assumed. -/
theorem edge_frontier_partition {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    {t : BinarySyntax V} (ht : Represents G t root) (e : E) :
    ∃ u, Below t u ∧ ∀ x, G.outDegree x = 0 →
      (G.ReachWithout e (G.target e) x ↔ x ∈ u.frontier) ∧
      (G.ReachWithout e (G.source e) x ↔ x ∉ u.frontier) := by
  obtain ⟨u,hu,hrep⟩ := edge_has_subtree ht e ((ht.mem_nodes_iff _).mpr (hr _))
  refine ⟨u,hu,fun x hx => ?_⟩
  have hm : x ∈ u.frontier ↔ G.DReach (G.target e) x := by
    rw [hrep.frontier_iff_reachable_sink]; simp only [hx,and_true]
  exact ⟨(target_cut_iff G ha hui e x).trans hm.symm,
    (source_cut_iff G ha hui root hr e x).trans (not_congr hm.symm)⟩

#print axioms Represents.frontier_iff_reachable_sink
#print axioms edge_frontier_partition
end Nanuq.GraphSyntax
