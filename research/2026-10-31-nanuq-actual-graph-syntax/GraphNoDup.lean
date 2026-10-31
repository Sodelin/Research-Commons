import GraphUnique
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem Represents.nodes_nodup {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) {t : BinarySyntax V} {v : V}
    (h : Represents G t v) : t.nodes.Nodup := by
  induction h with
  | tip v hv => simp [BinarySyntax.nodes]
  | @fork v e f hne he hf hall l r hl hr il ir =>
    have hnL : v ∉ l.nodes := by
      intro hm
      have hp := hl.mem_nodes_iff v |>.mp hm
      exact no_edge_return G ha e (by simpa only [he] using hp)
    have hnR : v ∉ r.nodes := by
      intro hm
      have hp := hr.mem_nodes_iff v |>.mp hm
      exact no_edge_return G ha f (by simpa only [hf] using hp)
    have hd : List.Disjoint l.nodes r.nodes := by
      intro x hx hy
      exact hne (first_edge_unique G ha hui e f (he.trans hf.symm)
        ((hl.mem_nodes_iff x).mp hx) ((hr.mem_nodes_iff x).mp hy))
    simp only [BinarySyntax.nodes, List.nodup_cons, List.mem_append, not_or]
    exact ⟨⟨hnL, hnR⟩, List.nodup_append.mpr ⟨il, ir, fun a ha b hb heq => hd ha (heq ▸ hb)⟩⟩

/-- The root expansion contains every actual graph vertex exactly once.
Rootedness is actual reachability, not an assumed syntax enumeration. -/
theorem rooted_exact_enumeration (G : EdgeGraph V E) (ha : G.Acyclic)
    (hui : Function.Injective G.target) (hb : ∀ v, G.outDegree v = 0 ∨ G.outDegree v = 2)
    (root : V) (hroot : ∀ x, G.DReach root x) :
    ∃ t, Represents G t root ∧ t.nodes.Nodup ∧ ∀ x, x ∈ t.nodes := by
  obtain ⟨t, ht⟩ := exists_represents G ha hb root
  exact ⟨t, ht, ht.nodes_nodup ha hui, fun x => (ht.mem_nodes_iff x).mpr (hroot x)⟩

#print axioms rooted_exact_enumeration
end Nanuq.GraphSyntax
