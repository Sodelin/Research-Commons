import GraphUnfold
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

def BinarySyntax.nodes : BinarySyntax V → List V
  | .tip v => [v]
  | .fork v l r => v :: (l.nodes ++ r.nodes)

theorem sink_reach_eq (G : EdgeGraph V E) (v x : V)
    (hv : G.outDegree v = 0) (h : G.DReach v x) : x = v := by
  classical
  have hz : Finset.univ.filter (fun e => G.source e = v) = ∅ := Finset.card_eq_zero.mp hv
  induction h with
  | refl => rfl
  | @tail a b hp hs ih =>
    obtain ⟨e, he, ht⟩ := hs
    have hm : e ∈ Finset.univ.filter (fun e => G.source e = v) := by simp [he, ih]
    rw [hz] at hm
    exact False.elim (Finset.notMem_empty e hm)

/-- Exact vertex reachability, not an assumed graph-to-syntax certificate. -/
theorem Represents.mem_nodes_iff {G : EdgeGraph V E} {t : BinarySyntax V} {v : V}
    (h : Represents G t v) (x : V) : x ∈ t.nodes ↔ G.DReach v x := by
  induction h with
  | tip v hv =>
    simp only [BinarySyntax.nodes, List.mem_singleton]
    exact ⟨fun he => he ▸ Relation.ReflTransGen.refl,
      fun hr => sink_reach_eq G v x hv hr⟩
  | @fork v e f hne he hf hall l r hl hr il ir =>
    simp only [BinarySyntax.nodes, List.mem_cons, List.mem_append]
    constructor
    · rintro (hx | hx | hx)
      · subst x; exact .refl
      · exact (il.mp hx).head ⟨e, he, rfl⟩
      · exact (ir.mp hx).head ⟨f, hf, rfl⟩
    · intro hx
      rcases hx.cases_head with heq | ⟨a, ⟨g, hg, ht⟩, ha⟩
      · exact Or.inl heq.symm
      · rcases hall g hg with hge | hgf
        · subst g
          exact Or.inr (Or.inl (il.mpr (ht ▸ ha)))
        · subst g
          exact Or.inr (Or.inr (ir.mpr (ht ▸ ha)))

#print axioms Represents.mem_nodes_iff
end Nanuq.GraphSyntax
