import NanuqActualNanuqAnchorBridge

/-! Galled ordinary-detour hypotheses force the hybrid outgoing edge to be
ordinary and bridge-like. The detour predicate is the existing graph API;
its equivalence to the source's marked simple-cycle convention remains a
separate admission bridge. No planar order is assumed here. -/
namespace Nanuq.Source.EdgeGraph
open scoped Classical
variable {V E : Type*} [Fintype E] [DecidableEq V] (G : EdgeGraph V E)

theorem outgoing_equal_of_degree_one {v : V} (hv : G.outDegree v = 1)
    (e f : E) (he : G.source e = v) (hf : G.source f = v) : e = f := by
  classical
  obtain ⟨g,hg,hu⟩ := Finset.card_eq_one_iff_existsUnique.mp hv
  exact (hu e (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)).trans
    (hu f (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩)).symm

theorem ordinary_walk_from_no_incidence_constant {v w : V}
    (hn : ∀ e, ¬ G.IsHybrid (G.target e) → G.source e ≠ v ∧ G.target e ≠ v)
    (h : G.UReach (fun e => ¬ G.IsHybrid (G.target e)) v w) : w = v := by
  induction h with
  | refl => rfl
  | @tail a b hp hs ih =>
    obtain ⟨e,he,hinc⟩ := hs
    rcases hinc with ⟨hs,_⟩ | ⟨_,ht⟩
    · exact False.elim ((hn e he).1 (hs.trans ih))
    · exact False.elim ((hn e he).2 (ht.trans ih))
end Nanuq.Source.EdgeGraph

namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_galled_hybrid_child_not_hybrid (hg : N.graph.GalledDetour)
    (e : E) (hh : N.graph.IsHybrid (N.graph.source e)) :
    ¬ N.graph.IsHybrid (N.graph.target e) := by
  intro hk
  obtain ⟨f,hf,hne⟩ := N.graph.hybrid_has_partner hk e
  have hd := hg (N.graph.target e) hk e f hne.symm rfl hf
  have hn (g : E) (ho : ¬ N.graph.IsHybrid (N.graph.target g)) :
      N.graph.source g ≠ N.graph.source e ∧ N.graph.target g ≠ N.graph.source e := by
    constructor
    · intro hs
      have heq := N.graph.outgoing_equal_of_degree_one hh.2 g e hs rfl
      exact ho (by rw [heq];exact hk)
    · intro ht
      exact ho (by rw [ht];exact hh)
  have hparents : N.graph.source f = N.graph.source e :=
    N.graph.ordinary_walk_from_no_incidence_constant hn
      (N.graph.ureach_mono (fun _ h => h.1) hd)
  exact hne (N.graph.outgoing_equal_of_degree_one hh.2 f e hparents rfl)
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_galled_hybrid_child_not_hybrid
