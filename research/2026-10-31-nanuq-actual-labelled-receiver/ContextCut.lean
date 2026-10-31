import FrontierPartition
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem context_partition_for_edge {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    {t u : BinarySyntax V} {inner : List V} (ht : Represents G t root)
    (hc : Context t u inner) (e : E) (hrep : Represents G u (G.target e)) :
    (∀ x, x ∈ u.frontier → G.outDegree x = 0) ∧
      (∀ x, x ∈ inner → G.outDegree x = 0) ∧
      ∀ x, G.outDegree x = 0 →
        (G.ReachWithout e (G.target e) x ↔ x ∈ u.frontier) ∧
        (G.ReachWithout e (G.source e) x ↔ x ∈ inner) := by
  have hn := frontier_nodup ha hui ht
  refine ⟨?_,?_,?_⟩
  · intro x hx; exact ((hrep.mem_frontier_iff x).mp hx).2
  · intro x hx
    have hm := ((hc.outside_iff hn x).mp hx).1
    exact ((ht.mem_frontier_iff x).mp hm).2
  · intro x hx
    have hm : x ∈ u.frontier ↔ G.DReach (G.target e) x := by
      rw [hrep.frontier_iff_reachable_sink]; simp only [hx,and_true]
    have hglob : x ∈ t.frontier := (ht.frontier_iff_reachable_sink x).mpr ⟨hr x,hx⟩
    have hout : x ∈ inner ↔ x ∉ u.frontier := by
      rw [hc.outside_iff hn x]; simp only [hglob,true_and]
    exact ⟨(target_cut_iff G ha hui e x).trans hm.symm,
      ((source_cut_iff G ha hui root hr e x).trans (not_congr hm.symm)).trans hout.symm⟩

#print axioms context_partition_for_edge
end Nanuq.GraphReceiver
