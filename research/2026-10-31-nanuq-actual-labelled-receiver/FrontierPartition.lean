import EncodeWitness
set_option debug.skipKernelTC false
namespace Nanuq.GraphReceiver
open Nanuq.GraphSyntax Nanuq.Restriction Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem frontier_filter {G : EdgeGraph V E} {t : BinarySyntax V} {v : V}
    (h : Represents G t v) :
    t.frontier = t.nodes.filter (fun x => decide (G.outDegree x = 0)) := by
  induction h with
  | tip v hv => simp [BinarySyntax.frontier,BinarySyntax.nodes,hv]
  | @fork v e f hne he hf hall l r hl hr il ir =>
    have hv : G.outDegree v ≠ 0 := by
      classical
      intro hz
      have hem : e ∈ Finset.univ.filter (fun g => G.source g = v) := by simp [he]
      have hs : Finset.univ.filter (fun g => G.source g = v) = ∅ := Finset.card_eq_zero.mp hz
      rw [hs] at hem
      exact Finset.notMem_empty e hem
    simp [BinarySyntax.frontier,BinarySyntax.nodes,hv,il,ir]

theorem frontier_nodup {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) {t : BinarySyntax V} {v : V}
    (h : Represents G t v) : t.frontier.Nodup := by
  rw [frontier_filter h]
  exact (h.nodes_nodup ha hui).filter _

theorem Context.outside_iff {t u : BinarySyntax V} {out : List V}
    (hctx : Context t u out) (hn : t.frontier.Nodup) (x : V) :
    x ∈ out ↔ x ∈ t.frontier ∧ x ∉ u.frontier := by
  have hp := hctx.frontier_perm
  have hnd : (u.frontier ++ out).Nodup := hp.nodup_iff.mp hn
  have hd := (List.nodup_append.mp hnd).2.2
  constructor
  · intro hx
    exact ⟨hp.mem_iff.mpr (List.mem_append_right _ hx),fun hu => hd x hu x hx rfl⟩
  · rintro ⟨hx,hu⟩
    rcases List.mem_append.mp (hp.mem_iff.mp hx) with h | h
    · exact False.elim (hu h)
    · exact h

#print axioms Context.outside_iff
end Nanuq.GraphReceiver
