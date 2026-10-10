import SourceQuartetRelation

/-!
Fixed-vertex transport of individual edge occurrences and actual edge-cut
quartets. Cloud G6 source prototype, 8 October 2026. COMPILER UNCHECKED.
The bijection and its endpoint equations are primitive graph data, not a
desired quartet or target equality. The actual two-port switching consumer
must derive these data from its original source; source suppression is separate.
-/

namespace UnifiedLean.G6.EdgeOccurrenceTransport

open Nanuq.Source

universe u v w
variable {V : Type u} {E : Type v} {F : Type w}

/-- An equivalence of actual edge IDs that fixes their original endpoints. -/
structure OccurrenceEquiv (G : EdgeGraph V E) (H : EdgeGraph V F) where
  edge : E ≃ F
  source : ∀ e, H.source (edge e) = G.source e
  target : ∀ e, H.target (edge e) = G.target e

namespace OccurrenceEquiv
variable {G : EdgeGraph V E} {H : EdgeGraph V F} (φ : OccurrenceEquiv G H)

def symm : OccurrenceEquiv H G where
  edge := φ.edge.symm
  source f := by
    have hs := φ.source (φ.edge.symm f)
    simpa only [Equiv.apply_symm_apply] using hs.symm
  target f := by
    have ht := φ.target (φ.edge.symm f)
    simpa only [Equiv.apply_symm_apply] using ht.symm

theorem inc_iff (e : E) (a b : V) :
    H.Inc (φ.edge e) a b ↔ G.Inc e a b := by
  unfold EdgeGraph.Inc
  rw [φ.source e, φ.target e]

theorem ustep_map {keep : E → Prop} {more : F → Prop}
    (hkeep : ∀ e, keep e → more (φ.edge e)) {a b : V}
    (h : G.UStep keep a b) : H.UStep more a b := by
  obtain ⟨e, he, hinc⟩ := h
  exact ⟨φ.edge e, hkeep e he, (φ.inc_iff e a b).mpr hinc⟩

theorem ureach_map {keep : E → Prop} {more : F → Prop}
    (hkeep : ∀ e, keep e → more (φ.edge e)) {a b : V}
    (h : G.UReach keep a b) : H.UReach more a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (φ.ustep_map hkeep hstep)

/-- Deletion of one ID transports to deletion of precisely its image ID. -/
theorem reachWithout_map (e : E) {a b : V}
    (h : G.ReachWithout e a b) : H.ReachWithout (φ.edge e) a b := by
  apply φ.ureach_map (keep := fun f => f ≠ e) (more := fun f => f ≠ φ.edge e) _ h
  intro f hf heq
  exact hf (φ.edge.injective heq)

theorem reachWithout_iff (e : E) (a b : V) :
    G.ReachWithout e a b ↔ H.ReachWithout (φ.edge e) a b := by
  constructor
  · exact φ.reachWithout_map e
  · intro h
    have hr := φ.symm.reachWithout_map (φ.edge e) h
    simpa only [symm, Equiv.symm_apply_apply] using hr

theorem isBridge_iff (e : E) :
    G.IsBridge e ↔ H.IsBridge (φ.edge e) := by
  unfold EdgeGraph.IsBridge
  rw [φ.source e, φ.target e]
  exact not_congr (φ.reachWithout_iff e (G.source e) (G.target e))

theorem orientedQuartet_iff (e : E) (a b c d : V) :
    G.OrientedQuartet e a b c d ↔ H.OrientedQuartet (φ.edge e) a b c d := by
  unfold EdgeGraph.OrientedQuartet
  rw [φ.source e, φ.target e]
  exact and_congr (φ.reachWithout_iff e (G.source e) a)
    (and_congr (φ.reachWithout_iff e (G.source e) b)
      (and_congr (φ.reachWithout_iff e (G.target e) c)
        (φ.reachWithout_iff e (G.target e) d)))

theorem hasQuartet_map {a b c d : V}
    (h : G.HasQuartet a b c d) : H.HasQuartet a b c d := by
  obtain ⟨e, he, hq⟩ := h
  refine ⟨φ.edge e, (φ.isBridge_iff e).mp he, ?_⟩
  rcases hq with hq | hq
  · exact Or.inl ((φ.orientedQuartet_iff e a b c d).mp hq)
  · exact Or.inr ((φ.orientedQuartet_iff e c d a b).mp hq)

theorem hasQuartet_iff (a b c d : V) :
    G.HasQuartet a b c d ↔ H.HasQuartet a b c d := by
  exact ⟨φ.hasQuartet_map, φ.symm.hasQuartet_map⟩

/-- The original formal quartet predicate is transported, not replaced. -/
theorem resolves_iff (vertices : Fin 4 → V) (q : Nanuq.Quartet.Resolution) :
    G.Resolves vertices q ↔ H.Resolves vertices q := by
  cases q <;>
    exact φ.hasQuartet_iff _ _ _ _

end OccurrenceEquiv

#print axioms OccurrenceEquiv.reachWithout_iff
#print axioms OccurrenceEquiv.isBridge_iff
#print axioms OccurrenceEquiv.hasQuartet_iff
#print axioms OccurrenceEquiv.resolves_iff

end UnifiedLean.G6.EdgeOccurrenceTransport
