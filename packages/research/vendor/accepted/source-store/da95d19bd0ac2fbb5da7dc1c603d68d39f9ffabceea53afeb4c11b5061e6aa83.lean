import NanuqActualGalledHybridBoundary

/-! Erasing an excursion through a leaf of an allowed-edge graph. The proof
uses actual edge IDs and retains parallel occurrences. -/
namespace Nanuq.Source.EdgeGraph
open scoped Classical
variable {V E : Type*} [DecidableEq V] (G : EdgeGraph V E)

def leafEdgeCollapse (e : E) (v : V) : V := if v = G.source e then G.target e else v

theorem allowed_walk_erases_leaf_edge (keep : E → Prop) (e : E)
    (hne : G.source e ≠ G.target e)
    (hincident : ∀ f, keep f → f ≠ e → G.source f ≠ G.source e ∧ G.target f ≠ G.source e)
    {a b : V} (h : G.UReach keep a b) :
    G.UReach (fun f => keep f ∧ f ≠ e) (G.leafEdgeCollapse e a) (G.leafEdgeCollapse e b) := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨f,hf,hinc⟩ := hs
    by_cases hfe : f = e
    · subst f
      have hvw : G.leafEdgeCollapse e v = G.leafEdgeCollapse e w := by
        rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
        · rw [← hs,← ht]
          simp [leafEdgeCollapse,hne.symm]
        · rw [← hs,← ht]
          simp [leafEdgeCollapse,hne.symm]
      exact hvw ▸ ih
    · have hn := hincident f hf hfe
      apply ih.tail
      refine ⟨f,⟨hf,hfe⟩,?_⟩
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · exact Or.inl ⟨by simpa [leafEdgeCollapse,hn.1] using congrArg (G.leafEdgeCollapse e) hs,
          by simpa [leafEdgeCollapse,hn.2] using congrArg (G.leafEdgeCollapse e) ht⟩
      · exact Or.inr ⟨by simpa [leafEdgeCollapse,hn.1] using congrArg (G.leafEdgeCollapse e) hs,
          by simpa [leafEdgeCollapse,hn.2] using congrArg (G.leafEdgeCollapse e) ht⟩

theorem allowed_walk_avoids_leaf_edge (keep : E → Prop) (e : E)
    (hne : G.source e ≠ G.target e)
    (hincident : ∀ f, keep f → f ≠ e → G.source f ≠ G.source e ∧ G.target f ≠ G.source e)
    {a b : V} (ha : a ≠ G.source e) (hb : b ≠ G.source e)
    (h : G.UReach keep a b) : G.UReach (fun f => keep f ∧ f ≠ e) a b := by
  simpa [leafEdgeCollapse,ha,hb] using G.allowed_walk_erases_leaf_edge keep e hne hincident h
end Nanuq.Source.EdgeGraph

#print axioms Nanuq.Source.EdgeGraph.allowed_walk_avoids_leaf_edge
