import GraphCuts
import GraphSwitching

/-! Walk locality for the forthcoming actual four-port quartet restriction.
The predicate used below is an actual edge-deletion component; no quartet or
matrix-law equality is assumed. This file alone is not the restriction theorem. -/
namespace Nanuq.Source.EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

theorem reach_without_other_edge_of_closed_predicate {e f : E} {a b : V}
    (P : V → Prop)
    (hclosed : ∀ ⦃u v⦄, G.UStep (fun g => g ≠ e) u v → P u → P v)
    (hs : ¬ P (G.source f)) (ht : ¬ P (G.target f))
    (ha : P a) (hab : G.ReachWithout e a b) : G.ReachWithout f a b := by
  induction hab with
  | refl => exact .refl
  | tail hprev hstep ih =>
    obtain ⟨g, _, hinc⟩ := hstep
    have hp := G.ureach_preserves hclosed hprev ha
    have hgf : g ≠ f := by
      intro heq
      subst g
      rcases hinc with ⟨hsource, _⟩ | ⟨_, htarget⟩
      · rw [← hsource] at hp
        exact hs hp
      · rw [← htarget] at hp
        exact ht hp
    exact ih.tail ⟨g, hgf, hinc⟩

theorem source_side_walk_avoids_opposite_edge {e f : E} {a b : V}
    (he : G.IsBridge e) (ha : G.ReachWithout e (G.source e) a)
    (hs : G.ReachWithout e (G.target e) (G.source f))
    (ht : G.ReachWithout e (G.target e) (G.target f))
    (hab : G.ReachWithout e a b) : G.ReachWithout f a b := by
  exact G.reach_without_other_edge_of_closed_predicate
    (fun x => G.ReachWithout e (G.source e) x)
    (fun _ _ hstep h => h.tail hstep)
    (fun h => G.bridge_sides_disjoint he h hs)
    (fun h => G.bridge_sides_disjoint he h ht) ha hab

theorem target_side_walk_avoids_opposite_edge {e f : E} {a b : V}
    (he : G.IsBridge e) (ha : G.ReachWithout e (G.target e) a)
    (hs : G.ReachWithout e (G.source e) (G.source f))
    (ht : G.ReachWithout e (G.source e) (G.target f))
    (hab : G.ReachWithout e a b) : G.ReachWithout f a b := by
  exact G.reach_without_other_edge_of_closed_predicate
    (fun x => G.ReachWithout e (G.target e) x)
    (fun _ _ hstep h => h.tail hstep)
    (fun h => G.bridge_sides_disjoint he hs h)
    (fun h => G.bridge_sides_disjoint he ht h) ha hab

end Nanuq.Source.EdgeGraph
