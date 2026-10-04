import G1ComponentDescendantClosure
import UnifiedLean.Source.SourceCalendarTiming

/-! Derived directed-descendant geometry of an actual original cut edge.
Contributor: dot, 2026-10-03. No unique-parent assumption on the original
reticulation network, no calendar/source state field and no desired law. -/
namespace G1ActualCutDescendants
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

lemma actual_directed_walk_avoids_or_crosses (G : EdgeGraph V E) (e : E) {a b : V}
    (h : G.DReach a b) : G.ReachWithout e a b ∨
      (G.DReach a (G.source e) ∧ G.DReach (G.target e) b) := by
  induction h with
  | refl => exact Or.inl .refl
  | @tail b c hab hstep ih =>
      obtain ⟨f,hs,ht⟩ := hstep
      by_cases hf : f = e
      · subst f
        exact Or.inr ⟨by rw [hs]; exact hab,by rw [ht]; exact .refl⟩
      · rcases ih with hw | ⟨hsrc,htar⟩
        · exact Or.inl (hw.tail ⟨f,hf,Or.inl ⟨hs,ht⟩⟩)
        · exact Or.inr ⟨hsrc,htar.tail ⟨f,hs,ht⟩⟩

/-- Every vertex in the target component of an ACTUAL bridge is an actual
DIRECTED descendant of its target. Rooted reachability supplies the crossing;
this remains true with arbitrary original hybrid vertices elsewhere. -/
theorem actual_bridge_target_side_descendant (N : RootedBinary V E X) (e : E)
    (he : N.graph.IsBridge e) (v : V) :
    N.graph.ReachWithout e (N.graph.target e) v ↔ N.graph.DReach (N.graph.target e) v := by
  constructor
  · intro hv
    rcases actual_directed_walk_avoids_or_crosses N.graph e (N.rooted v) with hw | ⟨_,hdesc⟩
    · exact False.elim (N.graph.bridge_sides_disjoint he
        ((N.root_on_source_side e).trans hw) hv)
    · exact hdesc
  · intro hv
    exact N.graph.dreach_preserves
      (P := fun v => N.graph.ReachWithout e (N.graph.target e) v)
      (fun _ _ hs hv => N.graph.bridge_target_forward_closed he hs hv) hv .refl

/-- If a source-side vertex reaches a target-side taxon, its directed path
necessarily crosses the SAME original bridge and therefore starts strictly
older than the target. -/
theorem actual_bridge_source_descendant_crossing (N : RootedBinary V E X)
    (e : E) (he : N.graph.IsBridge e) {v w : V}
    (hv : N.graph.ReachWithout e (N.graph.source e) v)
    (hw : N.graph.ReachWithout e (N.graph.target e) w) (hd : N.graph.DReach v w) :
    N.graph.DReach v (N.graph.source e) := by
  rcases actual_directed_walk_avoids_or_crosses N.graph e hd with havoids | ⟨hsrc,_⟩
  · exact False.elim (N.graph.bridge_sides_disjoint he (hv.trans havoids) hw)
  · exact hsrc

lemma actual_calendar_directed_age (N : RootedBinary V E X) (C : Calendar N.graph)
    {v w : V} (h : N.graph.DReach v w) : C.age w ≤ C.age v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih =>
      obtain ⟨e,hs,ht⟩ := hstep
      have he := C.edge_older e
      rw [hs,ht] at he
      exact he.le.trans ih

lemma actual_calendar_directed_age_strict (N : RootedBinary V E X) (C : Calendar N.graph)
    {v w : V} (hne : v ≠ w) (h : N.graph.DReach v w) : C.age w < C.age v := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨u,⟨e,hs,ht⟩,hrest⟩
  · exact False.elim (hne heq)
  · have he := C.edge_older e
    rw [hs,ht] at he
    exact (actual_calendar_directed_age N C hrest).trans_lt he

theorem actual_source_side_age_strict (N : RootedBinary V E X) (C : Calendar N.graph)
    (e : E) (he : N.graph.IsBridge e) {v w : V}
    (hv : N.graph.ReachWithout e (N.graph.source e) v)
    (hw : N.graph.ReachWithout e (N.graph.target e) w) (hd : N.graph.DReach v w) :
    C.age (N.graph.target e) < C.age v := by
  exact (C.edge_older e).trans_le
    (actual_calendar_directed_age N C (actual_bridge_source_descendant_crossing N e he hv hw hd))

end G1ActualCutDescendants
