import G1NaturalCalendarNodes

/-! Exact original descendant-interface CURRENT-root frontier. Contributor:
dot, 2026-10-03. SourceValid, actual post-exit physical readiness, and the
proved natural-node/edge-entry invariants identify ALL descendant labels at D.
No original-copy cap, desired input forest, or source law is a premise. -/
namespace G1ActualEnteringFrontier
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceCalendarPhysicalSupport
open G1ActualCutDescendants G1NaturalCalendarNodes
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Just before D's node entry, original descendant copies occupy EXACTLY D.
The strict edge-entry bound excludes abstract premature child-edge states;
NaturalNodes excludes abstract dormant future internal-node states. -/
theorem actual_descendant_interface_location (N : RootedBinary V E X)
    (C : Calendar N.graph) (e : E) (he : N.graph.IsBridge e) {sample : Copy → X}
    (s : Code N sample) (hready : AfterExits N C (C.age (N.graph.target e)) (state s))
    (hnodes : NaturalNodes N C sample (C.age (N.graph.target e)) (state s))
    (hentered : ∀ x : Copy, ∀ f : E, copyLocation (state s) x = .edge f →
      C.age (N.graph.target f) < C.age (N.graph.target e))
    (x : Copy) :
    N.graph.DReach (N.graph.target e) (N.leaf (sample x)) ↔
      copyLocation (state s) x = .node (N.graph.target e) := by
  constructor
  · intro hx
    have hleaf := (actual_bridge_target_side_descendant N e he _).mpr hx
    have hvalid : DescendsTo N (copyLocation (state s) x) (sample x) := s.property.original_descendant x
    have hp := hready.1 x
    cases hloc : copyLocation (state s) x with
    | node v =>
        rw [hloc] at hvalid
        change N.graph.DReach v (N.leaf (sample x)) at hvalid
        rw [hloc] at hp
        have hvside : N.graph.ReachWithout e (N.graph.target e) v := by
          rcases N.graph.edge_side_cover e (N.underlying_connected (N.graph.source e) v) with hs | ht
          · have ho := actual_source_side_age_strict N C e he hs hleaf hvalid
            rcases hnodes x v hloc with hv | hv
            · rw [hv] at hs
              exact False.elim (N.graph.bridge_sides_disjoint he hs hleaf)
            · exact False.elim (not_lt_of_ge hv ho)
          · exact ht
        have hvdesc := (actual_bridge_target_side_descendant N e he v).mp hvside
        have hv : v = N.graph.target e := by
          by_contra hn
          have hstrict := actual_calendar_directed_age_strict N C (Ne.symm hn) hvdesc
          exact not_lt_of_ge hp hstrict
        exact congrArg Location.node hv
    | edge f =>
        rw [hloc] at hvalid
        change N.graph.DReach (N.graph.target f) (N.leaf (sample x)) at hvalid
        rw [hloc] at hp
        have htarget : N.graph.ReachWithout e (N.graph.target e) (N.graph.target f) := by
          rcases N.graph.edge_side_cover e (N.underlying_connected (N.graph.source e) (N.graph.target f)) with hs | ht
          · have ho := actual_source_side_age_strict N C e he hs hleaf hvalid
            exact False.elim (not_lt_of_ge hp.1 ho)
          · exact ht
        have hfe : f ≠ e := by
          intro h; subst f
          exact (lt_irrefl _) (hentered x e hloc)
        have hsource : N.graph.ReachWithout e (N.graph.target e) (N.graph.source f) :=
          htarget.tail ⟨f,hfe,Or.inr ⟨rfl,rfl⟩⟩
        have hdesc := (actual_bridge_target_side_descendant N e he _).mp hsource
        have hage := actual_calendar_directed_age N C hdesc
        exact False.elim (not_lt_of_ge hage (hready.2 x f hloc))
    | rootPopulation v =>
        rw [hloc] at hp
        have hstrict := actual_calendar_directed_age_strict N C (N.edge_target_ne_root e).symm
          (N.rooted (N.graph.target e))
        exact False.elim (not_lt_of_ge hp.2 hstrict)
  · intro hloc
    have hv : DescendsTo N (copyLocation (state s) x) (sample x) := s.property.original_descendant x
    rw [hloc] at hv
    exact hv

/-- The actual component roots are picked from the current live-owner set,
not the original sample-copy set or descendant leaves of carried subtrees. -/
noncomputable def enteringRoots (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (D : V) : Finset Copy :=
  (state s).live.filter (fun l => (state s).location l = .node D)

noncomputable def exteriorRoots (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (D : V) : Finset Copy := (state s).live \ enteringRoots N s D

lemma actual_entering_root_partition (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (D : V) :
    enteringRoots N s D ∪ exteriorRoots N s D = (state s).live ∧
      Disjoint (enteringRoots N s D) (exteriorRoots N s D) := by
  exact ⟨Finset.union_sdiff_of_subset (Finset.filter_subset _ _),by
    apply Finset.disjoint_left.mpr
    intro l hi ho
    exact (Finset.mem_sdiff.mp ho).2 hi⟩

/-- Every exterior CURRENT owner has its original representative sample
outside D's descendants. Every inside owner is at D; all opaque leaf payloads
remain in the original state. These facts instantiate the graph-side separator. -/
theorem actual_current_frontier_owner_binding (N : RootedBinary V E X)
    (C : Calendar N.graph) (e : E) (he : N.graph.IsBridge e) {sample : Copy → X}
    (s : Code N sample) (hready : AfterExits N C (C.age (N.graph.target e)) (state s))
    (hnodes : NaturalNodes N C sample (C.age (N.graph.target e)) (state s))
    (hentered : ∀ x : Copy, ∀ f : E, copyLocation (state s) x = .edge f →
      C.age (N.graph.target f) < C.age (N.graph.target e)) :
    (∀ x ∈ enteringRoots N s (N.graph.target e), copyLocation (state s) x = .node (N.graph.target e)) ∧
      (∀ y ∈ exteriorRoots N s (N.graph.target e),
        ¬ N.graph.DReach (N.graph.target e) (N.leaf (sample y))) := by
  constructor
  · intro x hx
    have hx := Finset.mem_filter.mp hx
    have hr : (state s).ancestor x = x := s.property.forest.representative x hx.1
    rw [copyLocation,hr]
    exact hx.2
  · intro y hy hd
    have hy := Finset.mem_sdiff.mp hy
    have hloc := (actual_descendant_interface_location N C e he s hready hnodes hentered y).mp hd
    have hr : (state s).ancestor y = y := s.property.forest.representative y hy.1
    change (state s).location ((state s).ancestor y) = .node (N.graph.target e) at hloc
    rw [hr] at hloc
    exact hy.2 (Finset.mem_filter.mpr ⟨hy.1,hloc⟩)

end G1ActualEnteringFrontier
