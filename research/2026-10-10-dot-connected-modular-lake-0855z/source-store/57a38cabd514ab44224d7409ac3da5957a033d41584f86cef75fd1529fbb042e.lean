import G1SimpleCurveConcatenation

/-! The ACTUAL new bigon-splice edge is a simple curved entry-arm-child
concatenation, with image inside the unchanged original multigraph drawing.
Parallel-arm IDs/interiors are not conflated. Other new drawing fields and
semidirected root suppression are subsequent explicit admission gates. -/
namespace G1ActualBigonSpliceSimpleCurve
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1OuterLabelledMultigraphCurves G1SimpleCurveConcatenation Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_arcs_meet_only_at_first_target {W F : Type*} {G : EdgeGraph W F}
    (D : PlanarCurves G) (e f : F) (hef : e ≠ f)
    (hs : G.source e ≠ G.source f) (ht : G.source e ≠ G.target f)
    (t u : unitInterval) (he : D.arc e t = D.arc f u) : D.arc e t = D.point (G.target e) := by
  have hi := D.edge_incidence e f hef t u he
  rcases hi.1 with hzero | hone
  · rcases hi.2 with hzero' | hone'
    · have hp : D.point (G.source e) = D.point (G.source f) := by simpa [hzero,hzero'] using he
      exact False.elim (hs (D.point_injective hp))
    · have hp : D.point (G.source e) = D.point (G.target f) := by simpa [hzero,hone'] using he
      exact False.elim (ht (D.point_injective hp))
  · simp [hone]

noncomputable def entryCurve (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (D : PlanarCurves N.graph) : Path (D.point (N.graph.source A.entry)) (D.point A.fragment.upper) :=
  (D.arc A.entry).cast rfl (congrArg D.point A.entry_target.symm)

noncomputable def armCurve (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (D : PlanarCurves N.graph) : Path (D.point A.fragment.upper) (D.point A.fragment.parents.hybrid) :=
  (D.arc A.fragment.parents.parent0).cast
    (congrArg D.point (A.fragment.arm_sources false).symm) (congrArg D.point A.fragment.parents.target0.symm)

noncomputable def childCurve (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (D : PlanarCurves N.graph) : Path (D.point A.fragment.parents.hybrid) (D.point (N.graph.target A.child)) :=
  (D.arc A.child).cast (congrArg D.point A.child_source.symm) rfl

noncomputable def actualSpliceCurve (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (D : PlanarCurves N.graph) : Path (D.point (N.graph.source A.entry)) (D.point (N.graph.target A.child)) :=
  ((entryCurve N b A D).trans (armCurve N b A D)).trans (childCurve N b A D)

lemma actual_entry_arm_meet_at_upper (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (D : PlanarCurves N.graph) (t u : unitInterval)
    (he : entryCurve N b A D t = armCurve N b A D u) : entryCurve N b A D t = D.point A.fragment.upper := by
  have hdiff : A.entry ≠ A.fragment.parents.parent0 := by
    intro hh
    have hv := congrArg N.graph.target hh
    rw [A.entry_target,A.fragment.parents.target0] at hv
    exact actual_upper_hybrid_distinct N b A hv
  have hports := (actual_external_interface_vertices N b A).1
  have hs0 : N.graph.source A.fragment.parents.parent0 = A.fragment.upper := A.fragment.arm_sources false
  have hshare := actual_arcs_meet_only_at_first_target D A.entry A.fragment.parents.parent0 hdiff
    (by simpa only [hs0] using hports.1)
    (by simpa only [A.fragment.parents.target0] using hports.2) t u he
  change D.arc A.entry t = D.point A.fragment.upper
  simpa only [A.entry_target] using hshare

lemma actual_arm_child_meet_at_hybrid (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (D : PlanarCurves N.graph) (t u : unitInterval)
    (he : armCurve N b A D t = childCurve N b A D u) : armCurve N b A D t = D.point A.fragment.parents.hybrid := by
  have hs0 : N.graph.source A.fragment.parents.parent0 = A.fragment.upper := A.fragment.arm_sources false
  have hdiff : A.fragment.parents.parent0 ≠ A.child := by
    intro hh
    have hv := congrArg N.graph.source hh
    rw [hs0,A.child_source] at hv
    exact actual_upper_hybrid_distinct N b A hv
  have hshare := actual_arcs_meet_only_at_first_target D A.fragment.parents.parent0 A.child hdiff
    (by rw [hs0,A.child_source]; exact actual_upper_hybrid_distinct N b A)
    (by rw [hs0]; exact Ne.symm (actual_external_interface_vertices N b A).2.1) t u he
  change D.arc A.fragment.parents.parent0 t = D.point A.fragment.parents.hybrid
  simpa only [A.fragment.parents.target0] using hshare

lemma actual_entry_child_curves_disjoint (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (D : PlanarCurves N.graph) (t u : unitInterval) :
    entryCurve N b A D t ≠ childCurve N b A D u := by
  have hentry := C.edge_older A.entry
  have harm := C.edge_older A.fragment.parents.parent0
  have hchild := C.edge_older A.child
  have hs0 : N.graph.source A.fragment.parents.parent0 = A.fragment.upper := A.fragment.arm_sources false
  rw [A.entry_target] at hentry
  rw [hs0,A.fragment.parents.target0] at harm
  rw [A.child_source] at hchild
  have hsd : N.graph.source A.entry ≠ N.graph.target A.child := by intro hh; rw [hh] at hentry; linarith
  have hdiff : A.entry ≠ A.child := by
    intro hh
    exact (actual_external_interface_vertices N b A).1.2 ((congrArg N.graph.source hh).trans A.child_source)
  intro he
  have hshare := actual_arcs_meet_only_at_first_target D A.entry A.child hdiff
    (by rw [A.child_source]; exact (actual_external_interface_vertices N b A).1.2) hsd t u he
  have hup : entryCurve N b A D t = D.point A.fragment.upper := by
    change D.arc A.entry t = D.point A.fragment.upper
    simpa only [A.entry_target] using hshare
  have hv := D.vertex_incidence A.child A.fragment.upper u (he.symm.trans hup)
  rcases hv with hv | hv
  · rw [A.child_source] at hv
    exact actual_upper_hybrid_distinct N b A hv
  · exact (actual_external_interface_vertices N b A).2.1 hv.symm

theorem actual_bigon_splice_curve_injective (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (D : PlanarCurves N.graph) :
    Function.Injective (actualSpliceCurve N b A D) := by
  have hprefix : Function.Injective ((entryCurve N b A D).trans (armCurve N b A D)) :=
    actual_simple_path_concatenation _ _ (D.arc_injective A.entry) (D.arc_injective A.fragment.parents.parent0)
      (actual_entry_arm_meet_at_upper N b A D)
  apply actual_simple_path_concatenation _ _ hprefix (D.arc_injective A.child)
  intro t u he
  have hr : ((entryCurve N b A D).trans (armCurve N b A D)) t ∈
      range (entryCurve N b A D) ∪ range (armCurve N b A D) := by
    rw [←Path.trans_range]
    exact mem_range_self t
  rcases hr with hr | hr
  · obtain ⟨v,hv⟩ := hr
    exact False.elim (actual_entry_child_curves_disjoint N C b A D v u (hv.trans he))
  · obtain ⟨v,hv⟩ := hr
    exact hv.symm.trans (actual_arm_child_meet_at_hybrid N b A D v u (hv.trans he))

theorem actual_bigon_splice_curve_trace_subset (N : RootedBinary V E X)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (D : PlanarCurves N.graph) :
    range (actualSpliceCurve N b A D) ⊆ drawing D := by
  intro point hp
  rw [actualSpliceCurve,Path.trans_range,Path.trans_range] at hp
  rcases hp with (hp | hp) | hp
  · exact Or.inr (mem_iUnion.mpr ⟨A.entry,hp⟩)
  · exact Or.inr (mem_iUnion.mpr ⟨A.fragment.parents.parent0,hp⟩)
  · exact Or.inr (mem_iUnion.mpr ⟨A.child,hp⟩)

#print axioms actual_bigon_splice_curve_injective
end G1ActualBigonSpliceSimpleCurve
