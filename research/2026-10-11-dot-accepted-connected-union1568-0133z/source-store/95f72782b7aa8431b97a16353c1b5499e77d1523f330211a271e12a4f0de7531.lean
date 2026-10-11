import G1ActualBigonSpliceSimpleCurve

/-! Full faithful planar multigraph drawing of the ACTUAL constructed splice.
Every retained curve/vertex is literal original geometry; the new curve is
the proved simple entry-arm-child concatenation inside the old trace. -/
namespace G1ActualSplicedPlanarCurves
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1OuterLabelledMultigraphCurves G1ActualBigonSpliceSimpleCurve Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_new_curve_kept_vertex_incidence (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (D : PlanarCurves N.graph) (v : SplicedVertex N b A) (t : unitInterval)
    (he : actualSpliceCurve N b A D t = D.point v.val) :
    v.val = N.graph.source A.entry ∨ v.val = N.graph.target A.child := by
  have hr : D.point v.val ∈ range (actualSpliceCurve N b A D) := ⟨t,he⟩
  rw [actualSpliceCurve,Path.trans_range,Path.trans_range] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨q,hq⟩ := hr
    rcases D.vertex_incidence A.entry v.val q hq with hs | ht
    · exact Or.inl hs
    · rw [A.entry_target] at ht
      exact False.elim (v.property.1 ht)
  · obtain ⟨q,hq⟩ := hr
    rcases D.vertex_incidence A.fragment.parents.parent0 v.val q hq with hs | ht
    · have hs0 : N.graph.source A.fragment.parents.parent0 = A.fragment.upper := A.fragment.arm_sources false
      rw [hs0] at hs
      exact False.elim (v.property.1 hs)
    · rw [A.fragment.parents.target0] at ht
      exact False.elim (v.property.2 ht)
  · obtain ⟨q,hq⟩ := hr
    rcases D.vertex_incidence A.child v.val q hq with hs | ht
    · rw [A.child_source] at hs
      exact False.elim (v.property.2 hs)
    · exact Or.inr ht

lemma actual_new_curve_kept_vertex_parameter (N : RootedBinary V E X) (C : Calendar N.graph) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (D : PlanarCurves N.graph) (v : SplicedVertex N b A) (t : unitInterval)
    (he : actualSpliceCurve N b A D t = D.point v.val) : t = 0 ∨ t = 1 := by
  have hi := actual_bigon_splice_curve_injective N C b A D
  rcases actual_new_curve_kept_vertex_incidence N b A D v t he with hs | ht
  · left
    apply hi
    exact he.trans ((congrArg D.point hs).trans (actualSpliceCurve N b A D).source.symm)
  · right
    apply hi
    exact he.trans ((congrArg D.point ht).trans (actualSpliceCurve N b A D).target.symm)

lemma actual_retained_curve_new_intersection (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (A : ActualBlobBigon N b) (D : PlanarCurves N.graph)
    (e : RetainedEdge N b A) (t u : unitInterval)
    (he : D.arc e.val t = actualSpliceCurve N b A D u) : (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  have hneq : e.val ≠ A.entry ∧ e.val ≠ A.child ∧ e.val ≠ A.fragment.parents.parent0 ∧ e.val ≠ A.fragment.parents.parent1 := by
    simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton,not_or] using e.property
  have hr : actualSpliceCurve N b A D u ∈ range (actualSpliceCurve N b A D) := mem_range_self u
  rw [actualSpliceCurve,Path.trans_range,Path.trans_range] at hr
  have hend : t = 0 ∨ t = 1 := by
    rcases hr with (hr | hr) | hr
    · obtain ⟨q,hq⟩ := hr
      exact (D.edge_incidence e.val A.entry hneq.1 t q (he.trans hq.symm)).1
    · obtain ⟨q,hq⟩ := hr
      exact (D.edge_incidence e.val A.fragment.parents.parent0 hneq.2.2.1 t q (he.trans hq.symm)).1
    · obtain ⟨q,hq⟩ := hr
      exact (D.edge_incidence e.val A.child hneq.2.1 t q (he.trans hq.symm)).1
  refine ⟨hend,?_⟩
  rcases hend with ht | ht
  · apply actual_new_curve_kept_vertex_parameter N C b A D (retainedSource N hc b A e) u
    simpa only [ht,Path.source,retainedSource] using he.symm
  · apply actual_new_curve_kept_vertex_parameter N C b A D (retainedTarget N hc b A e) u
    simpa only [ht,Path.target,retainedTarget] using he.symm

noncomputable def splicePoint (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (D : PlanarCurves N.graph) (v : SplicedVertex N b A) : Plane := D.point v.val

noncomputable def spliceArc (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (D : PlanarCurves N.graph) (e : SplicedEdge N b A) :
    Path (splicePoint N b A D ((spliceGraph N hc b A).source e))
      (splicePoint N b A D ((spliceGraph N hc b A).target e)) := by
  cases e with
  | inl e => exact D.arc e.val
  | inr e => exact actualSpliceCurve N b A D

/-- Literal constructed output drawing, including nonincident-vertex and
distinct-edge interior disjointness. Parallel retained edges keep their IDs. -/
noncomputable def actualSplicedPlanarCurves (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (A : ActualBlobBigon N b) (D : PlanarCurves N.graph) :
    PlanarCurves (spliceGraph N hc b A) where
  point := splicePoint N b A D
  point_injective := fun v w he => Subtype.ext (D.point_injective he)
  arc := spliceArc N hc b A D
  arc_injective := by
    intro e
    cases e with
    | inl e => exact D.arc_injective e.val
    | inr e => exact actual_bigon_splice_curve_injective N C b A D
  vertex_incidence := by
    intro e v t he
    cases e with
    | inl e =>
      rcases D.vertex_incidence e.val v.val t he with hs | ht
      · exact Or.inl (Subtype.ext hs)
      · exact Or.inr (Subtype.ext ht)
    | inr e =>
      rcases actual_new_curve_kept_vertex_incidence N b A D v t he with hs | ht
      · exact Or.inl (Subtype.ext hs)
      · exact Or.inr (Subtype.ext ht)
  edge_incidence := by
    intro e f hdiff t u he
    cases e with
    | inl e =>
      cases f with
      | inl f =>
        have hn : e.val ≠ f.val := fun hh => hdiff (congrArg Sum.inl (Subtype.ext hh))
        exact D.edge_incidence e.val f.val hn t u he
      | inr f => exact actual_retained_curve_new_intersection N C hc b A D e t u he
    | inr e =>
      cases f with
      | inl f =>
        have hi := actual_retained_curve_new_intersection N C hc b A D f u t he.symm
        exact ⟨hi.2,hi.1⟩
      | inr f =>
        cases e; cases f
        exact False.elim (hdiff rfl)

theorem actual_spliced_drawing_subset (N : RootedBinary V E X) (C : Calendar N.graph)
    (hc : CutChild N) (b : N.graph.Blob) (A : ActualBlobBigon N b) (D : PlanarCurves N.graph) :
    drawing (actualSplicedPlanarCurves N C hc b A D) ⊆ drawing D := by
  intro point hp
  rcases hp with hp | hp
  · obtain ⟨v,hv⟩ := hp
    exact Or.inl ⟨v.val,hv⟩
  · obtain ⟨e,he⟩ := mem_iUnion.mp hp
    cases e with
    | inl e => exact Or.inr (mem_iUnion.mpr ⟨e.val,he⟩)
    | inr e => exact actual_bigon_splice_curve_trace_subset N b A D he

#print axioms actualSplicedPlanarCurves
end G1ActualSplicedPlanarCurves
