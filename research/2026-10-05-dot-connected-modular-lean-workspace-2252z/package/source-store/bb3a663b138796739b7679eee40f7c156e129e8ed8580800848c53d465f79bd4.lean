import G1FormerRootSimpleSuppressionCurve

/-! The complete faithful drawing of the literal former-root-suppressed
multigraph, with the correct retained/new edge IDs. Its drawing is inside
the original rooted drawing, hence every original labelled leaf remains on
the same unbounded complementary face. -/
namespace G1RootSuppressedPlanarCurves
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1OuterLabelledMultigraphCurves G1FormerRootSimpleSuppressionCurve Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_kept_curve_suppression_intersection (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) (e : KeptEdge N) (t u : unitInterval)
    (he : D.arc e.val t = formerRootCurve N ports D u) :
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  have hf : e.val ≠ ports.first := fun h => e.property (h ▸ ports.source_first)
  have hs : e.val ≠ ports.second := fun h => e.property (h ▸ ports.source_second)
  have hr : formerRootCurve N ports D u ∈ range (formerRootCurve N ports D) := mem_range_self u
  rw [actual_former_root_curve_range] at hr
  have ht : t = 0 ∨ t = 1 := by
    rcases hr with hr | hr
    · obtain ⟨q,hq⟩ := hr
      exact (D.edge_incidence e.val ports.first hf t q (he.trans hq.symm)).1
    · obtain ⟨q,hq⟩ := hr
      exact (D.edge_incidence e.val ports.second hs t q (he.trans hq.symm)).1
  refine ⟨ht,?_⟩
  rcases ht with ht | ht
  · apply actual_suppression_curve_kept_vertex_parameter N ports D (keptSource N e) u
    simpa only [ht,Path.source,keptSource] using he.symm
  · apply actual_suppression_curve_kept_vertex_parameter N ports D (keptTarget N e) u
    simpa only [ht,Path.target,keptTarget] using he.symm

noncomputable def rootSuppressedArc (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) (e : SuppressedEdge N) :
    Path (D.point ((suppressedGraph N ports).source e).val)
      (D.point ((suppressedGraph N ports).target e).val) := by
  cases e with
  | inl e => exact D.arc e.val
  | inr e => exact formerRootCurve N ports D

noncomputable def actualRootSuppressedPlanarCurves (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) : PlanarCurves (suppressedGraph N ports) where
  point := fun v => D.point v.val
  point_injective := fun v w he => Subtype.ext (D.point_injective he)
  arc := rootSuppressedArc N ports D
  arc_injective := by
    intro e
    cases e with
    | inl e => exact D.arc_injective e.val
    | inr e => exact actual_former_root_curve_injective N ports D
  vertex_incidence := by
    intro e v t he
    cases e with
    | inl e =>
      rcases D.vertex_incidence e.val v.val t he with hs | ht
      · exact Or.inl (Subtype.ext hs)
      · exact Or.inr (Subtype.ext ht)
    | inr e =>
      rcases actual_suppression_curve_kept_vertex N ports D v t he with hs | ht
      · exact Or.inl (Subtype.ext hs)
      · exact Or.inr (Subtype.ext ht)
  edge_incidence := by
    intro e f hdiff t u he
    cases e with
    | inl e =>
      cases f with
      | inl f =>
        exact D.edge_incidence e.val f.val
          (fun h => hdiff (congrArg Sum.inl (Subtype.ext h))) t u he
      | inr f => exact actual_kept_curve_suppression_intersection N ports D e t u he
    | inr e =>
      cases f with
      | inl f =>
        have h := actual_kept_curve_suppression_intersection N ports D f u t he.symm
        exact ⟨h.2,h.1⟩
      | inr f => cases e; cases f; exact False.elim (hdiff rfl)

theorem actual_root_suppressed_drawing_subset (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) : drawing (actualRootSuppressedPlanarCurves N ports D) ⊆ drawing D := by
  intro p hp
  rcases hp with hp | hp
  · obtain ⟨v,hv⟩ := hp
    exact Or.inl ⟨v.val,hv⟩
  · obtain ⟨e,he⟩ := mem_iUnion.mp hp
    cases e with
    | inl e => exact Or.inr (mem_iUnion.mpr ⟨e.val,he⟩)
    | inr e =>
      change p ∈ range (formerRootCurve N ports D) at he
      rw [actual_former_root_curve_range] at he
      rcases he with he | he
      · exact Or.inr (mem_iUnion.mpr ⟨ports.first,he⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨ports.second,he⟩)

noncomputable def actualRootSuppressedOuterCurves (N : RootedBinary V E X) (ports : RootPorts N)
    (D : OuterLabelledCurves N.graph N.leaf) :
    OuterLabelledCurves (suppressedGraph N ports) (suppressedLeaf N) where
  curves := actualRootSuppressedPlanarCurves N ports D.curves
  outer_face := Classical.choice (actual_outer_face_of_drawing_subset D.curves
    (actualRootSuppressedPlanarCurves N ports D.curves) N.leaf (suppressedLeaf N) D.outer_face
    (actual_root_suppressed_drawing_subset N ports D.curves) (fun x => rfl))

#print axioms actualRootSuppressedOuterCurves
end G1RootSuppressedPlanarCurves
