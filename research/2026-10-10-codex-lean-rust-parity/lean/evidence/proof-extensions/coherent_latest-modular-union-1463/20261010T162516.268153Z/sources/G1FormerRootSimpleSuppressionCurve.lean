import G1LiteralSemidirectedRootSuppression

/-! The former-root replacement curve is the reversed first old root arc
followed by the second. It is simple because the faithful old drawing lets
the two distinct root arcs meet only at the root. No parallel edge is merged. -/
namespace G1FormerRootSimpleSuppressionCurve
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1OuterLabelledMultigraphCurves G1SimpleCurveConcatenation Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def backwardsFirst (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) : Path (D.point (N.graph.target ports.first)) (D.point N.root) :=
  (D.arc ports.first).symm.cast rfl (congrArg D.point ports.source_first.symm)
noncomputable def forwardsSecond (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) : Path (D.point N.root) (D.point (N.graph.target ports.second)) :=
  (D.arc ports.second).cast (congrArg D.point ports.source_second.symm) rfl
noncomputable def formerRootCurve (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) :
    Path (D.point (N.graph.target ports.first)) (D.point (N.graph.target ports.second)) :=
  (backwardsFirst N ports D).trans (forwardsSecond N ports D)

lemma actual_two_root_arcs_meet_only_at_root (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) (t u : unitInterval)
    (he : D.arc ports.first t = D.arc ports.second u) : D.arc ports.first t = D.point N.root := by
  have hi := D.edge_incidence ports.first ports.second ports.different t u he
  rcases hi.1 with hz | ho
  · simpa [hz,ports.source_first]
  · rcases hi.2 with hz | ho'
    · have hp : N.graph.target ports.first = N.root :=
        D.point_injective (by simpa [ho,hz,ports.source_second] using he)
      exact False.elim (N.edge_target_ne_root ports.first hp)
    · have hp : N.graph.target ports.first = N.graph.target ports.second :=
        D.point_injective (by simpa [ho,ho'] using he)
      exact False.elim (actual_root_children_distinct N ports hp)

theorem actual_former_root_curve_injective (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) : Function.Injective (formerRootCurve N ports D) := by
  apply actual_simple_path_concatenation
  · exact (D.arc_injective ports.first).comp unitInterval.symm_involutive.injective
  · exact D.arc_injective ports.second
  · intro t u he
    exact actual_two_root_arcs_meet_only_at_root N ports D _ _ he

theorem actual_former_root_curve_range (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) :
    range (formerRootCurve N ports D) = range (D.arc ports.first) ∪ range (D.arc ports.second) := by
  rw [formerRootCurve,Path.trans_range]
  change range (D.arc ports.first).symm ∪ range (D.arc ports.second) = _
  rw [Path.symm_range]

lemma actual_suppression_curve_kept_vertex (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) (v : SuppressedVertex N) (t : unitInterval)
    (he : formerRootCurve N ports D t = D.point v.val) :
    v.val = N.graph.target ports.first ∨ v.val = N.graph.target ports.second := by
  have hr : D.point v.val ∈ range (formerRootCurve N ports D) := ⟨t,he⟩
  rw [actual_former_root_curve_range] at hr
  rcases hr with hr | hr
  · obtain ⟨q,hq⟩ := hr
    rcases D.vertex_incidence ports.first v.val q hq with hs | ht
    · exact False.elim (v.property (hs.trans ports.source_first))
    · exact Or.inl ht
  · obtain ⟨q,hq⟩ := hr
    rcases D.vertex_incidence ports.second v.val q hq with hs | ht
    · exact False.elim (v.property (hs.trans ports.source_second))
    · exact Or.inr ht

lemma actual_suppression_curve_kept_vertex_parameter (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves N.graph) (v : SuppressedVertex N) (t : unitInterval)
    (he : formerRootCurve N ports D t = D.point v.val) : t = 0 ∨ t = 1 := by
  have hi := actual_former_root_curve_injective N ports D
  rcases actual_suppression_curve_kept_vertex N ports D v t he with hf | hs
  · exact Or.inl (hi (he.trans ((congrArg D.point hf).trans (formerRootCurve N ports D).source.symm)))
  · exact Or.inr (hi (he.trans ((congrArg D.point hs).trans (formerRootCurve N ports D).target.symm)))

#print axioms actual_former_root_curve_injective
end G1FormerRootSimpleSuppressionCurve
