import G1OriginalRootSubdivisionData

/-! Actual incidence and interior-disjointness after midpoint subdivision
of the root-suppressed edge. These fields are derived from the input
semidirected multigraph drawing, including distinct parallel edge IDs. -/
namespace G1RootSubdivisionIncidence
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1OuterLabelledMultigraphCurves G1InjectiveHalfArcSubdivision G1OriginalRootSubdivisionData Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma left_reverse_ne_one (t : unitInterval) : leftTime (unitInterval.symm t) ≠ 1 := by
  intro h
  have hv := congrArg Subtype.val h
  change (1-(t:ℝ))/2 = 1 at hv
  have h0 := t.property.1
  linarith
lemma right_ne_zero (t : unitInterval) : rightTime t ≠ 0 := by
  intro h
  have hv := congrArg Subtype.val h
  change ((t:ℝ)+1)/2 = 0 at hv
  have h0 := t.property.1
  linarith
lemma left_reverse_zero (t : unitInterval) (h : leftTime (unitInterval.symm t) = 0) : t = 1 := by
  have hv := congrArg Subtype.val h
  apply Subtype.ext
  change (1-(t:ℝ))/2 = 0 at hv
  change (t:ℝ)=1
  linarith
lemma right_one (t : unitInterval) (h : rightTime t = 1) : t = 1 := by
  have hv := congrArg Subtype.val h
  apply Subtype.ext
  change ((t:ℝ)+1)/2 = 1 at hv
  change (t:ℝ)=1
  linarith

lemma actual_kept_arc_misses_root_midpoint (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : KeptEdge N) (t : unitInterval) :
    D.arc (.inl e) t ≠ rootPoint N ports D := by
  intro he
  have hi := D.edge_incidence (.inl e) (.inr ()) (by simp) t halfTime he
  exact hi.2.elim halfTime_ne_zero halfTime_ne_one

lemma actual_first_root_vertex_incidence (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (v : V) (t : unitInterval)
    (he : firstRootArc N ports D t = liftPoint N ports D v) :
    v = N.graph.source ports.first ∨ v = N.graph.target ports.first := by
  by_cases hv : v = N.root
  · exact Or.inl (hv.trans ports.source_first.symm)
  · rw [liftPoint_nonroot N ports D v hv] at he
    change D.arc (.inr ()) (leftTime (unitInterval.symm t)) = D.point ⟨v,hv⟩ at he
    rcases D.vertex_incidence (.inr ()) ⟨v,hv⟩ _ he with hf | hs
    · exact Or.inr (congrArg Subtype.val hf)
    · have hp : D.arc (.inr ()) (leftTime (unitInterval.symm t)) = D.arc (.inr ()) 1 :=
        he.trans ((congrArg D.point hs).trans (D.arc (.inr ())).target.symm)
      exact False.elim (left_reverse_ne_one t ((D.arc_injective (.inr ())) hp))

lemma actual_second_root_vertex_incidence (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (v : V) (t : unitInterval)
    (he : secondRootArc N ports D t = liftPoint N ports D v) :
    v = N.graph.source ports.second ∨ v = N.graph.target ports.second := by
  by_cases hv : v = N.root
  · exact Or.inl (hv.trans ports.source_second.symm)
  · rw [liftPoint_nonroot N ports D v hv] at he
    change D.arc (.inr ()) (rightTime t) = D.point ⟨v,hv⟩ at he
    rcases D.vertex_incidence (.inr ()) ⟨v,hv⟩ _ he with hf | hs
    · have hp : D.arc (.inr ()) (rightTime t) = D.arc (.inr ()) 0 :=
        he.trans ((congrArg D.point hf).trans (D.arc (.inr ())).source.symm)
      exact False.elim (right_ne_zero t ((D.arc_injective (.inr ())) hp))
    · exact Or.inr (congrArg Subtype.val hs)

lemma actual_kept_root_vertex_incidence (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : KeptEdge N) (v : V) (t : unitInterval)
    (he : keptRootArc N ports D e t = liftPoint N ports D v) :
    v = N.graph.source e.val ∨ v = N.graph.target e.val := by
  by_cases hv : v = N.root
  · subst v
    exact False.elim (actual_kept_arc_misses_root_midpoint N ports D e t (by simpa only [keptRootArc,Path.cast_coe,liftPoint_root] using he))
  · rw [liftPoint_nonroot N ports D v hv] at he
    rcases D.vertex_incidence (.inl e) ⟨v,hv⟩ t he with hs | ht
    · exact Or.inl (congrArg Subtype.val hs)
    · exact Or.inr (congrArg Subtype.val ht)

lemma actual_two_subdivided_root_arcs_intersection (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (t u : unitInterval)
    (he : firstRootArc N ports D t = secondRootArc N ports D u) :
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  have htime := D.arc_injective (.inr ()) he
  have hv := congrArg Subtype.val htime
  change (1-(t:ℝ))/2 = ((u:ℝ)+1)/2 at hv
  have ht0 := t.property.1
  have hu0 := u.property.1
  have ht : t = 0 := Subtype.ext (by change (t:ℝ)=0; linarith)
  have hu : u = 0 := Subtype.ext (by change (u:ℝ)=0; linarith)
  exact ⟨Or.inl ht,Or.inl hu⟩

lemma actual_kept_first_root_intersection (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : KeptEdge N) (t u : unitInterval)
    (he : keptRootArc N ports D e t = firstRootArc N ports D u) :
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  have hi := D.edge_incidence (.inl e) (.inr ()) (by simp) t (leftTime (unitInterval.symm u)) he
  refine ⟨hi.1,?_⟩
  rcases hi.2 with hz | ho
  · exact Or.inr (left_reverse_zero u hz)
  · exact False.elim (left_reverse_ne_one u ho)

lemma actual_kept_second_root_intersection (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : KeptEdge N) (t u : unitInterval)
    (he : keptRootArc N ports D e t = secondRootArc N ports D u) :
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  have hi := D.edge_incidence (.inl e) (.inr ()) (by simp) t (rightTime u) he
  refine ⟨hi.1,?_⟩
  rcases hi.2 with hz | ho
  · exact False.elim (right_ne_zero u hz)
  · exact Or.inr (right_one u ho)

#print axioms actual_two_subdivided_root_arcs_intersection
end G1RootSubdivisionIncidence
