import G1RootSubdivisionIncidence

/-! Full original rooted drawing reconstructed from the literal
semidirected partner drawing. Thus the splice transport can start with the
accepted taxon-only outer-labelled semidirected admission, rather than a
stronger input drawing hypothesis. -/
namespace G1RootSubdivisionPlanarAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1OuterLabelledMultigraphCurves G1InjectiveHalfArcSubdivision G1OriginalRootSubdivisionData
open G1RootSubdivisionIncidence Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_original_edge_cases (N : RootedBinary V E X) (ports : RootPorts N) (e : E) :
    e = ports.first ∨ e = ports.second ∨ N.graph.source e ≠ N.root := by
  by_cases hroot : N.graph.source e = N.root
  · exact (ports.exhaustive e hroot).elim Or.inl (Or.inr ∘ Or.inl)
  · exact Or.inr (Or.inr hroot)

lemma actual_lift_arc_injective (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : E) : Function.Injective (liftArc N ports D e) := by
  rcases actual_original_edge_cases N ports e with hf | hs | hk
  · subst e
    rw [liftArc_first]
    exact (actual_left_half_injective (D.arc (.inr ())) (D.arc_injective (.inr ()))).comp
      unitInterval.symm_involutive.injective
  · subst e
    rw [liftArc_second]
    exact actual_right_half_injective (D.arc (.inr ())) (D.arc_injective (.inr ()))
  · rw [liftArc_kept N ports D ⟨e,hk⟩]
    exact D.arc_injective (.inl ⟨e,hk⟩)

lemma actual_lift_vertex_incidence (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e : E) (v : V) (t : unitInterval)
    (he : liftArc N ports D e t = liftPoint N ports D v) : v = N.graph.source e ∨ v = N.graph.target e := by
  rcases actual_original_edge_cases N ports e with hf | hs | hk
  · subst e; rw [liftArc_first] at he
    exact actual_first_root_vertex_incidence N ports D v t he
  · subst e; rw [liftArc_second] at he
    exact actual_second_root_vertex_incidence N ports D v t he
  · rw [liftArc_kept N ports D ⟨e,hk⟩] at he
    exact actual_kept_root_vertex_incidence N ports D ⟨e,hk⟩ v t he

lemma actual_lift_edge_incidence (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) (e f : E) (hef : e ≠ f) (t u : unitInterval)
    (he : liftArc N ports D e t = liftArc N ports D f u) :
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  rcases actual_original_edge_cases N ports e with hf | hs | hk
  · subst e; rw [liftArc_first] at he
    rcases actual_original_edge_cases N ports f with hf | hs | hk
    · exact False.elim (hef hf.symm)
    · subst f; rw [liftArc_second] at he
      exact actual_two_subdivided_root_arcs_intersection N ports D t u he
    · rw [liftArc_kept N ports D ⟨f,hk⟩] at he
      have h := actual_kept_first_root_intersection N ports D ⟨f,hk⟩ u t he.symm
      exact ⟨h.2,h.1⟩
  · subst e; rw [liftArc_second] at he
    rcases actual_original_edge_cases N ports f with hf | hs | hk
    · subst f; rw [liftArc_first] at he
      have h := actual_two_subdivided_root_arcs_intersection N ports D u t he.symm
      exact ⟨h.2,h.1⟩
    · exact False.elim (hef hs.symm)
    · rw [liftArc_kept N ports D ⟨f,hk⟩] at he
      have h := actual_kept_second_root_intersection N ports D ⟨f,hk⟩ u t he.symm
      exact ⟨h.2,h.1⟩
  · rw [liftArc_kept N ports D ⟨e,hk⟩] at he
    rcases actual_original_edge_cases N ports f with hf | hs | hk'
    · subst f; rw [liftArc_first] at he
      exact actual_kept_first_root_intersection N ports D ⟨e,hk⟩ t u he
    · subst f; rw [liftArc_second] at he
      exact actual_kept_second_root_intersection N ports D ⟨e,hk⟩ t u he
    · rw [liftArc_kept N ports D ⟨f,hk'⟩] at he
      exact D.edge_incidence (.inl ⟨e,hk⟩) (.inl ⟨f,hk'⟩)
        (by intro h; exact hef (congrArg (fun x : SuppressedEdge N => x.elim Subtype.val (fun _ => e)) h)) t u he

noncomputable def actualRootSubdivisionPlanarCurves (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) : PlanarCurves N.graph where
  point := liftPoint N ports D
  point_injective := actual_lift_point_injective N ports D
  arc := liftArc N ports D
  arc_injective := actual_lift_arc_injective N ports D
  vertex_incidence := actual_lift_vertex_incidence N ports D
  edge_incidence := actual_lift_edge_incidence N ports D

theorem actual_root_subdivision_drawing_subset (N : RootedBinary V E X) (ports : RootPorts N)
    (D : PlanarCurves (suppressedGraph N ports)) : drawing (actualRootSubdivisionPlanarCurves N ports D) ⊆ drawing D := by
  intro p hp
  rcases hp with hp | hp
  · obtain ⟨v,hv⟩ := hp
    change liftPoint N ports D v = p at hv
    by_cases hroot : v = N.root
    · subst v
      rw [liftPoint_root] at hv
      exact Or.inr (mem_iUnion.mpr ⟨.inr (),⟨halfTime,hv⟩⟩)
    · rw [liftPoint_nonroot N ports D v hroot] at hv
      exact Or.inl ⟨⟨v,hroot⟩,hv⟩
  · obtain ⟨e,he⟩ := mem_iUnion.mp hp
    obtain ⟨t,ht⟩ := he
    change liftArc N ports D e t = p at ht
    rcases actual_original_edge_cases N ports e with hf | hs | hk
    · subst e; rw [liftArc_first] at ht
      exact Or.inr (mem_iUnion.mpr ⟨.inr (),⟨leftTime (unitInterval.symm t),ht⟩⟩)
    · subst e; rw [liftArc_second] at ht
      exact Or.inr (mem_iUnion.mpr ⟨.inr (),⟨rightTime t,ht⟩⟩)
    · rw [liftArc_kept N ports D ⟨e,hk⟩] at ht
      exact Or.inr (mem_iUnion.mpr ⟨.inl ⟨e,hk⟩,⟨t,ht⟩⟩)

noncomputable def actualRootSubdivisionOuterCurves (N : RootedBinary V E X) (ports : RootPorts N)
    (D : OuterLabelledCurves (suppressedGraph N ports) (suppressedLeaf N)) :
    OuterLabelledCurves N.graph N.leaf where
  curves := actualRootSubdivisionPlanarCurves N ports D.curves
  outer_face := Classical.choice (actual_outer_face_of_drawing_subset D.curves
    (actualRootSubdivisionPlanarCurves N ports D.curves) (suppressedLeaf N) N.leaf D.outer_face
    (actual_root_subdivision_drawing_subset N ports D.curves)
    (fun x => liftPoint_nonroot N ports D.curves (N.leaf x) (N.leaf_ne_root x)))

#print axioms actualRootSubdivisionOuterCurves
end G1RootSubdivisionPlanarAdmission
