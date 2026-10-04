import G1SharpOriginalSegmentsToFaithfulCurves

/-! The accepted ALL-n original rays/corridor certificate gives the EXACT
same unbounded complementary component incident to every original taxon.
Connectedness, unboundedness and closure are proved in the real plane; this
is not a split-compatible-order or separate drawing witness. -/
namespace G1SharpOriginalUnboundedTaxonFace
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1SharpCoreCombOuterEmbedding
open G1OuterLabelledMultigraphCurves G1SharpOriginalSegmentsToFaithfulCurves Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def commonCorridor : Set Plane := range (fun x : ℝ => (x,(-1:ℝ)))

lemma common_corridor_preconnected : IsPreconnected commonCorridor := by
  rw [commonCorridor,← image_univ]
  exact isPreconnected_univ.image _ (by fun_prop)

lemma actual_corridor_subset_component (N : RootedBinary V E X) (D : OriginalOuterEmbedding N.graph) :
    commonCorridor ⊆ connectedComponentIn
      (G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D))ᶜ (0,-1) := by
  apply common_corridor_preconnected.subset_connectedComponentIn ⟨0,rfl⟩
  rintro p ⟨x,rfl⟩
  exact actual_corridor_misses_full_drawing N D x

lemma actual_shared_component_unbounded (N : RootedBinary V E X) (D : OriginalOuterEmbedding N.graph) :
    ¬ Bornology.IsBounded (connectedComponentIn
      (G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D))ᶜ (0,-1)) := by
  intro hb
  have hc := hb.subset (actual_corridor_subset_component N D)
  obtain ⟨C,hC⟩ := Metric.isBounded_range_iff.mp hc
  have h := hC (C+1) 0
  have hbound : |C+1| ≤ C := by
    simpa only [Prod.dist_eq,Real.dist_eq,sub_zero,sub_self,abs_zero,max_eq_left (abs_nonneg (C+1))] using h
  linarith [le_abs_self (C+1)]

lemma actual_vertex_on_same_unbounded_face (N : RootedBinary V E X) (D : OriginalOuterEmbedding N.graph)
    (v : V) : D.point v ∈ closure (connectedComponentIn
      (G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D))ᶜ (0,-1)) := by
  let rayMap : ℝ → Plane := fun s => ((D.point v).1,(D.point v).2-s)
  let ray : Set Plane := rayMap '' Ioi (0:ℝ)
  have hf : Continuous rayMap := by fun_prop
  have hpre : IsPreconnected ray := isPreconnected_Ioi.image rayMap hf.continuousOn
  have hrsubset : ray ⊆ (G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D))ᶜ := by
    rintro p ⟨s,hs,rfl⟩
    exact actual_downward_ray_misses_full_drawing N D v s hs
  have hcsubset : commonCorridor ⊆ (G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D))ᶜ := by
    rintro p ⟨x,rfl⟩
    exact actual_corridor_misses_full_drawing N D x
  obtain ⟨s,hs,he⟩ := D.ray_reaches_corridor v
  have hinter : (commonCorridor ∩ ray).Nonempty :=
    ⟨((D.point v).1,-1),⟨⟨(D.point v).1,rfl⟩,⟨s,hs,he⟩⟩⟩
  have hwhole := IsPreconnected.union' hinter common_corridor_preconnected hpre
  have hcomponent : commonCorridor ∪ ray ⊆ connectedComponentIn
      (G1OuterLabelledMultigraphCurves.drawing (originalSegmentCurves N D))ᶜ (0,-1) :=
    hwhole.subset_connectedComponentIn (Or.inl ⟨0,rfl⟩) (union_subset hcsubset hrsubset)
  have hz : (0:ℝ) ∈ closure (Ioi (0:ℝ)) := by rw [closure_Ioi (0:ℝ)]; exact (show (0:ℝ) ≤ 0 from le_rfl)
  have hcl := mem_closure_image hf.continuousAt hz
  have hv : D.point v ∈ closure ray := by
    simpa only [ray,rayMap,sub_zero,Prod.eta] using hcl
  exact closure_mono (subset_union_right.trans hcomponent) hv

/-- The original ALL-n segment certificate is now admitted by the exact
faithful taxon-only curve/unbounded-component definition, on the SAME graph. -/
noncomputable def actualOriginalSegmentOuterCurves (N : RootedBinary V E X) (D : OriginalOuterEmbedding N.graph) :
    OuterLabelledCurves N.graph N.leaf where
  curves := originalSegmentCurves N D
  outer_face :=
    { outside := (0,-1)
      outside_not_drawing := actual_corridor_misses_full_drawing N D 0
      component_unbounded := actual_shared_component_unbounded N D
      taxon_on_face := fun x => actual_vertex_on_same_unbounded_face N D (N.leaf x) }

#print axioms actualOriginalSegmentOuterCurves
end G1SharpOriginalUnboundedTaxonFace
