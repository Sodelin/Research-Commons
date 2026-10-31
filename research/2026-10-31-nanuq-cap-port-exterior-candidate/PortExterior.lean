import CapTrace
import RemovedPointMerge
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.DenselyOrdered

/-! UNCOMPILED source-bound cap-port exterior candidate. No circular-order
or contour conclusion; all topology is on the SAME original drawing. -/
noncomputable section
namespace Nanuq.CapExterior
open Nanuq.Source G1OuterLabelledMultigraphCurves Nanuq.CapCurves Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

lemma near_endpoint (p : N.BlobPort b) :
    (N.originalPortInner b p).val ∈ nearSide N b p := .refl

lemma far_trace_disjoint_bound (p : N.BlobPort b) :
    Disjoint (sideTrace D (nearSide N b p)ᶜ) (portBound N D b p) := by
  apply Set.disjoint_left.mpr
  intro z hz hzB
  rcases hzB with hn | ⟨t,ht,rfl⟩
  · exact Set.disjoint_left.mp (sideTrace_disjoint D disjoint_compl_left) hz hn
  · have hinner := near_endpoint N b p
    by_cases hp : N.graph.bridgeQuotient.source p.val = b
    · rw [N.originalPortInner_value_outgoing b p hp] at hinner
      have hends := arc_meets_sideTrace_endpoint D (nearSide N b p)ᶜ p.val.val
        (fun h => h.1 hinner) t hz
      rcases hends with ⟨_,h⟩ | ⟨h,_⟩
      · exact h hinner
      · subst t
        have hh : (1 : unitInterval) ≤ oneHalf := by
          simpa only [retainedParameters,if_pos hp,mem_Iic] using ht
        have := show (1 : ℝ) ≤ 1/2 from hh
        norm_num at this
    · rw [N.originalPortInner_value_incoming b p (p.property.resolve_left hp)] at hinner
      have hends := arc_meets_sideTrace_endpoint D (nearSide N b p)ᶜ p.val.val
        (fun h => h.2 hinner) t hz
      rcases hends with ⟨h,_⟩ | ⟨_,h⟩
      · subst t
        have hh : oneThird ≤ (0 : unitInterval) := by
          simpa only [retainedParameters,if_neg hp,mem_Ici] using ht
        have := show (1/3 : ℝ) ≤ 0 from hh
        norm_num at this
      · exact h hinner

lemma far_trace_in_cap_complement (hb : N.NonleafBlob b) (p : N.BlobPort b) :
    sideTrace D (nearSide N b p)ᶜ ⊆ (drawing (actualRootedCapCurves N D b hb))ᶜ := by
  intro z hz hd
  exact Set.disjoint_left.mp (far_trace_disjoint_bound N D b p) hz
    (cap_drawing_bound N D b hb p hd)

def omittedParameters (p : N.BlobPort b) : Set unitInterval :=
  if N.graph.bridgeQuotient.source p.val = b then Ioi oneHalf else Iio oneThird

def omittedTail (p : N.BlobPort b) : Set Plane := D.arc p.val.val '' omittedParameters N b p

lemma omitted_parameters_complement (p : N.BlobPort b) :
    omittedParameters N b p = (retainedParameters N b p)ᶜ := by
  by_cases hp : N.graph.bridgeQuotient.source p.val = b <;>
    simp [omittedParameters,retainedParameters,hp]

lemma omitted_tail_preconnected (p : N.BlobPort b) : IsPreconnected (omittedTail N D b p) := by
  apply IsPreconnected.image _ _ (D.arc p.val.val).continuous.continuousOn
  by_cases hp : N.graph.bridgeQuotient.source p.val = b
  · simpa only [omittedParameters,if_pos hp] using
      (isPreconnected_Ioi : IsPreconnected (Ioi oneHalf))
  · simpa only [omittedParameters,if_neg hp] using
      (isPreconnected_Iio : IsPreconnected (Iio oneThird))

lemma far_point_in_tail (p : N.BlobPort b) : D.point (farVertex N b p) ∈ omittedTail N D b p := by
  by_cases hp : N.graph.bridgeQuotient.source p.val = b
  · refine ⟨1,?_,?_⟩
    · norm_num [omittedParameters,hp,oneHalf]
    · simpa only [farVertex,if_pos hp] using (D.arc p.val.val).target
  · refine ⟨0,?_,?_⟩
    · norm_num [omittedParameters,hp,oneThird]
    · simpa only [farVertex,if_neg hp] using (D.arc p.val.val).source

lemma port_tip_in_tail_closure (p : N.BlobPort b) :
    D.arc p.val.val (portParameter N b p) ∈ closure (omittedTail N D b p) := by
  apply mem_closure_image (D.arc p.val.val).continuous.continuousAt
  by_cases hp : N.graph.bridgeQuotient.source p.val = b
  · simp only [portParameter,omittedParameters,if_pos hp]
    rw [closure_Ioi' (show (Ioi oneHalf).Nonempty from ⟨1,by norm_num [oneHalf]⟩)]
    exact le_rfl
  · simp only [portParameter,omittedParameters,if_neg hp]
    rw [closure_Iio' (show (Iio oneThird).Nonempty from ⟨0,by norm_num [oneThird]⟩)]
    exact le_rfl

lemma omitted_tail_in_cap_complement (hb : N.NonleafBlob b) (p : N.BlobPort b) :
    omittedTail N D b p ⊆ (drawing (actualRootedCapCurves N D b hb))ᶜ := by
  rintro z ⟨t,ht,rfl⟩ hz
  have hzB := cap_drawing_bound N D b hb p hz
  rcases hzB with hn | ⟨u,hu,he⟩
  · have hfar := far_not_near N b p
    by_cases hp : N.graph.bridgeQuotient.source p.val = b
    · simp only [farVertex,if_pos hp] at hfar
      rcases arc_meets_sideTrace_endpoint D (nearSide N b p) p.val.val
          (fun h => hfar h.2) t hn with ⟨ht0,_⟩ | ⟨_,hbad⟩
      · subst t
        have hh : oneHalf < (0 : unitInterval) := by
          simpa only [omittedParameters,if_pos hp,mem_Ioi] using ht
        have := show (1/2 : ℝ) < 0 from hh
        norm_num at this
      · exact hfar hbad
    · simp only [farVertex,if_neg hp] at hfar
      rcases arc_meets_sideTrace_endpoint D (nearSide N b p) p.val.val
          (fun h => hfar h.1) t hn with ⟨_,hbad⟩ | ⟨ht1,_⟩
      · exact hfar hbad
      · subst t
        have hh : (1 : unitInterval) < oneThird := by
          simpa only [omittedParameters,if_neg hp,mem_Iio] using ht
        have := show (1 : ℝ) < 1/3 from hh
        norm_num at this
  · have hut : u = t := D.arc_injective p.val.val he
    subst u
    exact (omitted_parameters_complement N b p ▸ ht) hu

/-- An actual original port fibre supplies the original-ID path from the
far endpoint to a globally outer taxon. All its traces are absent from the cap. -/
lemma far_point_in_outer_component (hb : N.NonleafBlob b)
    (face : TaxonOuterFace D N.leaf) (p : N.BlobPort b) :
    D.point (farVertex N b p) ∈ connectedComponentIn
      (drawing (actualRootedCapCurves N D b hb))ᶜ face.outside := by
  obtain ⟨x,hx⟩ := N.blobProjection_surjective b hb p
  have hw := port_fibre_far N b hb p x hx
  have htrace := far_trace_in_cap_complement N D b hb p
  have hxFar := far_walk_not_near N b p hw
  have hxU : D.point (N.leaf x) ∉ drawing (actualRootedCapCurves N D b hb) :=
    htrace (Or.inl ⟨N.leaf x,hxFar,rfl⟩)
  have hOld := Nanuq.RemovedPointMerge.old_face_subset_new_component
    (actualRootedCapCurves_drawing_subset N D b hb) hxU (face.taxon_on_face x)
  have ha := hOld (mem_connectedComponentIn face.outside_not_drawing)
  have hwalk := N.graph.ureach_symm (far_walk_internal N b p hw)
  have hfar := point_same_component_of_original_walk D
    (fun e he => (arc_range_subset_sideTrace D e he.1 he.2).trans htrace) hxU hwalk
  rw [← connectedComponentIn_eq ha]
  exact hfar

/-- New port labels lie on ONE unbounded component of the literal capped
original drawing. This is exterior incidence, not port cyclic-order compatibility. -/
def actualRootedCapOuterFace (hb : N.NonleafBlob b) (face : TaxonOuterFace D N.leaf) :
    TaxonOuterFace (actualRootedCapCurves N D b hb) (N.actualRootedCapLeaf b) where
  outside := face.outside
  outside_not_drawing := fun h => face.outside_not_drawing
    (actualRootedCapCurves_drawing_subset N D b hb h)
  component_unbounded := fun h => face.component_unbounded (h.subset
    (connectedComponentIn_mono face.outside
      (compl_subset_compl.mpr (actualRootedCapCurves_drawing_subset N D b hb))))
  taxon_on_face := by
    intro p
    have hfar := far_point_in_outer_component N D b hb face p
    have htail := (omitted_tail_preconnected N D b p).subset_connectedComponentIn
      (far_point_in_tail N D b p) (omitted_tail_in_cap_complement N D b hb p)
    have heq := connectedComponentIn_eq hfar
    have ht : omittedTail N D b p ⊆ connectedComponentIn
        (drawing (actualRootedCapCurves N D b hb))ᶜ face.outside := by
      rw [heq]
      exact htail
    exact closure_mono ht (port_tip_in_tail_closure N D b p)

#print axioms actualRootedCapOuterFace
end Nanuq.CapExterior
