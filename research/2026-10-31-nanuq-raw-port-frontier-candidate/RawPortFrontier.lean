import PortExterior
import OriginalBlobSupplier

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.RawPortFrontier
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves Nanuq.CapCurves Nanuq.CapExterior Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

/-- The actual raw blob is a literal part of the already realized cap.
Its nonbridge original ID is mapped to the corresponding cap-internal tag. -/
theorem raw_drawing_subset_cap (hb : N.NonleafBlob b) :
    drawing (blobCurves D b) ⊆ drawing (actualRootedCapCurves N D b hb) := by
  rintro z (⟨v,rfl⟩ | hz)
  · exact Or.inl ⟨Sum.inl ⟨v.val,v.property⟩,rfl⟩
  · obtain ⟨e,t,rfl⟩ := mem_iUnion.mp hz
    let ce : N.RootedCapArc b := Sum.inl ⟨e.val,e.property.2,
      ((originalBlob N.graph b).target e).property⟩
    exact Or.inr (mem_iUnion.mpr ⟨ce,t,rfl⟩)

/-- The actual raw trace is on the near side of every incident ORIGINAL bridge. -/
theorem raw_drawing_subset_near (p : N.BlobPort b) :
    drawing (blobCurves D b) ⊆ sideTrace D (nearSide N b p) := by
  rintro z (⟨v,rfl⟩ | hz)
  · exact Or.inl ⟨v.val,blob_vertex_near N b p ⟨v.val,v.property⟩,rfl⟩
  · obtain ⟨e,t,rfl⟩ := mem_iUnion.mp hz
    apply arc_range_subset_sideTrace D e.val
    · exact blob_vertex_near N b p ⟨_,e.property.2⟩
    · exact blob_vertex_near N b p ⟨_,((originalBlob N.graph b).target e).property⟩
    · exact ⟨t,rfl⟩

/-- Remove ONLY the actual inner attachment endpoint from the complete original
bridge. For an incoming port this includes BOTH cap subarcs [1/3,2/3] and
[2/3,1], with only the endpoint 1 removed. -/
def awayParameters (p : N.BlobPort b) : Set unitInterval :=
  if N.graph.bridgeQuotient.source p.val=b then Ioi 0 else Iio 1

def awayBridge (p : N.BlobPort b) : Set Plane := D.arc p.val.val '' awayParameters N b p

theorem awayBridge_preconnected (p : N.BlobPort b) : IsPreconnected (awayBridge N D b p) := by
  apply IsPreconnected.image _ _ (D.arc p.val.val).continuous.continuousOn
  by_cases hp : N.graph.bridgeQuotient.source p.val=b
  · simpa only [awayParameters,if_pos hp] using
      (isPreconnected_Ioi : IsPreconnected (Ioi (0:unitInterval)))
  · simpa only [awayParameters,if_neg hp] using
      (isPreconnected_Iio : IsPreconnected (Iio (1:unitInterval)))

theorem far_point_mem_awayBridge (p : N.BlobPort b) :
    D.point (farVertex N b p) ∈ awayBridge N D b p := by
  by_cases hp : N.graph.bridgeQuotient.source p.val=b
  · refine ⟨1,?_,?_⟩
    · simp [awayParameters,hp]
    · simpa only [farVertex,if_pos hp] using (D.arc p.val.val).target
  · refine ⟨0,?_,?_⟩
    · simp [awayParameters,hp]
    · simpa only [farVertex,if_neg hp] using (D.arc p.val.val).source

theorem awayBridge_subset_raw_complement (p : N.BlobPort b) :
    awayBridge N D b p ⊆ (drawing (blobCurves D b))ᶜ := by
  rintro z ⟨t,ht,rfl⟩ hz
  have hn := raw_drawing_subset_near N D b p hz
  have hfar := far_not_near N b p
  by_cases hp : N.graph.bridgeQuotient.source p.val=b
  · simp only [farVertex,if_pos hp] at hfar
    rcases arc_meets_sideTrace_endpoint D (nearSide N b p) p.val.val
      (fun h => hfar h.2) t hn with ⟨ht0,_⟩ | ⟨_,hbad⟩
    · subst t
      have hh : (0:unitInterval)<0 := by simpa [awayParameters,hp] using ht
      exact (lt_irrefl _ hh)
    · exact hfar hbad
  · simp only [farVertex,if_neg hp] at hfar
    rcases arc_meets_sideTrace_endpoint D (nearSide N b p) p.val.val
      (fun h => hfar h.1) t hn with ⟨_,hbad⟩ | ⟨ht1,_⟩
    · exact hfar hbad
    · subst t
      have hh : (1:unitInterval)<1 := by simpa [awayParameters,hp] using ht
      exact (lt_irrefl _ hh)

theorem attachment_mem_awayBridge_closure (p : N.BlobPort b) :
    D.point (N.originalPortInner b p).val ∈ closure (awayBridge N D b p) := by
  by_cases hp : N.graph.bridgeQuotient.source p.val=b
  · rw [N.originalPortInner_value_outgoing b p hp,← (D.arc p.val.val).source]
    apply mem_closure_image (D.arc p.val.val).continuous.continuousAt
    simp only [awayParameters,if_pos hp]
    rw [closure_Ioi' (show (Ioi (0:unitInterval)).Nonempty from ⟨1,by norm_num⟩)]
    exact le_rfl
  · rw [N.originalPortInner_value_incoming b p (p.property.resolve_left hp),← (D.arc p.val.val).target]
    apply mem_closure_image (D.arc p.val.val).continuous.continuousAt
    simp only [awayParameters,if_neg hp]
    rw [closure_Iio' (show (Iio (1:unitInterval)).Nonempty from ⟨0,by norm_num⟩)]
    exact le_rfl

/-- SAME original outside basepoint throughout. The accepted cap result puts
an ACTUAL far original vertex in its exterior; raw⊆cap transfers that point,
and the connected whole bridge minus attachment propagates it to every stub. -/
theorem awayBridge_in_raw_outer_component (hb : N.NonleafBlob b)
    (face : TaxonOuterFace D N.leaf) (p : N.BlobPort b) :
    awayBridge N D b p ⊆ connectedComponentIn (drawing (blobCurves D b))ᶜ face.outside := by
  have hmono := connectedComponentIn_mono face.outside
    (compl_subset_compl.mpr (raw_drawing_subset_cap N D b hb))
  have hfar := hmono (far_point_in_outer_component N D b hb face p)
  have hwhole := (awayBridge_preconnected N D b p).subset_connectedComponentIn
    (far_point_mem_awayBridge N D b p) (awayBridge_subset_raw_complement N D b p)
  rw [← connectedComponentIn_eq hfar] at hwhole
  exact hwhole

/-- All blob sizes: actual original port attachments lie on the frontier of
ONE unbounded raw-blob complementary component. No cyclic-order conclusion. -/
theorem actual_raw_port_frontier (hb : N.NonleafBlob b) (face : TaxonOuterFace D N.leaf) :
    face.outside ∉ drawing (blobCurves D b) ∧
    ¬ Bornology.IsBounded (connectedComponentIn (drawing (blobCurves D b))ᶜ face.outside) ∧
    ∀ p : N.BlobPort b, D.point (N.originalPortInner b p).val ∈
      frontier (connectedComponentIn (drawing (blobCurves D b))ᶜ face.outside) := by
  have hsub := (raw_drawing_subset_cap N D b hb).trans
    (actualRootedCapCurves_drawing_subset N D b hb)
  have hnot : face.outside ∉ drawing (blobCurves D b) := fun hz => face.outside_not_drawing (hsub hz)
  have hunbounded : ¬ Bornology.IsBounded (connectedComponentIn (drawing (blobCurves D b))ᶜ face.outside) := by
    intro hbounded
    exact face.component_unbounded (hbounded.subset
      (connectedComponentIn_mono face.outside (compl_subset_compl.mpr hsub)))
  refine ⟨hnot,hunbounded,?_⟩
  intro p
  have hcl := closure_mono (awayBridge_in_raw_outer_component N D b hb face p)
    (attachment_mem_awayBridge_closure N D b p)
  have hattach : D.point (N.originalPortInner b p).val ∈ drawing (blobCurves D b) :=
    Or.inl ⟨⟨(N.originalPortInner b p).val,(N.originalPortInner b p).property⟩,rfl⟩
  rw [frontier]
  refine ⟨hcl,?_⟩
  intro hi
  exact (connectedComponentIn_subset _ _ (interior_subset hi)) hattach

#print axioms awayBridge_in_raw_outer_component
#print axioms actual_raw_port_frontier
end Nanuq.RawPortFrontier
