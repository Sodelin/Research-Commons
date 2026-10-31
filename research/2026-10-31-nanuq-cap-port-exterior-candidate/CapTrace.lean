import SourceSides

/-! Working exact drawing bound for ONE original port cut. UNCOMPILED. -/
noncomputable section
namespace Nanuq.CapExterior
open Nanuq.Source G1OuterLabelledMultigraphCurves Nanuq.CapCurves Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

def retainedParameters (p : N.BlobPort b) : Set unitInterval :=
  if N.graph.bridgeQuotient.source p.val = b then Iic oneHalf else Ici oneThird

def portBound (p : N.BlobPort b) : Set Plane :=
  sideTrace D (nearSide N b p) ∪ D.arc p.val.val '' retainedParameters N b p

lemma other_port_trace_bound (p q : N.BlobPort b) (hpq : q ≠ p) (t : unitInterval) :
    D.arc q.val.val t ∈ portBound N D b p := by
  obtain ⟨hs,ht⟩ := other_port_near N b p q hpq
  exact Or.inl (arc_range_subset_sideTrace D _ hs ht ⟨t,rfl⟩)

lemma port_tip_bound (p q : N.BlobPort b) :
    D.arc q.val.val (portParameter N b q) ∈ portBound N D b p := by
  by_cases h : q = p
  · subst q
    apply Or.inr
    refine ⟨portParameter N b p,?_,rfl⟩
    by_cases hp : N.graph.bridgeQuotient.source p.val = b <;>
      simp [retainedParameters,portParameter,hp]
  · exact other_port_trace_bound N D b p q h _

lemma incoming_root_bound (p : N.BlobPort b) (r : {u : Unit // b ≠ N.graph.blobOf N.root}) :
    D.arc (N.originalIncomingBlobPort b r.property).val.val twoThirds ∈ portBound N D b p := by
  let q := N.originalIncomingBlobPort b r.property
  by_cases h : q = p
  · have hp : ¬ N.graph.bridgeQuotient.source p.val = b := by
      rw [← h]
      exact N.originalRootedCapIncoming_outside_source b r.property
    change D.arc q.val.val twoThirds ∈ _
    rw [h]
    apply Or.inr
    refine ⟨twoThirds,?_,rfl⟩
    norm_num [retainedParameters,hp,oneThird,twoThirds]
  · exact other_port_trace_bound N D b p q h _

lemma cap_point_bound (p : N.BlobPort b) (v : N.RootedCapVertex b) :
    capPoint N D b v ∈ portBound N D b p := by
  rcases v with v | (q | r)
  · exact Or.inl (Or.inl ⟨v.val,blob_vertex_near N b p v,rfl⟩)
  · exact port_tip_bound N D b p q
  · exact incoming_root_bound N D b p r

lemma cap_raw_arc_bound (p : N.BlobPort b) (e : N.RootedCapArc b) (t : unitInterval) :
    capRawArc N D b e t ∈ portBound N D b p := by
  rcases e with e | (q | r)
  · exact Or.inl (arc_range_subset_sideTrace D e.val
      (blob_vertex_near N b p ⟨_,e.property.1⟩)
      (blob_vertex_near N b p ⟨_,e.property.2⟩) ⟨t,rfl⟩)
  · by_cases h : q = p
    · subst q
      by_cases hp : N.graph.bridgeQuotient.source p.val = b
      · simp only [capRawArc,if_pos hp]
        apply Or.inr
        refine ⟨_,?_,rfl⟩
        change affineParameter 0 oneHalf t ∈ retainedParameters N b p
        simp only [retainedParameters,if_pos hp,mem_Iic]
        change (affineParameter 0 oneHalf t : ℝ) ≤ (oneHalf : ℝ)
        simp only [affineParameter,oneHalf]
        nlinarith [t.property.2]
      · simp only [capRawArc,if_neg hp]
        apply Or.inr
        refine ⟨_,?_,rfl⟩
        change affineParameter twoThirds oneThird t ∈ retainedParameters N b p
        simp only [retainedParameters,if_neg hp,mem_Ici]
        change (oneThird : ℝ) ≤ (affineParameter twoThirds oneThird t : ℝ)
        simp only [affineParameter,oneThird,twoThirds]
        nlinarith [t.property.2]
    · by_cases hq : N.graph.bridgeQuotient.source q.val = b <;>
        simp only [capRawArc,hq,ite_true,ite_false] <;>
        exact other_port_trace_bound N D b p q h _
  · let q := N.originalIncomingBlobPort b r.property
    by_cases h : q = p
    · have hp : ¬ N.graph.bridgeQuotient.source p.val = b := by
        rw [← h]
        exact N.originalRootedCapIncoming_outside_source b r.property
      change D.arc q.val.val (affineParameter twoThirds 1 t) ∈ _
      rw [h]
      apply Or.inr
      refine ⟨_,?_,rfl⟩
      simp only [retainedParameters,if_neg hp,mem_Ici]
      change (oneThird : ℝ) ≤ (affineParameter twoThirds 1 t : ℝ)
      simp only [affineParameter,oneThird,twoThirds]
      nlinarith [t.property.1]
    · exact other_port_trace_bound N D b p q h _

lemma cap_drawing_bound (hb : N.NonleafBlob b) (p : N.BlobPort b) :
    drawing (actualRootedCapCurves N D b hb) ⊆ portBound N D b p := by
  intro z hz
  rcases hz with ⟨v,rfl⟩ | hz
  · exact cap_point_bound N D b p v
  · obtain ⟨e,t,rfl⟩ := Set.mem_iUnion.mp hz
    exact cap_raw_arc_bound N D b p e t

end Nanuq.CapExterior
