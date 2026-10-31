import PendantCapExport
import OneExitExterior
import PrefixArc
import AmbientTransport

/-! UNCOMPILED join to the SAME original exterior component. No extra
local collar, cyclic order or relative slit-domain connectivity premise. -/
noncomputable section
namespace Nanuq.Pendant
open Set Schoenflies unitInterval Nanuq.Source
open scoped Graph

theorem original_taxon_exterior_one_exit {V E X : Type*}
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
    (N : RootedBinary V E X) (D : G1OuterLabelledMultigraphCurves.PlanarCurves N.graph)
    (face : G1OuterLabelledMultigraphCurves.TaxonOuterFace D N.leaf) (x : X) :
    ∃ (e : E) (f : ℝ → Plane) (H : Plane ≃ₜ Plane) (r b t : ℝ) (C : Set Plane),
      N.graph.target e=N.leaf x ∧ ContinuousOn f I ∧ InjOn f I ∧
      f '' I=Graph.edgeArc (NanuqFaithfulSupplierDrawing.curve D) e ∧
      f 0=NanuqFaithfulSupplierDrawing.vertex D (N.leaf x) ∧
      f 1=NanuqFaithfulSupplierDrawing.vertex D (N.graph.source e) ∧
      0 < r ∧ r < b ∧ t ∈ Ioo (1/2) (13/24) ∧ IsJordanCurve C ∧
      (∀ y : ℝ, |y| < r → Plane.mk r y ∈ C) ∧
      H (f (1/2))=0 ∧ H (f (13/24))=Plane.mk b 0 ∧ H (f t)=Plane.mk r 0 ∧
      H '' (f '' Icc (1/2) (13/24))=segment ℝ (0:Plane) (Plane.mk b 0) ∧
      C ∩ (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D))={Plane.mk r 0} ∧
      (C ∪ inside C) ∩ (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D))=H '' (f '' Icc 0 t) ∧
      Plane.mk r (r/2) ∈ C \ (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D)) ∧
      Plane.mk r (-r/2) ∈ C \ (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
        G1OuterLabelledMultigraphCurves.drawing D)) ∧
      Plane.mk r (-r/2) ∈ connectedComponentIn
        (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
          G1OuterLabelledMultigraphCurves.drawing D))ᶜ (Plane.mk r (r/2)) ∧
      C \ {Plane.mk r 0} ⊆ connectedComponentIn
        (H '' (NanuqFaithfulSupplierDrawing.coordinates ''
          G1OuterLabelledMultigraphCurves.drawing D))ᶜ
        (H (NanuqFaithfulSupplierDrawing.coordinates face.outside)) := by
  obtain ⟨e,f,H,r,b,t,C,het,hfc,hfi,him,hf0,hf1,hr,hrb,ht,hC,hcap,
    hmid,hend,hcut,hseg,hinter,hclosed,hu,hd,hreturn⟩ := original_taxon_one_exit_cap N D x
  let K := H '' (NanuqFaithfulSupplierDrawing.coordinates ''
    G1OuterLabelledMultigraphCurves.drawing D)
  let A := H '' (f '' Icc 0 t)
  have htpos : 0<t := by linarith [ht.1]
  have ht1 : t≤1 := by linarith [ht.2]
  have hArc : IsArcBetween A (H (f 0)) (H (f t)) := by
    have h := prefix_isArcBetween (fun u => H (f u))
      (H.continuous.comp_continuousOn hfc)
      (fun u hu v hv heq => hfi hu hv (H.injective heq)) htpos ht1
    simpa only [A,Set.image_image,Function.comp_apply] using h
  have hpA : H (f 0)∈A := hArc.left_mem
  have hpq : H (f 0)≠Plane.mk r 0 := by
    intro heq
    have heqt : f 0=f t := H.injective (heq.trans hcut.symm)
    have h0t := hfi zero_mem_I ⟨htpos.le,ht1⟩ heqt
    linarith
  have hpinside : H (f 0)∈inside C := by
    have hp : H (f 0)∈(C ∪ inside C) ∩ K := hclosed.symm ▸ hpA
    rcases hp.1 with hpC | hpI
    · have hq : H (f 0)=Plane.mk r 0 := by
        have hm : H (f 0)∈({Plane.mk r 0}:Set Plane) :=
          hinter ▸ (show H (f 0)∈C∩K from ⟨hpC,hp.2⟩)
        exact hm
      exact False.elim (hpq hq)
    · exact hpI
  have hcoord := Nanuq.AmbientTransport.outer_face_transfer
    NanuqFaithfulSupplierDrawing.coordinates.toHomeomorph
    (G1OuterLabelledMultigraphCurves.drawing D) face.outside
    (fun y : X => D.point (N.leaf y))
    face.outside_not_drawing face.component_unbounded face.taxon_on_face
  have hH := Nanuq.AmbientTransport.outer_face_transfer H
    (NanuqFaithfulSupplierDrawing.coordinates '' G1OuterLabelledMultigraphCurves.drawing D)
    (NanuqFaithfulSupplierDrawing.coordinates face.outside)
    (fun y : X => NanuqFaithfulSupplierDrawing.coordinates (D.point (N.leaf y)))
    hcoord.1 hcoord.2.1 hcoord.2.2
  have hpcl : H (f 0) ∈ closure (connectedComponentIn Kᶜ
      (H (NanuqFaithfulSupplierDrawing.coordinates face.outside))) := by
    simpa only [K,hf0,NanuqFaithfulSupplierDrawing.vertex] using hH.2.2 x
  have hboundary := one_exit_specified_component hC hArc.isArc hinter hclosed hpinside hpcl hu
  exact ⟨e,f,H,r,b,t,C,het,hfc,hfi,him,hf0,hf1,hr,hrb,ht,hC,hcap,
    hmid,hend,hcut,hseg,hinter,hclosed,hu,hd,hreturn,hboundary⟩

#print axioms original_taxon_exterior_one_exit
end Nanuq.Pendant
