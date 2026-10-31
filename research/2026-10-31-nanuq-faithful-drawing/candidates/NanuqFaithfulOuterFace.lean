import NanuqFaithfulSupplierDrawing
import CoordinateFace
set_option debug.skipKernelTC false

/-! Exact full-original-interface face transport. Source candidate pending sole
compiler; no extracted G1 interface or order certificate is imported. -/
namespace NanuqFaithfulSupplierDrawing
open Set Nanuq.Source G1OuterLabelledMultigraphCurves
variable {V E X : Type*} {G : EdgeGraph V E}

theorem actual_taxon_outer_face (D : PlanarCurves G) (leaf : X → V)
    (face : TaxonOuterFace D leaf) :
    coordinates face.outside ∉ Graph.pointSet (graph D) (curve D) ∧
    ¬ Bornology.IsBounded (connectedComponentIn (Graph.pointSet (graph D) (curve D))ᶜ
      (coordinates face.outside)) ∧
    ∀ x, vertex D (leaf x) ∈ closure
      (connectedComponentIn (Graph.pointSet (graph D) (curve D))ᶜ (coordinates face.outside)) := by
  rw [pointSet_eq D]
  simpa only [vertex] using Nanuq.CoordinateFace.outer_face_transfer
    coordinates (drawing D) face.outside (fun x => D.point (leaf x))
    face.outside_not_drawing face.component_unbounded face.taxon_on_face

#print axioms actual_taxon_outer_face
end NanuqFaithfulSupplierDrawing
