import RawPortFrontier
import CoordinateFace
import ContinuousFaceCycles

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.RawPortFrontier
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set
open scoped Graph
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

/-- At least three original blob vertices: one NAMED actual outside cycle
contains all original port attachment vertices. Original nonbridge edge IDs,
original curves and the shared original outside basepoint are retained.
This is incidence, NOT a cyclic order or a cap/global traversal theorem. -/
theorem actual_raw_port_outer_cycle (hb : N.NonleafBlob b)
    (face : TaxonOuterFace D N.leaf)
    (hthree : ∃ a c d : BlobVertex N.graph b, a≠c ∧ a≠d ∧ c≠d) :
    ∃ (e : BlobEdge N.graph b) (u v : Schoenflies.Plane) (es : List (BlobEdge N.graph b)),
      Graph.IsFaceCycle (graph (blobCurves D b)) (curve (blobCurves D b))
        (coordinates face.outside) e u v es ∧
      Schoenflies.IsJordanCurve (Graph.edgesCover (curve (blobCurves D b)) (e::es)) ∧
      Graph.face (graph (blobCurves D b)) (curve (blobCurves D b)) (coordinates face.outside) =
        Schoenflies.outside (Graph.edgesCover (curve (blobCurves D b)) (e::es)) ∧
      ∀ p : N.BlobPort b, coordinates (D.point (N.originalPortInner b p).val) ∈
        Graph.edgesCover (curve (blobCurves D b)) (e::es) := by
  let G := graph (blobCurves D b)
  let φ := curve (blobCurves D b)
  let R := drawing (blobCurves D b)
  let F := connectedComponentIn Rᶜ face.outside
  haveI : Finite (BlobVertex N.graph b) := by unfold BlobVertex; infer_instance
  haveI : G.Finite := by
    refine ⟨?_,?_⟩
    · change (range (vertex (blobCurves D b))).Finite
      exact Set.finite_range _
    · change (univ : Set (BlobEdge N.graph b)).Finite
      exact Set.toFinite _
  obtain ⟨hnot,hub,hfront⟩ := actual_raw_port_frontier N D b hb face
  have hdraw := isDrawing (blobCurves D b)
  have htwo := actual_binary_blob_two_connected N D b hthree
  have hnotG : coordinates face.outside ∈ Graph.exterior G φ := by
    change coordinates face.outside ∉ Graph.pointSet G φ
    rw [pointSet_eq (blobCurves D b)]
    rintro ⟨x,hx,heq⟩
    exact hnot (coordinates.injective heq ▸ hx)
  have hcomp : coordinates '' F = Graph.face G φ (coordinates face.outside) := by
    change coordinates '' connectedComponentIn Rᶜ face.outside =
      connectedComponentIn (Graph.pointSet G φ)ᶜ (coordinates face.outside)
    rw [pointSet_eq (blobCurves D b)]
    exact Nanuq.CoordinateFace.component_image coordinates R face.outside hnot
  have hunbounded : ¬ Bornology.IsBounded (Graph.face G φ (coordinates face.outside)) := by
    rw [← hcomp]
    exact Nanuq.CoordinateFace.unbounded_image coordinates F hub
  obtain ⟨e,u,v,es,hface⟩ := Graph.face_cycles_continuous hdraw htwo (coordinates face.outside) hnotG
  have hC := hdraw.cycle_isJordanCurve hface.isCycle
  have hout : Graph.face G φ (coordinates face.outside) =
      Schoenflies.outside (Graph.edgesCover φ (e::es)) := by
    rcases hface.isRegionOf with hi | ho
    · exact False.elim (hunbounded (hi.symm ▸ hface.isSeparating.isBounded_inside))
    · exact ho
  refine ⟨e,u,v,es,hface,hC,hout,?_⟩
  intro p
  have hp : coordinates (D.point (N.originalPortInner b p).val) ∈ frontier (coordinates '' F) := by
    have hfrontier := coordinates.toHomeomorph.image_frontier F
    change coordinates '' frontier F = frontier (coordinates '' F) at hfrontier
    rw [← hfrontier]
    exact ⟨_,hfront p,rfl⟩
  rw [hcomp,hface.frontier_eq] at hp
  exact hp

#print axioms actual_raw_port_outer_cycle
end Nanuq.RawPortFrontier
