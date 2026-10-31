import SmallBlob
import RawPortFrontier
import CoordinateFace
import Schoenflies.Graph.CycleJordan
import Schoenflies.JordanClosed

/-! Own source candidate, UNCOMPILED. Original two-vertex blobs, including
parallel original edge IDs. No IsTwoConnected or three-vertex premise. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualBigonBoundary
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set
open scoped Graph
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

/-- The actual whole raw drawing is exactly a two-ID Jordan cycle. In
particular its vertex part has not been discarded from the point-set equality. -/
theorem actual_bigon_pointSet
    (u v : BlobVertex N.graph b) (huv : u ≠ v)
    (hall : ∀ w : BlobVertex N.graph b, w = u ∨ w = v) :
    ∃ e f : BlobEdge N.graph b, e ≠ f ∧
      (∀ g : BlobEdge N.graph b, g = e ∨ g = f) ∧
      ∃ s t : Schoenflies.Plane,
        (graph (blobCurves D b)).IsCycleThrough e s t [f] ∧
        Schoenflies.IsJordanCurve (Graph.edgesCover (curve (blobCurves D b)) [e,f]) ∧
        Graph.pointSet (graph (blobCurves D b)) (curve (blobCurves D b)) =
          Graph.edgesCover (curve (blobCurves D b)) [e,f] := by
  let B := originalBlob N.graph b
  let G := graph (blobCurves D b)
  let φ := curve (blobCurves D b)
  obtain ⟨e,f,hef,hex,hs,ht,hst⟩ := Nanuq.SmallBlob.two_vertex_exact_bigon N b u v huv hall
  have hs' : B.source f = B.source e := Subtype.ext hs
  have ht' : B.target f = B.target e := Subtype.ext ht
  have hst' : B.source e ≠ B.target e := fun h => hst (congrArg Subtype.val h)
  have hvex : ∀ w : BlobVertex N.graph b, w = B.source e ∨ w = B.target e := by
    intro w
    rcases hall (B.source e) with hsu | hsv <;>
      rcases hall (B.target e) with htu | htv
    · exact False.elim (hst' (hsu.trans htu.symm))
    · rcases hall w with hw | hw
      · exact Or.inl (hw.trans hsu.symm)
      · exact Or.inr (hw.trans htv.symm)
    · rcases hall w with hw | hw
      · exact Or.inr (hw.trans htu.symm)
      · exact Or.inl (hw.trans hsv.symm)
    · exact False.elim (hst' (hsv.trans htv.symm))
  let s := vertex (blobCurves D b) (B.source e)
  let t := vertex (blobCurves D b) (B.target e)
  have he : G.IsLink e s t := Or.inl ⟨rfl,rfl⟩
  have hf : G.IsLink f s t := Or.inl ⟨by dsimp [s]; rw [hs'],by dsimp [t]; rw [ht']⟩
  have hd := isDrawing (blobCurves D b)
  have hne : s ≠ t := hd.ne_of_isLink he
  have hc : G.IsCycleThrough e s t [f] :=
    ⟨he,Graph.IsPath.single hf hne,by simpa using hef⟩
  have hvertices : ∀ w : BlobVertex N.graph b,
      vertex (blobCurves D b) w ∈ Graph.edgesCover φ [e,f] := by
    intro w
    apply Graph.mem_edgesCover_iff.mpr
    refine ⟨e,by simp,?_⟩
    rcases hvex w with rfl | rfl
    · exact ⟨0,by norm_num,(curve_zero (blobCurves D b) e)⟩
    · exact ⟨1,by norm_num,(curve_one (blobCurves D b) e)⟩
  have hset : Graph.pointSet G φ = Graph.edgesCover φ [e,f] := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases hz with hz | hz
      · obtain ⟨w,rfl⟩ := hz
        exact hvertices w
      · obtain ⟨g,hg,hzg⟩ := Set.mem_iUnion₂.mp hz
        exact Graph.mem_edgesCover_iff.mpr ⟨g,by rcases hex g with rfl | rfl <;> simp,hzg⟩
    · exact Graph.edgesCover_subset_pointSet (fun _ _ => Set.mem_univ _)
  exact ⟨e,f,hef,hex,s,t,hc,hd.cycle_isJordanCurve hc,hset⟩

/-- The SAME specified original exterior is the exterior of the whole bigon
cycle, and every original port attachment belongs to that cycle. This is
incidence only, not a cyclic order or an opened duplicate-tip conclusion. -/
theorem actual_bigon_outer_boundary (hb : N.NonleafBlob b)
    (face : TaxonOuterFace D N.leaf)
    (u v : BlobVertex N.graph b) (huv : u ≠ v)
    (hall : ∀ w : BlobVertex N.graph b, w = u ∨ w = v) :
    ∃ e f : BlobEdge N.graph b, e ≠ f ∧
      (∀ g : BlobEdge N.graph b, g = e ∨ g = f) ∧
      ∃ s t : Schoenflies.Plane,
        (graph (blobCurves D b)).IsCycleThrough e s t [f] ∧
        Schoenflies.IsJordanCurve (Graph.edgesCover (curve (blobCurves D b)) [e,f]) ∧
        Graph.pointSet (graph (blobCurves D b)) (curve (blobCurves D b)) =
          Graph.edgesCover (curve (blobCurves D b)) [e,f] ∧
        Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
          (coordinates face.outside) =
          Schoenflies.outside (Graph.edgesCover (curve (blobCurves D b)) [e,f]) ∧
        ∀ p : N.BlobPort b, coordinates (D.point (N.originalPortInner b p).val) ∈
          Graph.edgesCover (curve (blobCurves D b)) [e,f] := by
  obtain ⟨e,f,hef,hex,s,t,hc,hC,hset⟩ := actual_bigon_pointSet N D b u v huv hall
  let R := drawing (blobCurves D b)
  let F := connectedComponentIn Rᶜ face.outside
  let G := graph (blobCurves D b)
  let φ := curve (blobCurves D b)
  change Graph.pointSet G φ = Graph.edgesCover φ [e,f] at hset
  obtain ⟨hnot,hub,_⟩ := Nanuq.RawPortFrontier.actual_raw_port_frontier N D b hb face
  have hnotG : coordinates face.outside ∉ Graph.pointSet G φ := by
    rw [pointSet_eq (blobCurves D b)]
    rintro ⟨x,hx,heq⟩
    exact hnot (coordinates.injective heq ▸ hx)
  have hcomp : coordinates '' F = Graph.face G φ (coordinates face.outside) := by
    change coordinates '' connectedComponentIn Rᶜ face.outside =
      connectedComponentIn (Graph.pointSet G φ)ᶜ (coordinates face.outside)
    rw [pointSet_eq (blobCurves D b)]
    exact Nanuq.CoordinateFace.component_image coordinates R face.outside hnot
  have hubG : ¬ Bornology.IsBounded (Graph.face G φ (coordinates face.outside)) := by
    rw [← hcomp]
    exact Nanuq.CoordinateFace.unbounded_image coordinates F hub
  have hout : coordinates face.outside ∈ Schoenflies.outside (Graph.edgesCover φ [e,f]) := by
    refine ⟨?_,?_⟩
    · simpa only [hset] using hnotG
    · change ¬ Bornology.IsBounded (connectedComponentIn (Graph.edgesCover φ [e,f])ᶜ _)
      simpa only [Graph.face,Graph.exterior,hset] using hubG
  refine ⟨e,f,hef,hex,s,t,hc,hC,hset,?_,?_⟩
  · change connectedComponentIn (Graph.pointSet G φ)ᶜ _ = _
    rw [hset]
    exact (Schoenflies.jordan_curve_theorem hC).connectedComponentIn_eq_outside hout
  · intro p
    rw [← hset]
    apply Graph.vertexSet_subset_pointSet
    exact ⟨⟨(N.originalPortInner b p).val,(N.originalPortInner b p).property⟩,rfl⟩

#print axioms actual_bigon_pointSet
#print axioms actual_bigon_outer_boundary
end Nanuq.ActualBigonBoundary
