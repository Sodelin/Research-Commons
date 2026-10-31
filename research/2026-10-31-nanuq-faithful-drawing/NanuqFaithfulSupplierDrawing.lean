import G1OuterLabelledMultigraphCurves
import Schoenflies.Graph.Drawing
import Mathlib.Topology.Order.ProjIcc

/-!
Actual source-curve adapter, candidate pending compilation against qualified supplier.
Contributor: dot, 2026-10-30. Supplier pin 05a43d29cde026618777db3d4e4316204ccca237.
No polygonal redrawing, rotation system, outer-face ordering or copied-tip adjacency
is assumed. The original edge type is retained, including parallel-edge bigons.
-/
noncomputable section
namespace NanuqFaithfulSupplierDrawing
open Set Nanuq.Source G1OuterLabelledMultigraphCurves
open scoped Graph

/-- Coordinate change only; no topological alteration of the drawing. -/
def coordinates : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

variable {V E : Type*} {G : EdgeGraph V E} (D : PlanarCurves G)

def vertex (v : V) : Schoenflies.Plane := coordinates (D.point v)

lemma vertex_injective : Function.Injective (vertex D) :=
  coordinates.injective.comp D.point_injective

/-- Edges are original IDs, not unordered endpoint pairs. -/
def graph : Graph Schoenflies.Plane E where
  vertexSet := range (vertex D)
  edgeSet := univ
  IsLink e x y :=
    (x = vertex D (G.source e) ∧ y = vertex D (G.target e)) ∨
    (x = vertex D (G.target e) ∧ y = vertex D (G.source e))
  isLink_symm := by
    intro e _
    constructor
    intro x y h
    rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact Or.inr ⟨hy,hx⟩
    · exact Or.inl ⟨hy,hx⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w h k
    rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;>
      rcases k with ⟨hv,hw⟩ | ⟨hv,hw⟩ <;> simp_all
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun _ => ⟨_,_,Or.inl ⟨rfl,rfl⟩⟩, fun _ => mem_univ _⟩
  left_mem_of_isLink := by
    intro e x y h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact mem_range_self _
    · exact mem_range_self _

/-- Source finiteness transfers without bounding parallel-edge multiplicity by vertices. -/
instance [Finite V] [Finite E] : (graph D).Finite where
  finite_vertexSet := Set.finite_range (vertex D)
  finite_edgeSet := Set.toFinite _

/-- Extend each original unit-interval path by clamping outside [0,1]. -/
def curve (e : E) (t : ℝ) : Schoenflies.Plane :=
  coordinates (D.arc e (projIcc 0 1 (by norm_num) t))

lemma curve_on_interval (e : E) (t : unitInterval) :
    curve D e t = coordinates (D.arc e t) := by
  simp only [curve, projIcc_of_mem _ t.property]

lemma curve_zero (e : E) : curve D e 0 = vertex D (G.source e) := by
  simpa [vertex] using curve_on_interval D e 0

lemma curve_one (e : E) : curve D e 1 = vertex D (G.target e) := by
  simpa [vertex] using curve_on_interval D e 1

lemma edgeArc_eq (e : E) :
    Graph.edgeArc (curve D) e = coordinates '' range (D.arc e) := by
  ext p
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact ⟨_,⟨projIcc 0 1 (by norm_num) t,rfl⟩,rfl⟩
  · rintro ⟨_,⟨t,rfl⟩,rfl⟩
    exact ⟨t,t.property,curve_on_interval D e t⟩

lemma arc_endpoint_inc (e : E) (t : unitInterval) (ht : t = 0 ∨ t = 1) :
    (graph D).Inc e (coordinates (D.arc e t)) := by
  rcases ht with rfl | rfl
  · exact ⟨vertex D (G.target e),Or.inl ⟨by simp [vertex],rfl⟩⟩
  · exact ⟨vertex D (G.source e),Or.inr ⟨by simp [vertex],rfl⟩⟩

/-- Genuine supplier premise, derived from the actual faithful source curves. -/
theorem isDrawing : Graph.IsDrawing (graph D) (curve D) := by
  constructor
  · intro e _
    refine ⟨?_,?_,?_⟩
    · exact (coordinates.continuous.comp ((D.arc e).continuous.comp
        continuous_projIcc)).continuousOn
    · intro t ht u hu he
      have hi := D.arc_injective e (coordinates.injective he)
      rw [projIcc_of_mem _ ht,projIcc_of_mem _ hu] at hi
      exact congrArg Subtype.val hi
    · rw [curve_zero,curve_one]
      exact Or.inl ⟨rfl,rfl⟩
  · intro e x y v hlink hv he
    obtain ⟨w,rfl⟩ := hv
    rw [edgeArc_eq] at he
    obtain ⟨_,⟨t,rfl⟩,he⟩ := he
    have hw := D.vertex_incidence e w t (coordinates.injective he)
    rcases hlink with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rcases hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases hw with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
  · intro e f _ _ hef p he hf
    rw [edgeArc_eq] at he hf
    obtain ⟨_,⟨t,rfl⟩,rfl⟩ := he
    obtain ⟨_,⟨u,rfl⟩,hu⟩ := hf
    have htu := D.edge_incidence e f hef t u
      (coordinates.injective hu.symm)
    have hi := arc_endpoint_inc D e t htu.1
    have hj := arc_endpoint_inc D f u htu.2
    rw [hu] at hj
    exact ⟨hi.vertex_mem,hi,hj⟩

/-- Exact occupied point set; not merely graph or vertex preservation. -/
theorem pointSet_eq : Graph.pointSet (graph D) (curve D) =
    coordinates '' G1OuterLabelledMultigraphCurves.drawing D := by
  ext p
  simp only [Graph.pointSet,graph,mem_union,mem_range,mem_iUnion,mem_univ,
    exists_const,edgeArc_eq,mem_image,G1OuterLabelledMultigraphCurves.drawing]
  constructor
  · rintro (⟨v,rfl⟩ | ⟨e,q,⟨t,rfl⟩,rfl⟩)
    · exact ⟨D.point v,Or.inl ⟨v,rfl⟩,rfl⟩
    · exact ⟨D.arc e t,Or.inr ⟨e,t,rfl⟩,rfl⟩
  · rintro ⟨q,(⟨v,rfl⟩ | ⟨e,t,rfl⟩),rfl⟩
    · exact Or.inl ⟨v,rfl⟩
    · exact Or.inr ⟨e,D.arc e t,⟨t,rfl⟩,rfl⟩

#print axioms isDrawing
#print axioms pointSet_eq
end NanuqFaithfulSupplierDrawing
