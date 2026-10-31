import ActualLeafOneExit
import OriginalBinaryStar

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Pendant
open Set Schoenflies unitInterval Nanuq.Source
open scoped Graph

/-- The leaf axiom identifies ONE ORIGINAL incoming ID and excludes every
other incidence; no simplegraph quotient or user-supplied leaf certificate. -/
theorem original_leaf_unique_id {V E X : Type*}
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
    (N : RootedBinary V E X) (x : X) :
    ∃ e : E, N.graph.target e=N.leaf x ∧
      ∀ g : E, N.graph.source g=N.leaf x ∨ N.graph.target g=N.leaf x → g=e := by
  classical
  have hcard : (Finset.univ.filter (fun e : E => N.graph.target e=N.leaf x)).card=1 :=
    (N.leaf_degrees x).1
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp hcard
  have het : N.graph.target e=N.leaf x := by
    have hh : e ∈ Finset.univ.filter (fun e : E => N.graph.target e=N.leaf x) := by
      rw [he]; simp
    exact (Finset.mem_filter.mp hh).2
  refine ⟨e,het,?_⟩
  intro g hg
  rcases hg with hgs | hgt
  · have hzero : (Finset.univ.filter (fun e : E => N.graph.source e=N.leaf x)).card=0 :=
      (N.leaf_degrees x).2
    have hmem : g ∈ Finset.univ.filter (fun e : E => N.graph.source e=N.leaf x) := by simp [hgs]
    rw [Finset.card_eq_zero.mp hzero] at hmem
    exact False.elim (Finset.not_mem_empty _ hmem)
  · have hmem : g ∈ Finset.univ.filter (fun e : E => N.graph.target e=N.leaf x) := by simp [hgt]
    rw [he] at hmem
    exact Finset.mem_singleton.mp hmem

/-- Original finite rooted-binary source, SAME full faithful drawing and SAME
edge ID. The derived leaf-to-parent parameterization and unique exit are
retained. Upper/lower are geometrical sides of this particular directed
carrier, not an assumed global orientation or a face-order certificate. -/
theorem original_taxon_one_exit {V E X : Type*}
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
    (N : RootedBinary V E X) (D : G1OuterLabelledMultigraphCurves.PlanarCurves N.graph)
    (x : X) :
    ∃ (e : E) (f : ℝ → Plane) (H : Plane ≃ₜ Plane) (r b t : ℝ) (C : Set Plane),
      N.graph.target e=N.leaf x ∧ ContinuousOn f I ∧ InjOn f I ∧
      f '' I=Graph.edgeArc (NanuqFaithfulSupplierDrawing.curve D) e ∧
      f 0=NanuqFaithfulSupplierDrawing.vertex D (N.leaf x) ∧
      f 1=NanuqFaithfulSupplierDrawing.vertex D (N.graph.source e) ∧
      0 < r ∧ r < b ∧ t ∈ Ioo (1/2) (13/24) ∧ IsJordanCurve C ∧
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
          G1OuterLabelledMultigraphCurves.drawing D))ᶜ (Plane.mk r (r/2)) := by
  obtain ⟨e,het,hunique⟩ := original_leaf_unique_id N x
  let G := NanuqFaithfulSupplierDrawing.graph D
  haveI : G.Finite := by
    refine ⟨?_,?_⟩
    · change (range (NanuqFaithfulSupplierDrawing.vertex D)).Finite
      exact Set.finite_range _
    · change (univ : Set E).Finite
      exact Set.toFinite _
  have he : G.IsLink e (NanuqFaithfulSupplierDrawing.vertex D (N.leaf x))
      (NanuqFaithfulSupplierDrawing.vertex D (N.graph.source e)) :=
    Or.inr ⟨congrArg (NanuqFaithfulSupplierDrawing.vertex D) het.symm,rfl⟩
  have hcover : ∀ g ∈ E(G), G.Inc g (NanuqFaithfulSupplierDrawing.vertex D (N.leaf x)) → g=e := by
    intro g _ hg
    obtain ⟨w,hw⟩ := hg
    apply hunique g
    rcases hw with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ((NanuqFaithfulSupplierDrawing.vertex_injective D) hs).symm
    · exact Or.inr ((NanuqFaithfulSupplierDrawing.vertex_injective D) hs).symm
  have hD := NanuqFaithfulSupplierDrawing.isDrawing D
  obtain ⟨f,hc,hi,him,h0,h1⟩ := hD.edge_isArcBetween he
  obtain ⟨H,r,b,t,C,hrest⟩ := actual_leaf_one_exit hD he hcover f hc hi him h0 h1
  refine ⟨e,f,H,r,b,t,C,het,hc,hi,him,h0,h1,?_⟩
  simpa only [NanuqFaithfulSupplierDrawing.pointSet_eq D] using hrest

#print axioms original_leaf_unique_id
#print axioms original_taxon_one_exit
end Nanuq.Pendant
