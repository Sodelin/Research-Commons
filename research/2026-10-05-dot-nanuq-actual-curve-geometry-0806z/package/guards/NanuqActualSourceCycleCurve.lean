import guards.NanuqActualCurveWalk
import guards.NanuqActualOriginalCurveAdapter

set_option debug.skipKernelTC false

/-! Actual edge-indexed simple cycles as embedded circles. The input consists
of two simple, edge-disjoint occurrence walks with only their endpoints in
common. All curve intersection and injectivity conclusions are derived from
the original faithful drawing. The formulation includes parallel-edge bigons.
It makes no assertion about ambient faces or adjacent opened tips. -/
namespace Nanuq.Source.EdgeGraph.OccurrenceWalk
open Set
variable {V E P : Type*} [TopologicalSpace P]
variable {G : EdgeGraph V E} (D : CurveDrawing (P := P) G)

theorem disjoint_edge_walk_intersection_is_vertex {a b c d : V}
    (w : G.OccurrenceWalk a b) (z : G.OccurrenceWalk c d)
    (hd : Disjoint w.edges z.edges) (t u : unitInterval)
    (h : w.curve D t = z.curve D u) :
    ∃ v, w.curve D t = D.point v := by
  have hw : w.curve D t ∈ Set.range (w.curve D) := ⟨t,rfl⟩
  have hz : z.curve D u ∈ Set.range (z.curve D) := ⟨u,rfl⟩
  rw [w.curve_range D] at hw
  rw [z.curve_range D] at hz
  rcases hw with hw | hw
  · exact ⟨a,hw⟩
  · rcases hz with hz | hz
    · exact ⟨c,h.trans hz⟩
    · obtain ⟨e,hw⟩ := Set.mem_iUnion.mp hw
      obtain ⟨he,s,hs⟩ := Set.mem_iUnion.mp hw
      obtain ⟨f,hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hf,r,hr⟩ := Set.mem_iUnion.mp hz
      have hne : e ≠ f := by
        intro heq;subst f;exact Set.disjoint_left.mp hd he hf
      have hc : D.arc e s = D.arc f r := hs.trans (h.trans hr.symm)
      rcases (D.edge_incidence e f hne s r hc).1 with hzero | hone
      · refine ⟨G.source e,?_⟩
        simpa [hzero] using hs.symm
      · refine ⟨G.target e,?_⟩
        simpa [hone] using hs.symm

theorem simple_two_walk_joint {a b : V} (w z : G.OccurrenceWalk a b)
    (hw : w.Simple) (hz : z.Simple) (hwn : w.Nonempty) (hzn : z.Nonempty)
    (hd : Disjoint w.edges z.edges)
    (hv : ∀ v, v ∈ w.vertices → v ∈ z.vertices → v = a ∨ v = b)
    (t u : unitInterval) (h : w.curve D t = z.curve D u) :
    (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1) := by
  obtain ⟨v,hvp⟩ := disjoint_edge_walk_intersection_is_vertex D w z hd t u h
  have hvz : z.curve D u = D.point v := h.symm.trans hvp
  have hwv := w.vertex_of_curve D v t hvp
  have hzv := z.vertex_of_curve D v u hvz
  have hiw := w.curve_injective D hw hwn
  have hiz := z.curve_injective D hz hzn
  rcases hv v hwv hzv with rfl | rfl
  · left
    exact ⟨hiw (by simpa using hvp),hiz (by simpa using hvz)⟩
  · right
    exact ⟨hiw (by simpa using hvp),hiz (by simpa using hvz)⟩

/-- A source cycle, specified by actual edge occurrences and ordinary
vertex-simplicity/disjointness, supplies the continuous injective circle map
needed by Jordan separation. No topological-cycle certificate is an input. -/
theorem actual_simple_cycle_circle {a b : V} (w z : G.OccurrenceWalk a b)
    (hw : w.Simple) (hz : z.Simple) (hwn : w.Nonempty) (hzn : z.Nonempty)
    (hd : Disjoint w.edges z.edges)
    (hv : ∀ v, v ∈ w.vertices → v ∈ z.vertices → v = a ∨ v = b) :
    ∃ r : AddCircle (1:ℝ) → P, Continuous r ∧ Function.Injective r ∧
      Set.range r = Set.range (w.curve D) ∪ Set.range (z.curve D) := by
  refine ⟨CurveDrawing.twoArmCircle (w.curve D) (z.curve D),
    CurveDrawing.twoArmCircle_continuous _ _,?_,CurveDrawing.twoArmCircle_range _ _⟩
  exact CurveDrawing.twoArmCircle_injective _ _ (w.curve_injective D hw hwn)
    (z.curve_injective D hz hzn) (simple_two_walk_joint D w z hw hz hwn hzn hd hv)

end Nanuq.Source.EdgeGraph.OccurrenceWalk
#print axioms Nanuq.Source.EdgeGraph.OccurrenceWalk.actual_simple_cycle_circle

namespace G1OuterLabelledMultigraphCurves
open Nanuq.Source
variable {V E : Type*} {G : EdgeGraph V E} (D : PlanarCurves G)
/-- The source-interface extraction feeds the actual cycle construction
without an added topological embedding hypothesis. -/
theorem actual_source_interface_cycle_circle {a b : V} (w z : G.OccurrenceWalk a b)
    (hw : w.Simple) (hz : z.Simple) (hwn : w.Nonempty) (hzn : z.Nonempty)
    (hd : Disjoint w.edges z.edges)
    (hv : ∀ v, v ∈ w.vertices → v ∈ z.vertices → v = a ∨ v = b) :
    ∃ r : AddCircle (1:ℝ) → Plane, Continuous r ∧ Function.Injective r ∧
      Set.range r = Set.range (w.curve D.toCurveDrawing) ∪
        Set.range (z.curve D.toCurveDrawing) :=
  w.actual_simple_cycle_circle D.toCurveDrawing z hw hz hwn hzn hd hv
end G1OuterLabelledMultigraphCurves
#print axioms G1OuterLabelledMultigraphCurves.actual_source_interface_cycle_circle
