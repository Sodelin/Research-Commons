import guards.NanuqActualOpenedChoiceFamily
import Mathlib.Topology.Path

set_option debug.skipKernelTC false

/-! Literal curve-level hybrid opening. This carrier has the same faithful
point/arc/incidence fields as the accepted G1 PlanarCurves carrier, without
importing its unrelated whole-G1 assembly. No rotation or outer-face order is
postulated. The new tips are actual interior points of original parent arcs. -/
namespace Nanuq.Source.EdgeGraph
open Set
variable {V E P : Type*} [TopologicalSpace P]

structure CurveDrawing (G : EdgeGraph V E) where
  point : V → P
  point_injective : Function.Injective point
  arc : ∀ e : E, Path (point (G.source e)) (point (G.target e))
  arc_injective : ∀ e, Function.Injective (arc e)
  vertex_incidence : ∀ e v t, arc e t = point v → v = G.source e ∨ v = G.target e
  edge_incidence : ∀ e f, e ≠ f → ∀ t u, arc e t = arc f u →
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)

namespace CurveDrawing
variable {G : EdgeGraph V E} (D : CurveDrawing (P := P) G)

noncomputable def mid : unitInterval := ⟨(1:ℝ)/2,by constructor <;> norm_num⟩
noncomputable def half (t : unitInterval) : unitInterval :=
  ⟨(t:ℝ)/2,by constructor <;> nlinarith [t.property.1,t.property.2]⟩

theorem mid_ne_zero : mid ≠ (0:unitInterval) := by
  intro h;have := congrArg (fun t : unitInterval => (t:ℝ)) h
  norm_num [mid] at this

theorem mid_ne_one : mid ≠ (1:unitInterval) := by
  intro h;have := congrArg (fun t : unitInterval => (t:ℝ)) h
  norm_num [mid] at this

theorem half_injective : Function.Injective half := by
  intro a b h;apply Subtype.ext
  have := congrArg (fun t : unitInterval => (t:ℝ)) h
  simp only [half] at this
  linarith

@[simp] theorem half_zero : half 0 = 0 := by apply Subtype.ext;simp [half]
@[simp] theorem half_one : half 1 = mid := by rfl

theorem half_ne_one (t : unitInterval) : half t ≠ 1 := by
  intro h;have := congrArg (fun t : unitInterval => (t:ℝ)) h
  simp only [half] at this
  have := t.property.2
  norm_num at *
  linarith

theorem arc_eq_vertex_parameter (e : E) (v : V) (t : unitInterval)
    (h : D.arc e t = D.point v) : t = 0 ∨ t = 1 := by
  rcases D.vertex_incidence e v t h with hs | ht
  · left;apply D.arc_injective e
    simpa [hs] using h
  · right;apply D.arc_injective e
    simpa [ht] using h

theorem midpoint_not_vertex (e : E) (v : V) : D.arc e mid ≠ D.point v := by
  intro h
  exact (D.arc_eq_vertex_parameter e v mid h).elim mid_ne_zero mid_ne_one

theorem midpoint_injective : Function.Injective (fun e => D.arc e mid) := by
  intro e f h
  by_contra hn
  exact ((D.edge_incidence e f hn mid mid h).1).elim mid_ne_zero mid_ne_one

noncomputable def firstHalf (e : E) : Path (D.point (G.source e)) (D.arc e mid) where
  toFun t := D.arc e (half t)
  continuous_toFun := (D.arc e).continuous.comp (by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div_const 2)
  source' := by simp
  target' := by simp

theorem firstHalf_injective (e : E) : Function.Injective (D.firstHalf e) := by
  intro a b h
  exact half_injective (D.arc_injective e h)
end CurveDrawing
end Nanuq.Source.EdgeGraph

namespace Nanuq.Source.RootedBinary
open scoped Classical
open EdgeGraph.CurveDrawing
variable {V E X P : Type*} [TopologicalSpace P]
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : EdgeGraph.CurveDrawing (P := P) N.graph)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

noncomputable def openedCurvePoint : N.OpenedHybridVertex → P :=
  Sum.elim (fun v => D.point v.val) (fun e => D.arc e.val mid)

theorem openedCurvePoint_injective : Function.Injective (N.openedCurvePoint D) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Sum.inl (Subtype.ext (D.point_injective h))
  · exact False.elim (D.midpoint_not_vertex b.val a.val h.symm)
  · exact False.elim (D.midpoint_not_vertex a.val b.val h)
  · exact congrArg Sum.inr (Subtype.ext (D.midpoint_injective h))

noncomputable def openedCurveArc (e : N.OpenedHybridEdge) :
    Path (N.openedCurvePoint D ((N.openedHybridGraph hleaf).source e))
      (N.openedCurvePoint D ((N.openedHybridGraph hleaf).target e)) :=
  match e with
  | Sum.inl f => D.arc f.val
  | Sum.inr f => D.firstHalf f.val

theorem openedCurveArc_injective (e : N.OpenedHybridEdge) :
    Function.Injective (N.openedCurveArc D hleaf e) := by
  rcases e with e | e
  · exact D.arc_injective e.val
  · exact D.firstHalf_injective e.val

theorem openedCurve_vertex_incidence (e : N.OpenedHybridEdge)
    (v : N.OpenedHybridVertex) (t : unitInterval)
    (h : N.openedCurveArc D hleaf e t = N.openedCurvePoint D v) :
    v = (N.openedHybridGraph hleaf).source e ∨ v = (N.openedHybridGraph hleaf).target e := by
  rcases e with e | e <;> rcases v with v | v
  · rcases D.vertex_incidence e.val v.val t h with hs | ht
    · exact Or.inl (congrArg Sum.inl (Subtype.ext hs))
    · exact Or.inr (congrArg Sum.inl (Subtype.ext ht))
  · have hn : e.val ≠ v.val := by
      intro he;exact e.property.2.1 (by rw [he];exact v.property)
    exact False.elim (((D.edge_incidence e.val v.val hn t mid h).2).elim
      mid_ne_zero mid_ne_one)
  · have hp : half t = 0 ∨ half t = 1 := D.arc_eq_vertex_parameter e.val v.val (half t) h
    have ht : t = 0 := half_injective ((hp.resolve_right (half_ne_one t)).trans half_zero.symm)
    left
    apply congrArg Sum.inl
    apply Subtype.ext
    apply D.point_injective
    have hh : D.arc e.val (half t) = D.point v.val := h
    simpa [ht] using hh.symm
  · by_cases he : e.val = v.val
    · right;exact congrArg Sum.inr (Subtype.ext he.symm)
    · exact False.elim (((D.edge_incidence e.val v.val he (half t) mid h).2).elim
        mid_ne_zero mid_ne_one)

theorem openedCurve_edge_incidence (e f : N.OpenedHybridEdge) (hne : e ≠ f)
    (t u : unitInterval)
    (h : N.openedCurveArc D hleaf e t = N.openedCurveArc D hleaf f u) :
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1) := by
  rcases e with e | e <;> rcases f with f | f
  · exact D.edge_incidence e.val f.val
      (fun he => hne (congrArg Sum.inl (Subtype.ext he))) t u h
  · have hn : e.val ≠ f.val := by
      intro he;exact e.property.2.1 (by rw [he];exact f.property)
    have hp := D.edge_incidence e.val f.val hn t (half u) h
    exact ⟨hp.1,Or.inl (half_injective ((hp.2.resolve_right (half_ne_one u)).trans half_zero.symm))⟩
  · have hn : e.val ≠ f.val := by
      intro he;exact f.property.2.1 (by rw [← he];exact e.property)
    have hp := D.edge_incidence e.val f.val hn (half t) u h
    exact ⟨Or.inl (half_injective ((hp.1.resolve_right (half_ne_one t)).trans half_zero.symm)),hp.2⟩
  · have hp := D.edge_incidence e.val f.val
      (fun he => hne (congrArg Sum.inr (Subtype.ext he))) (half t) (half u) h
    exact ⟨Or.inl (half_injective ((hp.1.resolve_right (half_ne_one t)).trans half_zero.symm)),
      Or.inl (half_injective ((hp.2.resolve_right (half_ne_one u)).trans half_zero.symm))⟩

noncomputable def actualOpenedCurveDrawing :
    EdgeGraph.CurveDrawing (P := P) (N.openedHybridGraph hleaf) where
  point := N.openedCurvePoint D
  point_injective := N.openedCurvePoint_injective D
  arc := N.openedCurveArc D hleaf
  arc_injective := N.openedCurveArc_injective D hleaf
  vertex_incidence := N.openedCurve_vertex_incidence D hleaf
  edge_incidence := N.openedCurve_edge_incidence D hleaf

/-- Every point of the opened drawing lies on the original drawing; the
construction does not require redrawing the graph. -/
theorem actualOpenedCurveDrawing_subset :
    Set.range (N.actualOpenedCurveDrawing D hleaf).point ∪
      (⋃ e, Set.range ((N.actualOpenedCurveDrawing D hleaf).arc e)) ⊆
    Set.range D.point ∪ (⋃ e, Set.range (D.arc e)) := by
  intro p hp
  rcases hp with ⟨v,rfl⟩ | hp
  · rcases v with v | e
    · exact Or.inl ⟨v.val,rfl⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨e.val,⟨mid,rfl⟩⟩)
  · obtain ⟨e,t,ht⟩ := Set.mem_iUnion.mp hp
    rcases e with e | e
    · exact Or.inr (Set.mem_iUnion.mpr ⟨e.val,⟨t,ht⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨e.val,⟨half t,ht⟩⟩)

end Nanuq.Source.RootedBinary
#print axioms Nanuq.Source.RootedBinary.actualOpenedCurveDrawing
