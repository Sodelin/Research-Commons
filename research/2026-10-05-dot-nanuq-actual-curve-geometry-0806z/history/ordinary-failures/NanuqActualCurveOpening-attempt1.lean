import NanuqActualOpenedChoiceFamily
import Mathlib.Topology.Path

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

def mid : unitInterval := ⟨(1:ℝ)/2,by constructor <;> norm_num⟩
def half (t : unitInterval) : unitInterval :=
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

def openedCurvePoint : N.OpenedHybridVertex → P :=
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
