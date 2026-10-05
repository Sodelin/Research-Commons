import SourceNetwork
import Mathlib.Topology.Path
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded

set_option debug.skipKernelTC false

/-! Faithful planar MULTIGRAPH curves, with only the labelled taxa required
on the unbounded face. Distinct parallel arcs remain distinct interior curves.
Root suppression and the exact semidirected-partner markings are subsequent
admission bridges, not supplied by this rooted curve carrier alone.
Primary convention: Holtgrefe et al. (2025), Definitions2.2 and2.3(v),
https://doi.org/10.1007/s11538-025-01549-4. -/
namespace G1OuterLabelledMultigraphCurves
open Nanuq.Source Set
open scoped Classical
abbrev Plane := ℝ × ℝ

structure PlanarCurves {V E : Type*} (G : EdgeGraph V E) where
  point : V → Plane
  point_injective : Function.Injective point
  arc : ∀ e : E, Path (point (G.source e)) (point (G.target e))
  arc_injective : ∀ e, Function.Injective (arc e)
  vertex_incidence : ∀ e v t, arc e t = point v → v = G.source e ∨ v = G.target e
  edge_incidence : ∀ e f, e ≠ f → ∀ t u, arc e t = arc f u →
    (t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)

def drawing {V E : Type*} {G : EdgeGraph V E} (D : PlanarCurves G) : Set Plane :=
  range D.point ∪ ⋃ e : E, range (D.arc e)

/-- A geometric unbounded complementary component, not an order determined
by displayed splits. Internal vertices are allowed on bounded faces. -/
structure TaxonOuterFace {V E X : Type*} {G : EdgeGraph V E}
    (D : PlanarCurves G) (leaf : X → V) where
  outside : Plane
  outside_not_drawing : outside ∉ drawing D
  component_unbounded : ¬ Bornology.IsBounded (connectedComponentIn (drawing D)ᶜ outside)
  taxon_on_face : ∀ x, D.point (leaf x) ∈ closure (connectedComponentIn (drawing D)ᶜ outside)

structure OuterLabelledCurves {V E X : Type*} (G : EdgeGraph V E) (leaf : X → V) where
  curves : PlanarCurves G
  outer_face : TaxonOuterFace curves leaf

/-- The exact outer-labelled face witness transports by an actual drawing
subset. This is why deleting an arm and concatenating existing curves does
not require a global straight-edge redrawing or all-vertices-outer premise. -/
theorem actual_outer_face_of_drawing_subset
    {V E W F X : Type*} {G : EdgeGraph V E} {H : EdgeGraph W F}
    (old : PlanarCurves G) (new : PlanarCurves H) (oldLeaf : X → V) (newLeaf : X → W)
    (face : TaxonOuterFace old oldLeaf) (hdraw : drawing new ⊆ drawing old)
    (hlabel : ∀ x, new.point (newLeaf x) = old.point (oldLeaf x)) :
    Nonempty (TaxonOuterFace new newLeaf) := by
  have hc : connectedComponentIn (drawing old)ᶜ face.outside ⊆
      connectedComponentIn (drawing new)ᶜ face.outside :=
    connectedComponentIn_mono face.outside (compl_subset_compl.mpr hdraw)
  refine ⟨⟨face.outside,?_,?_,?_⟩⟩
  · exact fun hm => face.outside_not_drawing (hdraw hm)
  · exact fun hb => face.component_unbounded (hb.subset hc)
  · intro x
    rw [hlabel x]
    exact closure_mono hc (face.taxon_on_face x)

theorem actual_three_path_trace_is_old_union {P : Type*} [TopologicalSpace P]
    {a b c d : P} (entry : Path a b) (arm : Path b c) (child : Path c d) :
    range ((entry.trans arm).trans child) = range entry ∪ range arm ∪ range child := by
  rw [Path.trans_range,Path.trans_range]

#print axioms actual_outer_face_of_drawing_subset
end G1OuterLabelledMultigraphCurves
