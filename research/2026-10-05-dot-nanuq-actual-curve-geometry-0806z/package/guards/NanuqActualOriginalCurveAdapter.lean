import guards.NanuqOriginalPlanarCurvesInterface
import guards.NanuqActualCurveOpening

set_option debug.skipKernelTC false

/-! Field-for-field adapter to the separately hash-bound G1 source-interface
extraction. This is a newly compiled extraction, not a replay of the original
whole-G1 assembly object. Original declaration-body bytes are preserved in the
extracted source; only its dependency import is reduced to SourceNetwork. -/
namespace G1OuterLabelledMultigraphCurves
open Nanuq.Source
variable {V E : Type*} {G : EdgeGraph V E}

def PlanarCurves.toCurveDrawing (D : PlanarCurves G) :
    EdgeGraph.CurveDrawing (P := Plane) G where
  point := D.point
  point_injective := D.point_injective
  arc := D.arc
  arc_injective := D.arc_injective
  vertex_incidence := D.vertex_incidence
  edge_incidence := D.edge_incidence

def ofCurveDrawing (D : EdgeGraph.CurveDrawing (P := Plane) G) : PlanarCurves G where
  point := D.point
  point_injective := D.point_injective
  arc := D.arc
  arc_injective := D.arc_injective
  vertex_incidence := D.vertex_incidence
  edge_incidence := D.edge_incidence

@[simp] theorem from_to_CurveDrawing (D : PlanarCurves G) :
    ofCurveDrawing D.toCurveDrawing = D := by cases D;rfl

@[simp] theorem to_from_CurveDrawing (D : EdgeGraph.CurveDrawing (P := Plane) G) :
    (ofCurveDrawing D).toCurveDrawing = D := by cases D;rfl

variable {X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

noncomputable def actualOpenedPlanarCurves : PlanarCurves (N.openedHybridGraph hleaf) :=
  ofCurveDrawing (N.actualOpenedCurveDrawing D.toCurveDrawing hleaf)

theorem actualOpenedPlanarCurves_drawing_subset :
    drawing (actualOpenedPlanarCurves N D hleaf) ⊆ drawing D :=
  N.actualOpenedCurveDrawing_subset D.toCurveDrawing hleaf

end G1OuterLabelledMultigraphCurves
#print axioms G1OuterLabelledMultigraphCurves.actualOpenedPlanarCurves
#print axioms G1OuterLabelledMultigraphCurves.actualOpenedPlanarCurves_drawing_subset
