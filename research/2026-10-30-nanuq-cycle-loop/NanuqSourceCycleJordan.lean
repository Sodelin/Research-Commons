import CircleLoop
import NanuqActualSourceCycleCurve
import Schoenflies.Curve
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Source candidate: pending sole-cloud compilation.
The retained actual cycle API uses the separately hash-bound extracted G1 interface.
Do not additionally import full G1OuterLabelledMultigraphCurves without reconciling
that duplicate interface module. No Jordan theorem or contour order is assumed here.
-/
set_option debug.skipKernelTC false
namespace Nanuq.SourceCycleJordan
open Set Nanuq.Source G1OuterLabelledMultigraphCurves

/-- Actual edge-walk cycle trace, including parallel bigons, meets the supplier's
Jordan predicate after an exact coordinate equivalence, not a redrawing. -/
theorem actual_cycle_isJordan
    {V E : Type*} {G : EdgeGraph V E} (D : PlanarCurves G)
    (e : G1OuterLabelledMultigraphCurves.Plane ≃L[ℝ] Schoenflies.Plane)
    {a b : V} (w z : G.OccurrenceWalk a b)
    (hw : w.Simple) (hz : z.Simple) (hwn : w.Nonempty) (hzn : z.Nonempty)
    (hd : Disjoint w.edges z.edges)
    (hv : ∀ v, v ∈ w.vertices → v ∈ z.vertices → v = a ∨ v = b) :
    Schoenflies.IsJordanCurve (e ''
      (range (w.curve D.toCurveDrawing) ∪ range (z.curve D.toCurveDrawing))) := by
  obtain ⟨r, hc, hi, hr⟩ := actual_source_interface_cycle_circle D w z hw hz hwn hzn hd hv
  obtain ⟨f, hf, hclose, hinj, htrace⟩ := Nanuq.CircleLoop.interval_loop
    (fun t => e (r t)) (e.continuous.comp hc) (e.injective.comp hi)
  refine ⟨f, ⟨hf.continuousOn, hclose, hinj⟩, ?_⟩
  rw [htrace, ← hr]
  exact Set.range_comp e r

#print axioms actual_cycle_isJordan
end Nanuq.SourceCycleJordan
