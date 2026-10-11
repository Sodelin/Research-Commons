import G1ActualSplicedPlanarCurves

/-! Actual nonroot bigon splices and their existing finite Steps preserve
a faithful curved MULTIGRAPH embedding with only taxa on the unbounded face.
This certifies the rooted drawing part; the prescribed semidirected former-
root suppression/marking bridge remains separate. -/
namespace G1SpliceOuterLabelledCurveAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1CutChildPorts G1ActualTwoPortBlob G1BigonSpliceGraph G1SplicedSourceAdmission
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OuterLabelledMultigraphCurves G1ActualSplicedPlanarCurves
open scoped Classical
universe u v w
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- The whole output embedding is CONSTRUCTED from old curves. Distinct
parallel edges stay distinct, and the existing taxon unbounded-face witness
works because the complete new drawing is inside the original trace. -/
noncomputable def actualSplicedOuterCurves (N : RootedBinary V E X) (C : Calendar N.graph) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (old : OuterLabelledCurves N.graph N.leaf) :
    OuterLabelledCurves (splicedNetwork N hc b hb A).graph (splicedNetwork N hc b hb A).leaf where
  curves := actualSplicedPlanarCurves N C hc b A old.curves
  outer_face := Classical.choice (actual_outer_face_of_drawing_subset old.curves
    (actualSplicedPlanarCurves N C hc b A old.curves) N.leaf (splicedNetwork N hc b hb A).leaf
    old.outer_face (actual_spliced_drawing_subset N C hc b A old.curves) (fun x => rfl))

def HasRootedOuterLabelledCurves {Y : Type w} [Fintype Y] (S : Source.{u,v,w} Y) : Prop :=
  Nonempty (OuterLabelledCurves S.network.graph S.network.leaf)

theorem actual_step_preserves_outer_labelled_curves {Y : Type w} [Fintype Y]
    {S T : Source.{u,v,w} Y} (step : Step S T) (hs : HasRootedOuterLabelledCurves S) :
    HasRootedOuterLabelledCurves T := by
  obtain ⟨old⟩ := hs
  cases step with
  | splice b hb hp =>
    let A := extractedBigon S.network S.cutChild b hb ((G1CutChildPorts.actual_quotient_port_card S.network b).symm.trans hp)
    exact ⟨actualSplicedOuterCurves S.network S.calendar S.cutChild b hb A old⟩

/-- Geometry belongs to the SAME actual finite core selected by the existing
Steps witness, not an unrelated separately chosen planar representative. -/
theorem actual_steps_preserve_outer_labelled_curves {Y : Type w} [Fintype Y]
    {S T : Source.{u,v,w} Y} (steps : Steps S T) (hs : HasRootedOuterLabelledCurves S) :
    HasRootedOuterLabelledCurves T := by
  induction steps with
  | refl => exact hs
  | tail prior step ih => exact actual_step_preserves_outer_labelled_curves step ih

#print axioms actual_steps_preserve_outer_labelled_curves
end G1SpliceOuterLabelledCurveAdmission
