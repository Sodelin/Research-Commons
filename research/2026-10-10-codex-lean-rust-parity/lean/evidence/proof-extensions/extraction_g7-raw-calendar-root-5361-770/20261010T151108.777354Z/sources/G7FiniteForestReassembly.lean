import G7PopulationForestReassembly

/-! A total finite full-forest index reassembler. Values outside the actual
source-view range use the entering index; actual-law equality is derived before
this total readout is applied, so no invalid-product support is postulated. -/
namespace GProgram.G7.FiniteForestReassembly
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCopyCarrierTransport
open GProgram.G7.WholeAncestorPanelCode GProgram.G7.PopulationForestReassembly
open G1ActualJointEpoch DotG6.ActualPopulationPanelSplit
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def viewIndex (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (v : SelectedView V E Copy) : SelectedIndex N sample Finset.univ :=
  if h : ∃ d : Code N sample, selectedView (state d) Finset.univ = v then
    ⟨v,h⟩ else projection N Finset.univ s

lemma viewIndex_actual (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) :
    viewIndex N s (selectedView (state d) Finset.univ) = projection N Finset.univ d := by
  rw [viewIndex,dif_pos ⟨d,rfl⟩]
  rfl

lemma projection_value (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (d : Code N sample) :
    (projection N keep d).val = selectedView (state d) keep := rfl

noncomputable def joinIndex (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy)
    (ab : SelectedIndex N (selectedSample sample keep) Finset.univ ×
      SelectedIndex N (selectedSample sample (Finset.univ \ keep)) Finset.univ) :
    SelectedIndex N sample Finset.univ :=
  viewIndex N s (joinViews keep (liftView keep ab.1.val)
    (liftView (Finset.univ \ keep) ab.2.val))

theorem actual_finite_forest_reassembly (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0)
    (s : Code N sample) (place : Location V E) :
    let keep := populationPanel (state s) place
    let hc : AncestorClosed (state s) keep :=
      locationPanel_closed (state s) s.property.forest place
    (sourceTimeKernel N r t s).map (projection N Finset.univ) =
      (independentProduct
        ((sourceTimeKernel N r t (panelCode N s keep hc)).map (projection N Finset.univ))
        ((sourceTimeKernel N r t (panelCode N s (Finset.univ \ keep)
          (closed_complement (state s) keep hc))).map (projection N Finset.univ))).map
        (joinIndex N s keep) := by
  dsimp only
  have h := congrArg (fun p : PMF (SelectedView V E Copy) => p.map (viewIndex N s))
    (actual_smaller_source_reassembly N r t s place)
  simpa [PMF.map_comp,Function.comp_def,viewIndex_actual,independentProduct,
    PMF.bind_map,PMF.map_bind,projection_value,joinIndex] using h

end GProgram.G7.FiniteForestReassembly
