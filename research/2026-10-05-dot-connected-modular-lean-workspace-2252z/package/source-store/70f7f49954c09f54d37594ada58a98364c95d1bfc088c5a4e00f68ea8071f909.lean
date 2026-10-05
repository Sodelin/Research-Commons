import G1UnrankedSourceView

/-! Actual original source generator and one-step law factor through the
whole rooted UNRANKED labelled view. Contributor: dot, 2026-10-03. -/
namespace G1UnrankedActualGenerator
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestGeneratorIntertwining
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open G1UnrankedSourceView
open scoped Classical BigOperators
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_unranked_population_generator (v w : SelectedView V E Copy)
    (h : unrankedView v = unrankedView w) (keep : Finset Copy) (place : Location V E)
    (rate : ℝ) (F : UnrankedView V E Copy → ℝ) :
    viewPopulationGenerator v keep place rate (F ∘ unrankedView) =
      viewPopulationGenerator w keep place rate (F ∘ unrankedView) := by
  unfold viewPopulationGenerator
  rw [actual_unranked_population_blocks v w h keep place]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  simp only [Function.comp_apply,actual_unranked_projected_merger v w h p.1 p.2,h]

theorem actual_unranked_intrinsic_generator (root : V) (v w : SelectedView V E Copy)
    (h : unrankedView v = unrankedView w) (keep : Finset Copy)
    (r : PositivePairRates E) (F : UnrankedView V E Copy → ℝ) :
    intrinsicSourceGenerator root v keep r.edge r.ancestral (F ∘ unrankedView) =
      intrinsicSourceGenerator root w keep r.edge r.ancestral (F ∘ unrankedView) := by
  unfold intrinsicSourceGenerator
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    exact actual_unranked_population_generator v w h keep (.edge e) (r.edge e) F
  · exact actual_unranked_population_generator v w h keep (.rootPopulation root) r.ancestral F

/-- Concrete actual PMF expectation is invariant under current representative
implementation IDs and child orientations, retaining ALL original clades,
population IDs and the SAME original register. -/
theorem actual_unranked_source_step_expectation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s z : Code N sample)
    (h : unrankedView (selectedView (state s) keep) = unrankedView (selectedView (state z) keep))
    (F : UnrankedView V E Copy → ℝ) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * F (unrankedView (selectedView (state d) keep))) =
      ∑ d : Code N sample, (sourceStep N r z d).toReal * F (unrankedView (selectedView (state d) keep)) := by
  have hs := sourceStep_selected_expectation_intrinsic N r s keep (F ∘ unrankedView)
  have hz := sourceStep_selected_expectation_intrinsic N r z keep (F ∘ unrankedView)
  simp only [Function.comp_apply] at hs hz
  rw [hs,hz,h,actual_unranked_intrinsic_generator N.root _ _ h keep r F]

abbrev UnrankedIndex (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) :=
  {v : UnrankedView V E Copy // ∃ s : Code N sample, unrankedView (selectedView (state s) keep) = v}

noncomputable def unrankedProjection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) : UnrankedIndex N sample keep :=
  ⟨unrankedView (selectedView (state s) keep),⟨s,rfl⟩⟩

noncomputable instance unrankedIndexFintype (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) : Fintype (UnrankedIndex N sample keep) :=
  Fintype.ofSurjective (unrankedProjection N keep) (by
    intro v; obtain ⟨s,hs⟩ := v.property; exact ⟨s,Subtype.ext hs⟩)

/-- Whole actual original source step law, not only test moments, descends
to the exact rooted unranked label/population/register interface. -/
theorem actual_unranked_step_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s z : Code N sample)
    (h : unrankedView (selectedView (state s) keep) = unrankedView (selectedView (state z) keep)) :
    (sourceStep N r s).map (unrankedProjection N keep) =
      (sourceStep N r z).map (unrankedProjection N keep) := by
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [map_probability_real,map_probability_real]
  have he (d : Code N sample) : unrankedProjection N keep d = v ↔
      unrankedView (selectedView (state d) keep) = v.val := Subtype.ext_iff
  simp_rw [he]
  exact actual_unranked_source_step_expectation N r keep s z h (fun w => if w = v.val then 1 else 0)

#print axioms actual_unranked_step_row_independent
end G1UnrankedActualGenerator
