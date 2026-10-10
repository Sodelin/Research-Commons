import UnifiedLean.Source.SourceStepGeneratorBinding
import UnifiedLean.Source.MatrixProjectionExponential
import Mathlib.Data.ENNReal.BigOperators

/-!
# Derived finite selected-view projection of the ACTUAL source step

Contributor: dot, 2026-10-02. The target carrier is the actual finite range of
source-valid code views. Equality of projected source step laws is DERIVED from
the concrete source generator binding. Choosing a representative defines the
projected row, and its independence of that choice is proved. No source law or
matrix-intertwining identity is an assumption field. Stochastic finite-time and
calendar/timed observation connections are later gates.
-/
namespace UnifiedLean.Source.SourceFiniteProjection
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open Matrix
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev SelectedIndex (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) :=
  {v : SelectedView V E Copy // ∃ s : Code N sample, selectedView (state s) keep = v}

noncomputable def projection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) : SelectedIndex N sample keep :=
  ⟨selectedView (state s) keep,⟨s,rfl⟩⟩

noncomputable instance selectedIndexFintype (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) : Fintype (SelectedIndex N sample keep) :=
  Fintype.ofSurjective (projection N keep) (by
    intro v
    obtain ⟨s,hs⟩ := v.property
    exact ⟨s,Subtype.ext hs⟩)

noncomputable def representative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) : Code N sample :=
  Classical.choose v.property

lemma representative_view (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) :
    selectedView (state (representative N keep v)) keep = v.val :=
  Classical.choose_spec v.property

lemma map_probability_real {A B : Type*} [Fintype A] (p : PMF A) (phi : A → B) (b : B) :
    ((p.map phi) b).toReal = ∑ a : A, (p a).toReal * if phi a = b then 1 else 0 := by
  classical
  rw [PMF.map_apply,tsum_fintype,ENNReal.toReal_sum (by
    intro a _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : phi a = b
  · simp only [if_pos h.symm,if_pos h,mul_one]
  · simp only [if_neg (Ne.symm h),if_neg h,ENNReal.toReal_zero,mul_zero]

noncomputable def projectedStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample) :
    PMF (SelectedIndex N sample keep) :=
  (sourceStep N r s).map (projection N keep)

lemma projectedStep_real (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample)
    (v : SelectedIndex N sample keep) :
    (projectedStep N r keep s v).toReal =
      ∑ d : Code N sample, (sourceStep N r s d).toReal *
        if selectedView (state d) keep = v.val then 1 else 0 := by
  rw [projectedStep,map_probability_real]
  apply Finset.sum_congr rfl
  intro d _
  have h : projection N keep d = v ↔ selectedView (state d) keep = v.val :=
    Subtype.ext_iff
  simp only [h]

/-- The target row is genuinely independent of all hidden representative
choices because its ACTUAL source PMF expectation factors through the view. -/
theorem projectedStep_eq_of_same_view (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s t : Code N sample)
    (h : selectedView (state s) keep = selectedView (state t) keep) :
    projectedStep N r keep s = projectedStep N r keep t := by
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [projectedStep_real,projectedStep_real]
  let f : SelectedView V E Copy → ℝ := fun q => if q = v.val then 1 else 0
  change (∑ d : Code N sample, (sourceStep N r s d).toReal * f (selectedView (state d) keep)) =
    ∑ d : Code N sample, (sourceStep N r t d).toReal * f (selectedView (state d) keep)
  rw [sourceStep_selected_expectation_intrinsic,sourceStep_selected_expectation_intrinsic,h]

noncomputable def selectedStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (v : SelectedIndex N sample keep) :
    PMF (SelectedIndex N sample keep) :=
  projectedStep N r keep (representative N keep v)

/-- Exact whole selected-state probability law for one actual source step. -/
theorem source_step_projection_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample) :
    projectedStep N r keep s = selectedStep N r keep (projection N keep s) := by
  apply projectedStep_eq_of_same_view
  exact (representative_view N keep (projection N keep s)).symm

noncomputable def sourceTransition (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Matrix (Code N sample) (Code N sample) ℝ :=
  fun s t => (sourceStep N r s t).toReal

noncomputable def selectedTransition (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Matrix (SelectedIndex N sample keep) (SelectedIndex N sample keep) ℝ :=
  fun s t => (selectedStep N r keep s t).toReal

noncomputable def projectionMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) : Matrix (Code N sample) (SelectedIndex N sample keep) ℝ :=
  fun s v => if projection N keep s = v then 1 else 0

/-- Concrete original-source matrix identity, derived from the actual law;
it is the missing INSTANCE for the existing conditional exponential adapter. -/
theorem actual_source_transition_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) :
    sourceTransition N (sample := sample) r * projectionMatrix N (sample := sample) keep =
      projectionMatrix N (sample := sample) keep * selectedTransition N (sample := sample) r keep := by
  ext s v
  simp only [Matrix.mul_apply,sourceTransition,selectedTransition,projectionMatrix]
  have h := congrArg (fun p : PMF (SelectedIndex N sample keep) => (p v).toReal)
    (source_step_projection_law N r keep s)
  rw [projectedStep,map_probability_real] at h
  have hleft :
      (∑ a : Code N sample, (sourceStep N r s a).toReal *
        (if projection N keep a = v then 1 else 0)) =
      (∑ a : Code N sample, (sourceStep N r s a).toReal *
        (@ite ℝ (projection N keep a = v) (Classical.propDecidable _) 1 0)) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : projection N keep a = v
    · simp only [if_pos ha]
    · simp only [if_neg ha]
  calc
    _ = _ := hleft
    _ = ((selectedStep N r keep (projection N keep s)) v).toReal := h
    _ = _ := by simp

#print axioms map_probability_real
#print axioms projectedStep_eq_of_same_view
#print axioms source_step_projection_law
#print axioms actual_source_transition_intertwining
end UnifiedLean.Source.SourceFiniteProjection
