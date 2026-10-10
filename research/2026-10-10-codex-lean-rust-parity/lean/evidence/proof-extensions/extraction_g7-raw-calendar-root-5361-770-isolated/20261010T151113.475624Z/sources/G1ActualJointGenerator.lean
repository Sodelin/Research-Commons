import G1JointSeparatedSourceGeometry
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The actual separated source generator is a joint tensor sum

Contributor: dot, 2026-10-03. The guarded projection vanishes outside the
population separator. Source mergers preserve that separator in both
directions. The joint generator identity is derived from concrete original
source choices and their rates, not supplied as an independence premise.
-/
namespace G1ActualJointGenerator
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Matrix
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourceCrossCarrierEpoch
open G1JointSeparatedSourceGeometry
open scoped Classical BigOperators
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev JointIndex (N : RootedBinary V E X) (sample : Copy → X)
    (inside outside : Finset Copy) :=
  SelectedIndex N sample inside × SelectedIndex N sample outside

noncomputable def jointProjection (N : RootedBinary V E X) {sample : Copy → X}
    (inside outside : Finset Copy) (s : Code N sample) : JointIndex N sample inside outside :=
  (projection N inside s, projection N outside s)

noncomputable def separatedProjectionMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (inside outside : Finset Copy) : Matrix (Code N sample) (JointIndex N sample inside outside) ℝ :=
  fun s v => if PopulationSeparated (state s) inside outside then
    (if projection N inside s = v.1 then 1 else 0) *
      (if projection N outside s = v.2 then 1 else 0) else 0

noncomputable def jointGenerator (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E) (inside outside : Finset Copy) :
    Matrix (JointIndex N sample inside outside) (JointIndex N sample inside outside) ℝ :=
  fun v w => selectedGeneratorMatrix N r inside v.1 w.1 * (if v.2 = w.2 then 1 else 0) +
    (if v.1 = w.1 then 1 else 0) * selectedGeneratorMatrix N r outside v.2 w.2

lemma marginal_generator_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) (v : SelectedIndex N sample keep) :
    (∑ p : Choice N s, choiceRate N r s p *
      ((if projection N keep (stepDestination N s (some p)) = v then (1:ℝ) else 0) -
        (if projection N keep s = v then 1 else 0))) =
      selectedGeneratorMatrix N r keep (projection N keep s) v := by
  rw [← original_generator_function N r s (fun d => if projection N keep d = v then (1:ℝ) else 0)]
  have h := congrArg (fun M => M s v) (actual_source_generator_matrix_intertwining N r keep)
  simpa [Matrix.mul_apply,projectionMatrix] using h

lemma product_indicator_increment {A B : Type*} [DecidableEq A] [DecidableEq B]
    (a a' av : A) (b b' bv : B) (h : a' = a ∨ b' = b) :
    (if a' = av then (1:ℝ) else 0) * (if b' = bv then 1 else 0) -
        (if a = av then 1 else 0) * (if b = bv then 1 else 0) =
      ((if a' = av then 1 else 0) - (if a = av then 1 else 0)) *
        (if b = bv then 1 else 0) +
      (if a = av then 1 else 0) *
        ((if b' = bv then 1 else 0) - (if b = bv then 1 else 0)) := by
  rcases h with h | h
  · subst a'; ring
  · subst b'; ring

/-- The complete two-panel actual generator has no joint jump term. Both
subsystem generators retain the same original rates, register and labels. -/
theorem actual_joint_generator_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (inside outside : Finset Copy) :
    sourceGeneratorMatrix N (sample := sample) r * separatedProjectionMatrix N inside outside =
      separatedProjectionMatrix N inside outside * jointGenerator N r inside outside := by
  ext s v
  rw [Matrix.mul_apply,Matrix.mul_apply,original_generator_function]
  by_cases hsep : PopulationSeparated (state s) inside outside
  · have hpsep (p : Choice N s) : PopulationSeparated (state (stepDestination N s (some p))) inside outside :=
      (actual_step_separation_iff N s inside outside _).mpr hsep
    simp only [separatedProjectionMatrix,if_pos hsep]
    simp only [if_pos (hpsep _)]
    have hchange (p : Choice N s) :
        projection N inside (stepDestination N s (some p)) = projection N inside s ∨
        projection N outside (stepDestination N s (some p)) = projection N outside s := by
      exact (actual_choice_changes_at_most_one_panel N s inside outside hsep p).imp
        (fun h => Subtype.ext h) (fun h => Subtype.ext h)
    simp_rw [product_indicator_increment _ _ _ _ _ _ (hchange _),mul_add]
    rw [Finset.sum_add_distrib]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    have hright : (∑ p : Choice N s, (choiceRate N r s p *
        (if projection N inside s = v.1 then (1:ℝ) else 0)) *
          ((if projection N outside (stepDestination N s (some p)) = v.2 then 1 else 0) -
            (if projection N outside s = v.2 then 1 else 0))) =
        (if projection N inside s = v.1 then 1 else 0) *
          ∑ p : Choice N s, choiceRate N r s p *
            ((if projection N outside (stepDestination N s (some p)) = v.2 then 1 else 0) -
              (if projection N outside s = v.2 then 1 else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [hright,marginal_generator_row,marginal_generator_row]
    simp [Fintype.sum_prod_type,jointGenerator]
  · have hpsep (p : Choice N s) : ¬ PopulationSeparated (state (stepDestination N s (some p))) inside outside :=
      fun h => hsep ((actual_step_separation_iff N s inside outside _).mp h)
    simp [separatedProjectionMatrix,hsep,hpsep]

#print axioms actual_joint_generator_intertwining
end G1ActualJointGenerator
