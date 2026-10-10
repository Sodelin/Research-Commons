import UnifiedLean.Source.SourceSmallCarrierGenerator

/-!
# Actual full/small ORIGINAL source epoch kernels share one selected law

Contributor: dot, 2026-10-02. Forms the finite disjoint union of the TWO actual
source-code carriers and their actual generator matrices. The common view row
is derived from the proved full and independently initialized small-source
operators, so unequal copy-dependent uniformization rates are not equated.
No cross-carrier generator/semigroup identity is supplied as an input field.
-/
namespace UnifiedLean.Source.SourceCrossCarrierEpoch
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceEpochRenewal
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceSmallCarrierGenerator
open UnifiedLean.Source.MatrixProjectionExponential
open Matrix NormedSpace
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev JoinedCode (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) :=
  Code N sample ⊕ Code N (selectedSample sample keep)

noncomputable def joinedView (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) : JoinedCode N sample keep → SelectedView V E Copy
  | .inl s => selectedView (state s) keep
  | .inr s => liftView keep (selectedView (state s) Finset.univ)

abbrev JoinedIndex (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) :=
  {v : SelectedView V E Copy // ∃ s : JoinedCode N sample keep, joinedView N keep s = v}

noncomputable def joinedProjection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : JoinedCode N sample keep) : JoinedIndex N sample keep :=
  ⟨joinedView N keep s,⟨s,rfl⟩⟩

noncomputable instance joinedIndexFintype (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) : Fintype (JoinedIndex N sample keep) :=
  Fintype.ofSurjective (joinedProjection N keep) (by
    intro v; obtain ⟨s,hs⟩ := v.property; exact ⟨s,Subtype.ext hs⟩)

noncomputable def joinedRepresentative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : JoinedIndex N sample keep) : JoinedCode N sample keep :=
  Classical.choose v.property

lemma joinedRepresentative_view (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : JoinedIndex N sample keep) :
    joinedView N keep (joinedRepresentative N keep v) = v.val := Classical.choose_spec v.property

noncomputable def joinedGenerator (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Matrix (JoinedCode N sample keep) (JoinedCode N sample keep) ℝ :=
  fromBlocks (sourceGeneratorMatrix N (sample := sample) r) 0 0
    (sourceGeneratorMatrix N (sample := selectedSample sample keep) r)

lemma original_generator_function (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (F : Code N sample → ℝ) :
    (∑ d : Code N sample, sourceGeneratorMatrix N (sample := sample) r s d * F d) =
      ∑ p : Choice N s, choiceRate N r s p * (F (stepDestination N s (some p))-F s) := by
  have h := actual_generator_row N r s s (fun d _ => F d)
  change (∑ d : Code N sample, sourceGeneratorMatrix N (sample := sample) r s d * F d) =
    (∑ p : Choice N s, choiceRate N r s p * F (stepDestination N s (some p))) - totalRate N r s*F s at h
  rw [h]
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,totalRate]

/-- Concrete actual full/small generator row equality on the original-labelled
view, derived from legal source mergers and original rate assignments. -/
theorem joined_actual_generator_action (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : JoinedCode N sample keep)
    (f : SelectedView V E Copy → ℝ) :
    (∑ d : JoinedCode N sample keep, joinedGenerator N r keep s d * f (joinedView N keep d)) =
      intrinsicSourceGenerator N.root (joinedView N keep s) keep r.edge r.ancestral f := by
  cases s with
  | inl s =>
      simp only [Fintype.sum_sum_type,joinedGenerator,fromBlocks_apply₁₁,fromBlocks_apply₁₂,
        Matrix.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,joinedView]
      rw [original_generator_function,actual_choice_increment_eq_native_generator,
        native_source_generator_intertwining N.root (state s) s.property.forest keep r.edge r.ancestral f]
  | inr s =>
      simp only [Fintype.sum_sum_type,joinedGenerator,fromBlocks_apply₂₁,fromBlocks_apply₂₂,
        Matrix.zero_apply,zero_mul,Finset.sum_const_zero,zero_add,joinedView]
      rw [original_generator_function]
      have h := actual_choice_increment_eq_native_generator N r s Finset.univ (fun v => f (liftView keep v))
      rw [h,small_original_source_generator N.root keep (state s) s.property.forest r.edge r.ancestral f]

noncomputable def joinedProjectionMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) : Matrix (JoinedCode N sample keep) (JoinedIndex N sample keep) ℝ :=
  fun s v => if joinedProjection N keep s = v then 1 else 0

/-- The common generator is the actual row of an actual full OR small source
representative. The preceding source theorem proves representation independence. -/
noncomputable def commonViewGenerator (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Matrix (JoinedIndex N sample keep) (JoinedIndex N sample keep) ℝ :=
  fun v w => ∑ d : JoinedCode N sample keep,
    joinedGenerator N r keep (joinedRepresentative N keep v) d * joinedProjectionMatrix N keep d w

lemma projected_joined_generator_action (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : JoinedCode N sample keep)
    (v : JoinedIndex N sample keep) :
    (∑ d : JoinedCode N sample keep, joinedGenerator N r keep s d * joinedProjectionMatrix N keep d v) =
      intrinsicSourceGenerator N.root (joinedView N keep s) keep r.edge r.ancestral
        (fun w => if w = v.val then 1 else 0) := by
  have h := joined_actual_generator_action N r keep s (fun w => if w = v.val then 1 else 0)
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  have he : joinedProjection N keep d = v ↔ joinedView N keep d = v.val := Subtype.ext_iff
  simp only [joinedProjectionMatrix,he]

/-- Actual cross-carrier generator matrix instance, without an assumed
intertwining equation. Original full/small source parameters are identical. -/
theorem actual_cross_carrier_generator_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) :
    joinedGenerator N (sample := sample) r keep * joinedProjectionMatrix N keep =
      joinedProjectionMatrix N keep * commonViewGenerator N r keep := by
  ext s v
  rw [Matrix.mul_apply,Matrix.mul_apply]
  change (∑ d : JoinedCode N sample keep, joinedGenerator N r keep s d * joinedProjectionMatrix N keep d v) =
    ∑ w : JoinedIndex N sample keep, (if joinedProjection N keep s = w then 1 else 0) * commonViewGenerator N r keep w v
  rw [show (∑ w : JoinedIndex N sample keep, (if joinedProjection N keep s = w then (1 : ℝ) else 0) *
      commonViewGenerator N r keep w v) = commonViewGenerator N r keep (joinedProjection N keep s) v by simp]
  rw [commonViewGenerator,projected_joined_generator_action,projected_joined_generator_action,
    joinedRepresentative_view]
  rfl

/-- Library matrix-exponential transport now instantiated by the ACTUAL two
source operators, whose uniformization constants may differ. -/
theorem actual_cross_carrier_exponential_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ) :
    exp (t • joinedGenerator N (sample := sample) r keep) * joinedProjectionMatrix N keep =
      joinedProjectionMatrix N keep * exp (t • commonViewGenerator N r keep) :=
  rectangular_scaled_exp_intertwining _ _ _ (actual_cross_carrier_generator_intertwining N r keep) t

lemma joined_exponential_blocks (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ) :
    exp (t • joinedGenerator N (sample := sample) r keep) =
      fromBlocks (exp (t • sourceGeneratorMatrix N (sample := sample) r)) 0 0
        (exp (t • sourceGeneratorMatrix N (sample := selectedSample sample keep) r)) := by
  rw [joinedGenerator,Matrix.fromBlocks_smul]
  simp only [smul_zero]
  exact exp_fromBlocks_diagonal _ _

lemma joined_exponential_projected_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ) (s : JoinedCode N sample keep)
    (v : JoinedIndex N sample keep) :
    (∑ d : JoinedCode N sample keep, (exp (t • joinedGenerator N r keep)) s d *
      joinedProjectionMatrix N keep d v) =
      (exp (t • commonViewGenerator N r keep)) (joinedProjection N keep s) v := by
  have h := congrArg (fun M => M s v) (actual_cross_carrier_exponential_intertwining N r keep t)
  simpa [Matrix.mul_apply,joinedProjectionMatrix] using h

/-- Actual full-source finite-time probabilities on the common view. -/
lemma full_actual_time_common_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) (s : Code N sample)
    (v : JoinedIndex N sample keep) :
    (((sourceTimeKernel N r t s).map (fun d => joinedProjection N keep (.inl d))) v).toReal =
      (exp ((t : ℝ) • commonViewGenerator N r keep)) (joinedProjection N keep (.inl s)) v := by
  rw [map_probability_real]
  have h := joined_exponential_projected_row N r keep (t : ℝ) (.inl s) v
  rw [joined_exponential_blocks] at h
  simp only [Fintype.sum_sum_type,fromBlocks_apply₁₁,fromBlocks_apply₁₂,Matrix.zero_apply,
    zero_mul,Finset.sum_const_zero,add_zero] at h
  simp_rw [← source_time_kernel_eq_exponential] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : joinedProjection N keep (.inl d) = v
  · simp only [joinedProjectionMatrix,if_pos hd]
  · simp only [joinedProjectionMatrix,if_neg hd]


/-- Actual independently initialized small-source finite-time probabilities,
using its OWN proved normalization constant and the SAME original rates. -/
lemma small_actual_time_common_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0)
    (s : Code N (selectedSample sample keep)) (v : JoinedIndex N sample keep) :
    (((sourceTimeKernel N r t s).map (fun d => joinedProjection N keep (.inr d))) v).toReal =
      (exp ((t : ℝ) • commonViewGenerator N r keep)) (joinedProjection N keep (.inr s)) v := by
  rw [map_probability_real]
  have h := joined_exponential_projected_row N r keep (t : ℝ) (.inr s) v
  rw [joined_exponential_blocks] at h
  simp only [Fintype.sum_sum_type,fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply,
    zero_mul,Finset.sum_const_zero,zero_add] at h
  simp_rw [← source_time_kernel_eq_exponential] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : joinedProjection N keep (.inr d) = v
  · simp only [joinedProjectionMatrix,if_pos hd]
  · simp only [joinedProjectionMatrix,if_neg hd]


/-- Genuine equality of ACTUAL full-source pruned and independently initialized
small-source epoch PMFs, whenever their actual original-labelled views agree.
There is no assumed source comparison/kernel equation; normalization rates may
differ. Calendar pulses and final completed observation are the next assembly. -/
theorem actual_cross_carrier_source_time_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) (s : Code N sample)
    (z : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state z) Finset.univ)) :
    (sourceTimeKernel N r t s).map (fun d => joinedProjection N keep (.inl d)) =
      (sourceTimeKernel N r t z).map (fun d => joinedProjection N keep (.inr d)) := by
  have he : joinedProjection N keep (.inl s) = joinedProjection N keep (.inr z) := Subtype.ext hs
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [full_actual_time_common_row,small_actual_time_common_row,he]

#print axioms joined_actual_generator_action
#print axioms actual_cross_carrier_generator_intertwining
#print axioms actual_cross_carrier_exponential_intertwining
#print axioms actual_cross_carrier_source_time_law
end UnifiedLean.Source.SourceCrossCarrierEpoch
