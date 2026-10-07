import UnifiedLean.Source.SourceCompletionHarmonic

/-!
UNCHECKED additive derivative, CLOUD-G6-SOL-ULTRA-20261007, 2026-10-07.
Specializes the original actual jump/completion kernels on AncestralRoot.
Classical uniform pair choice is prior; this file connects its rate cancellation
and rational row formula to the SAME source Code/merger/completion definitions.
No equality of unbinned waiting ages or executable enumeration is claimed.
-/
namespace UnifiedLean.G6.AncestralRateFree
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open scoped Classical BigOperators

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma ancestral_choice_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) (p : Choice N s) : p.1 = none := by
  have hp : p.2.val.1 ∈ populationRoots (state s) (originalPlace N p.1) :=
    (Finset.mem_offDiag.mp p.2.property).1
  have hm := Finset.mem_filter.mp hp
  have hloc : Location.rootPopulation N.root = originalPlace N p.1 :=
    (ancestral_live_location N s hs hm.1).symm.trans hm.2
  cases hi : p.1 with
  | none => exact hi
  | some e =>
    have hbad : Location.rootPopulation N.root = Location.edge e := by
      simpa only [hi, originalPlace] using hloc
    cases hbad

lemma ancestral_choice_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s)
    (p : Choice N s) : choiceRate N r s p = pairRate r none / 2 := by
  unfold choiceRate
  rw [ancestral_choice_population N s hs p]

lemma ancestral_total_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    totalRate N r s = (Fintype.card (Choice N s) : ℝ) * (pairRate r none / 2) := by
  unfold totalRate
  simp_rw [ancestral_choice_rate N r s hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A formula on the SAME ordered Choice carrier, with terminal holding. -/
noncomputable def ancestralChoiceMass (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Option (Choice N s) → ℝ
  | none => if Fintype.card (Choice N s) = 0 then 1 else 0
  | some _ => 1 / (Fintype.card (Choice N s) : ℝ)

lemma ancestral_jump_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s)
    (q : Option (Choice N s)) : jumpMass N r s q = ancestralChoiceMass N s q := by
  have hr : pairRate r none / 2 ≠ 0 := ne_of_gt (div_pos (pairRate_pos r none) (by norm_num))
  have hz : totalRate N r s = 0 ↔ Fintype.card (Choice N s) = 0 := by
    rw [ancestral_total_rate N r s hs, mul_eq_zero]
    simp [hr]
  cases q with
  | none => simp only [jumpMass, hz, ancestralChoiceMass]
  | some p =>
    letI : Nonempty (Choice N s) := ⟨p⟩
    have hc : (Fintype.card (Choice N s) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Choice N s) ≠ 0)
    rw [jumpMass, ancestral_choice_rate N r s hs p, ancestral_total_rate N r s hs]
    dsimp only [ancestralChoiceMass]
    field_simp [hc, hr]

noncomputable def rationalAncestralChoiceMass (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) : Option (Choice N s) → ℚ
  | none => if Fintype.card (Choice N s) = 0 then 1 else 0
  | some _ => 1 / (Fintype.card (Choice N s) : ℚ)

lemma rational_ancestral_choice_mass_actual (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) (q : Option (Choice N s)) :
    (rationalAncestralChoiceMass N s q : ℝ) = jumpMass N r s q := by
  rw [ancestral_jump_mass N r s hs q]
  cases q with
  | none =>
    by_cases hc : Fintype.card (Choice N s) = 0 <;>
      simp [rationalAncestralChoiceMass, ancestralChoiceMass, hc]
  | some p => simp [rationalAncestralChoiceMass, ancestralChoiceMass]

lemma ancestral_jump_choice_rate_invariant (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) : sourceJumpChoice N r s = sourceJumpChoice N rhat s := by
  apply PMF.ext
  intro q
  rw [sourceJumpChoice_apply, sourceJumpChoice_apply,
    ancestral_jump_mass N r s hs q, ancestral_jump_mass N rhat s hs q]

lemma ancestral_jump_step_rate_invariant (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) : sourceJumpStep N r s = sourceJumpStep N rhat s := by
  rw [sourceJumpStep, sourceJumpStep, ancestral_jump_choice_rate_invariant N r rhat s hs]

theorem ancestral_completion_rate_invariant (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (k : ℕ)
    (s : Code N sample) (hs : AncestralRoot N s) :
    ancestralCompletion N r k s = ancestralCompletion N rhat k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [ancestralCompletion, ancestralCompletion,
      ancestral_jump_step_rate_invariant N r rhat s hs]
    apply bind_congr_on_support
    intro d hd
    rcases source_jump_support_cases N rhat s hd with ⟨he, _⟩ | ⟨p, he⟩
    · subst d
      exact ih s hs
    · subst d
      exact ih _ (ancestral_merger_preserved N s hs p)

theorem completion_kernel_rate_invariant (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) : completionKernel N r s = completionKernel N rhat s :=
  ancestral_completion_rate_invariant N r rhat (Fintype.card Copy) s hs

#print axioms ancestral_choice_population
#print axioms ancestral_choice_rate
#print axioms ancestral_total_rate
#print axioms ancestral_jump_mass
#print axioms rational_ancestral_choice_mass_actual
#print axioms ancestral_jump_choice_rate_invariant
#print axioms ancestral_jump_step_rate_invariant
#print axioms ancestral_completion_rate_invariant
#print axioms completion_kernel_rate_invariant
end UnifiedLean.G6.AncestralRateFree
