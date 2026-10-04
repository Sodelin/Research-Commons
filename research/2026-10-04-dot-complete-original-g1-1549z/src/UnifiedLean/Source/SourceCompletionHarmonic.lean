import UnifiedLean.Source.SourceAncestralAbsorption

/-!
# Actual ancestral completion is harmonic for the ORIGINAL source kernel

Contributor: dot, 2026-10-02. The finite winner-jump completion is proved
stable and harmonic for the actual uniformized/Poisson source, not supplied
as a desired terminal law. Together with source-derived transient decay this
identifies the eventual unranked ancestral law.
-/
namespace UnifiedLean.Source.SourceCompletionHarmonic
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMarkDistribution
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceAncestralAbsorption
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma bind_congr_on_support {A B : Type*} (p : PMF A) (f g : A → PMF B)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff,not_not] using ha
    simp [hz]

/-- Completion is stable after the proved original live-card budget. -/
theorem ancestral_completion_stabilizes (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (hs : AncestralRoot N s)
    (hn : liveCard s ≤ n) : ancestralCompletion N r (n+1) s = ancestralCompletion N r n s := by
  induction n generalizing s with
  | zero =>
      have hc : liveCard s ≤ 1 := by omega
      rw [ancestral_completion_fixed_terminal N r 1 s hc,ancestral_completion_fixed_terminal N r 0 s hc]
  | succ n ih =>
      by_cases hc : liveCard s ≤ 1
      · rw [ancestral_completion_fixed_terminal N r (n+1+1) s hc,
          ancestral_completion_fixed_terminal N r (n+1) s hc]
      · change (sourceJumpStep N r s).bind (ancestralCompletion N r (n+1)) =
          (sourceJumpStep N r s).bind (ancestralCompletion N r n)
        apply bind_congr_on_support
        intro d hd
        rcases source_jump_support_cases N r s hd with ⟨_,hz⟩ | ⟨p,hp⟩
        · obtain ⟨p0⟩ := ancestral_choice_exists N s hs (lt_of_not_ge hc)
          exact False.elim ((current_pair_total_positive N r s p0).ne' hz)
        · subst d
          exact ih _ (ancestral_merger_preserved N s hs p)
            (by have hh := merger_destination_card N s p; omega)

noncomputable def completionKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Code N sample) :=
  ancestralCompletion N r (Fintype.card Copy) s

lemma completion_jump_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceJumpStep N r s).bind (completionKernel N r) = completionKernel N r s := by
  exact ancestral_completion_stabilizes N r (Fintype.card Copy) s hs (Finset.card_le_univ s.val.live)

lemma completion_terminal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : liveCard s ≤ 1) :
    completionKernel N r s = PMF.pure s := ancestral_completion_fixed_terminal N r _ s hs

/-- Completion is harmonic for actual normalized source steps, including
all genuine hold mass. The identity is derived from original rate fractions. -/
theorem completion_source_step_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceStep N r s).bind (completionKernel N r) = completionKernel N r s := by
  have hj := completion_jump_harmonic N r s hs
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [bind_probability_real,tsum_fintype,sourceStep_expectation,Fintype.sum_option]
  simp only [choiceMass]
  by_cases hz : totalRate N r s = 0
  · letI := choice_empty_of_zero_rate N r s hz
    simp [hz,stepDestination]
  · have he := congrArg (fun p : PMF (Code N sample) => (p z).toReal) hj
    rw [sourceJumpStep,PMF.bind_map,bind_probability_real,tsum_fintype,Fintype.sum_option] at he
    simp_rw [sourceJumpChoice_apply,ENNReal.toReal_ofReal (jumpMass_nonnegative N r s _)] at he
    simp only [jumpMass,if_neg hz,zero_mul,zero_add,Function.comp_apply] at he
    have hsums : (∑ p : Choice N s, choiceRate N r s p *
        (completionKernel N r (stepDestination N s (some p)) z).toReal) =
        totalRate N r s * (completionKernel N r s z).toReal := by
      simp_rw [div_mul_eq_mul_div] at he
      rw [← Finset.sum_div] at he
      exact ((div_eq_iff hz).mp he).trans (mul_comm _ _)
    change (1-totalRate N r s/globalRateBound (Copy := Copy) r)*
        (completionKernel N r s z).toReal +
        (∑ p : Choice N s, (choiceRate N r s p/globalRateBound (Copy := Copy) r)*
          (completionKernel N r (stepDestination N s (some p)) z).toReal) = _
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,hsums]
    ring

/-- The completed actual jump law is invariant under every actual source
iteration, using ancestral support rather than a globally asserted row law. -/
theorem completion_source_iteration_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceIteration N r k s).bind (completionKernel N r) = completionKernel N r s := by
  induction k generalizing s with
  | zero => simp [sourceIteration]
  | succ k ih =>
      rw [sourceIteration,PMF.bind_bind]
      calc
        _ = (sourceStep N r s).bind (completionKernel N r) := by
          apply bind_congr_on_support
          intro d hd
          exact ih d (ancestral_step_support N r s hs hd)
        _ = _ := completion_source_step_harmonic N r s hs

/-- Exact source-time kernel followed by actual completion equals the same
completed original-source law, for every nonnegative ancestral duration. -/
theorem completion_source_time_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceTimeKernel N r t s).bind (completionKernel N r) = completionKernel N r s := by
  rw [sourceTimeKernel,PMF.bind_bind]
  simp_rw [completion_source_iteration_harmonic N r _ s hs]
  exact PMF.bind_const _ _

#print axioms ancestral_completion_stabilizes
#print axioms completion_source_step_harmonic
#print axioms completion_source_iteration_harmonic
#print axioms completion_source_time_harmonic
end UnifiedLean.Source.SourceCompletionHarmonic
