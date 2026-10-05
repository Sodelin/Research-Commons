import UnifiedLean.Source.SourceEpochRenewal

/-!
# Finite real-merger expansion of the actual ORIGINAL source epoch law

Contributor: dot, 2026-10-02. Expands the proved actual first-jump recursion
using literal original pair densities and actual destinations. Strict live
cardinality descent proves this finite recursive integral exactly equals the
actual source PMF once the budget reaches the supplied copy carrier size.
This is the connected analytic half of the literal clock-path binding;
measurable timed path pushforward and terminal observation are still pending.
-/
namespace UnifiedLean.Source.SourceFiniteJumpExpansion
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceEpochRenewal
open UnifiedLean.Source.SourceEpochSemigroup
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- A concrete finite first-jump density recursion. It uses the original
source destinations and densities, not an asserted transition law field. -/
noncomputable def finiteJumpMass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Nat → ℝ≥0 → Code N sample → Code N sample → ℝ
  | 0,t,s,d => Real.exp (-(totalRate N r s*(t : ℝ))) * (if s = d then 1 else 0)
  | n+1,t,s,d => Real.exp (-(totalRate N r s*(t : ℝ))) * (if s = d then 1 else 0) +
      ∫ u in 0..(t : ℝ), Real.exp (-(totalRate N r s*u)) *
        ∑ p : Choice N s, choiceRate N r s p *
          finiteJumpMass N r n (Real.toNNReal ((t : ℝ)-u)) (stepDestination N s (some p)) d

lemma choice_empty_of_zero_live (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : liveCard s = 0) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have hp := (Finset.mem_offDiag.mp p.2.property).1
  have hl := populationRoots_subset_live (state s) (originalPlace N p.1) hp
  have hc : (state s).live.card = 0 := hs
  rw [Finset.card_eq_zero] at hc
  rw [hc] at hl
  simpa using hl

/-- All real mergers lower the actual source's live-copy cardinality. Thus
the concrete finite clock-density recursion closes the ACTUAL entire epoch
transition law, without an unknown source-size budget or uniqueness premise. -/
theorem finite_jump_mass_eq_source_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (t : ℝ≥0) (s d : Code N sample)
    (hn : liveCard s ≤ n) : finiteJumpMass N r n t s d = (sourceTimeKernel N r t s d).toReal := by
  induction n generalizing t s with
  | zero =>
      have hs : liveCard s = 0 := by omega
      letI := choice_empty_of_zero_live N s hs
      rw [actual_source_kernel_first_jump]
      simp only [finiteJumpMass,Finset.univ_eq_empty,Finset.sum_empty,mul_zero,
        intervalIntegral.integral_zero,add_zero]
  | succ n ih =>
      rw [finiteJumpMass,actual_source_kernel_first_jump]
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [ih _ (stepDestination N s (some p)) (by
        have hc := merger_destination_card N s p
        omega)]

/-- Uniform finite expansion for this SAME original supplied copy carrier.
This budget follows from source live IDs and does not bound an unknown G3
graph presentation or permit uncoupled rowwise fitting. -/
theorem original_copy_cap_jump_expansion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample) :
    finiteJumpMass N r (Fintype.card Copy) t s d = (sourceTimeKernel N r t s d).toReal :=
  finite_jump_mass_eq_source_kernel N r _ t s d (Finset.card_le_univ s.val.live)

/-- Nonnegativity and normalization of this concrete finite density expansion
are consequences of its proved actual-source equality, not input axioms. -/
theorem original_jump_expansion_stochastic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (∀ d : Code N sample, 0 ≤ finiteJumpMass N r (Fintype.card Copy) t s d) ∧
      (∑ d : Code N sample, finiteJumpMass N r (Fintype.card Copy) t s d) = 1 := by
  simp_rw [original_copy_cap_jump_expansion]
  exact ⟨fun _ => ENNReal.toReal_nonneg,pmf_sum_real _⟩

#print axioms finite_jump_mass_eq_source_kernel
#print axioms original_copy_cap_jump_expansion
#print axioms original_jump_expansion_stochastic
end UnifiedLean.Source.SourceFiniteJumpExpansion
