import UnifiedLean.Source.SourceCompletedUnrankedTree
import UnifiedLean.Source.SourceEpochRenewal

/-!
# Actual ORIGINAL ancestral source rank drift

Contributor: dot, 2026-10-02. For the eventual G2 unranked completion limit,
derive a positive source-dependent contraction from actual root pairs. No
uniform unknown-rival contraction or hidden graph budget is asserted. All
rates and current catalogues are the original source's actual parameters.
-/
namespace UnifiedLean.Source.SourceAncestralDrift
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourceAncestralCompletion
open scoped Classical BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def excessRank {N : RootedBinary V E X} {sample : Copy → X}
    (s : Code N sample) : ℝ := (liveCard s : ℝ)-1

lemma excessRank_nonnegative [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) : 0 ≤ excessRank s := by
  have hp := admitted_live_card_positive N s
  unfold excessRank
  have hh : (1 : ℝ) ≤ (liveCard s : ℝ) := by exact_mod_cast hp
  linarith

/-- One actual root ancestor supplies a distinct legal clock with every other
current root. This proves a linear ORIGINAL ancestral-rate lower bound. -/
theorem actual_ancestral_total_rate_lower [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (r.ancestral/2) * excessRank s ≤ totalRate N r s := by
  obtain ⟨x⟩ := ‹Nonempty Copy›
  let a := (state s).ancestor x
  have ha : a ∈ (state s).live := s.property.forest.ancestor_live x
  let Others := {b : Copy // b ∈ (state s).live.erase a}
  let e : Others → Choice N s := fun b =>
    ⟨none,⟨(a,b.val),Finset.mem_offDiag.mpr
      ⟨Finset.mem_filter.mpr ⟨ha,ancestral_live_location N s hs ha⟩,
        Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp b.property).2,
          ancestral_live_location N s hs (Finset.mem_erase.mp b.property).2⟩,
        Ne.symm (Finset.mem_erase.mp b.property).1⟩⟩⟩
  have he : Function.Injective e := by
    intro b c h
    exact Subtype.ext (congrArg (fun p : Choice N s => p.2.val.2) h)
  have hsub : (∑ q ∈ Finset.univ.image e, choiceRate N r s q) ≤ totalRate N r s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro q _ _
    exact (div_pos (pairRate_pos r q.1) (by norm_num)).le
  rw [Finset.sum_image (fun _ _ _ _ h => he h)] at hsub
  have hw : ∀ b : Others, choiceRate N r s (e b) = r.ancestral/2 := fun _ => rfl
  simp only [hw,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsub
  have hcard := Finset.card_erase_add_one ha
  have hc : ((state s).live.erase a).card = liveCard s-1 := by
    change _ + 1 = liveCard s at hcard
    omega
  have hcR : (((state s).live.erase a).card : ℝ) = excessRank s := by
    unfold excessRank
    have hh : ((((state s).live.erase a).card : ℝ)+1) = (liveCard s : ℝ) := by exact_mod_cast hcard
    linarith
  have hOthers : Fintype.card Others = ((state s).live.erase a).card := by
    dsimp [Others]
    exact Fintype.card_coe _
  rw [hOthers] at hsub
  rw [hcR,mul_comm] at hsub
  exact hsub

lemma merged_excessRank (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) : excessRank (stepDestination N s (some p)) = excessRank s-1 := by
  have h := merger_destination_card N s p
  have hh : ((liveCard (stepDestination N s (some p)) : ℝ)+1) = (liveCard s : ℝ) := by exact_mod_cast h
  unfold excessRank
  linarith

/-- Exact rank drift of the ACTUAL normalized source PMF, not a fitted Markov
table or an assumed contraction. Dummy holds correctly contribute zero drift. -/
theorem actual_source_excessRank_expectation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * excessRank d) =
      excessRank s-totalRate N r s/globalRateBound (Copy := Copy) r := by
  rw [sourceStep_expectation,Fintype.sum_option]
  simp only [choiceMass,merged_excessRank]
  change (1-totalRate N r s/globalRateBound (Copy := Copy) r)*excessRank s +
    (∑ p : Choice N s, (choiceRate N r s p/globalRateBound (Copy := Copy) r)*(excessRank s-1)) = _
  rw [← Finset.sum_mul,← Finset.sum_div]
  change (1-totalRate N r s/globalRateBound (Copy := Copy) r)*excessRank s +
    (totalRate N r s/globalRateBound (Copy := Copy) r)*(excessRank s-1) = _
  ring

/-- Fixed-source positive ancestral rate yields the necessary strict rank
contraction. Its constant depends on this original graph/rate/copy carrier;
it is not uniform over all unknown G4 rivals. -/
theorem actual_ancestral_excessRank_contraction [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * excessRank d) ≤
      (1-(r.ancestral/2)/globalRateBound (Copy := Copy) r)*excessRank s := by
  rw [actual_source_excessRank_expectation]
  have hbound := div_le_div_of_nonneg_right (actual_ancestral_total_rate_lower N r s hs)
    (globalRateBound_positive (Copy := Copy) r).le
  have hb : ((r.ancestral/2)/globalRateBound (Copy := Copy) r)*excessRank s ≤
      totalRate N r s/globalRateBound (Copy := Copy) r := by
    have heq : ((r.ancestral/2)/globalRateBound (Copy := Copy) r)*excessRank s =
        ((r.ancestral/2)*excessRank s)/globalRateBound (Copy := Copy) r := by ring
    rw [heq]
    exact hbound
  nlinarith

#print axioms actual_ancestral_total_rate_lower
#print axioms actual_source_excessRank_expectation
#print axioms actual_ancestral_excessRank_contraction
end UnifiedLean.Source.SourceAncestralDrift
