import G3PhysicalFixtureAdmission
import G4WholeProfileDetermination

/-!
# Fixed-bank paths and actual legal rows of the literal pendant fixture

Author: dot / OpenAI, 2026-10-14.
UNCOMPILED SOURCE DRAFT, including its source-only admission dependency.

This composes existing same-selector path uniqueness, selected-edge exposure,
weighted normalization and legal padded-panel moment theorems. The source
tuple and original occurrence/copy conventions are unchanged. No native
numeric table, assumed source-law equality or new admission axiom is used.
-/

namespace DotG3.PhysicalFixture

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open GProgram.G5.AttainedChronology
open GProgram.G7.OriginalSurvivalCoverage
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.UnrankedGenealogyObservation
open DotG4.ActualSelectedPathExposure DotG4.WeightedOrdinaryTreeLaw
open DotG4.WholeProfileDetermination DotG4.ActualLegalPanelComb
open GProgram.G2.LiteralTimedObservationPruning DotG34.SpecifiedCombEvent
open scoped Classical BigOperators

def fixtureChosenArm (coin : CommonSeed fixtureN) : Fin 9 :=
  if coin (fixtureIDs 0) then 4 else 3

def fixtureAPath (coin : CommonSeed fixtureN) : List (Fin 9) :=
  [0, 2, fixtureChosenArm coin, 5]

private lemma fixture_nonarm_kept (coin : CommonSeed fixtureN) (e : Fin 9)
    (h3 : e ≠ 3) (h4 : e ≠ 4) : (commonSwitching fixtureN fixtureH coin).keep e := by
  have h : ∀ f : Fin 9, f ≠ 3 → f ≠ 4 →
      ¬ fixtureN.graph.IsHybrid (fixtureN.graph.target f) := by decide
  exact Or.inl (h e h3 h4)

lemma fixture_chosen_arm_kept (coin : CommonSeed fixtureN) :
    (commonSwitching fixtureN fixtureH coin).keep (fixtureChosenArm coin) := by
  exact Or.inr ⟨fixtureIDs 0, fixture_parent_exact (coin (fixtureIDs 0))⟩

lemma fixture_A_bank_path (coin : CommonSeed fixtureN) :
    EdgePath fixtureN.graph fixtureN.root (fixtureN.leaf 0) (fixtureAPath coin) := by
  cases hc : coin (fixtureIDs 0)
  · simpa [fixtureAPath, fixtureChosenArm, hc] using fixture_A_path_false
  · simpa [fixtureAPath, fixtureChosenArm, hc] using fixture_A_path_true

lemma fixture_A_respects (coin : CommonSeed fixtureN) :
    RespectsSelector fixtureN (coinSelector fixtureN fixtureH coin) (fixtureAPath coin) := by
  intro e he
  apply common_kept_edge_respects fixtureN fixtureH coin
  simp only [fixtureAPath, List.mem_cons, List.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact fixture_nonarm_kept coin 0 (by decide) (by decide)
  · exact fixture_nonarm_kept coin 2 (by decide) (by decide)
  · exact fixture_chosen_arm_kept coin
  · exact fixture_nonarm_kept coin 5 (by decide) (by decide)

lemma fixture_B_respects (coin : CommonSeed fixtureN) :
    RespectsSelector fixtureN (coinSelector fixtureN fixtureH coin) [0, 6] := by
  intro e he
  apply common_kept_edge_respects fixtureN fixtureH coin
  simp only [List.mem_cons, List.mem_singleton] at he
  rcases he with rfl | rfl
  · exact fixture_nonarm_kept coin 0 (by decide) (by decide)
  · exact fixture_nonarm_kept coin 6 (by decide) (by decide)

lemma fixture_A_route (coin : CommonSeed fixtureN) :
    (commonRoutes fixtureN fixtureC fixtureH coin).edges 0 = fixtureAPath coin := by
  change compiledRoute fixtureN fixtureC (coinSelector fixtureN fixtureH coin)
    (fixtureN.leaf 0) = fixtureAPath coin
  exact (original_path_eq_compiled_of_respects fixtureN fixtureC
    (coinSelector fixtureN fixtureH coin) (fixture_A_bank_path coin)
    (fixture_A_respects coin)).symm

lemma fixture_B_route (coin : CommonSeed fixtureN) :
    (commonRoutes fixtureN fixtureC fixtureH coin).edges 1 = [0, 6] := by
  change compiledRoute fixtureN fixtureC (coinSelector fixtureN fixtureH coin)
    (fixtureN.leaf 1) = [0, 6]
  exact (original_path_eq_compiled_of_respects fixtureN fixtureC
    (coinSelector fixtureN fixtureH coin) fixture_B_path
    (fixture_B_respects coin)).symm

private lemma fixture_pair_edge_exposure (e : Fin 9) :
    pairRate fixtureR (some e) *
      (fixtureC.age (fixtureN.graph.source e) - fixtureC.age (fixtureN.graph.target e)) =
      -Real.log (fixtureEdgeSurvival e) :=
  fixture_whole_edge_exposure e

/-- The finite difference uses occurrences 2, the chosen arm, and 5. -/
lemma fixture_selected_exposure (coin : CommonSeed fixtureN) :
    selectedDirectedExposure fixtureN fixtureC fixtureH fixtureR coin 0 1 =
      -Real.log (3/4 : ℝ) + -Real.log (8/9 : ℝ) + -Real.log (3/4 : ℝ) := by
  unfold selectedDirectedExposure
  simp_rw [fixture_A_route, fixture_B_route, fixture_pair_edge_exposure]
  cases hc : coin (fixtureIDs 0) <;>
    norm_num [fixtureAPath, fixtureChosenArm, hc, Fin.sum_univ_succ,
      fixtureEdgeSurvival, add_assoc]

lemma fixture_selected_survival (coin : CommonSeed fixtureN) :
    Real.exp (-selectedDirectedExposure fixtureN fixtureC fixtureH fixtureR coin 0 1) =
      (1/2 : ℝ) := by
  rw [fixture_selected_exposure]
  calc
    Real.exp (-(-Real.log (3/4 : ℝ) + -Real.log (8/9 : ℝ) +
      -Real.log (3/4 : ℝ))) =
        Real.exp (Real.log (3/4 : ℝ) + Real.log (8/9 : ℝ) + Real.log (3/4 : ℝ)) := by
          congr 1
          ring
    _ = (3/4 : ℝ) * (8/9 : ℝ) * (3/4 : ℝ) := by
      simp only [Real.exp_add,
        Real.exp_log (show (0 : ℝ) < 3/4 by norm_num),
        Real.exp_log (show (0 : ℝ) < 8/9 by norm_num)]
    _ = 1/2 := by norm_num

lemma fixture_selected_exposure_half (coin : CommonSeed fixtureN) :
    selectedDirectedExposure fixtureN fixtureC fixtureH fixtureR coin 0 1 =
      -Real.log (1/2 : ℝ) := by
  have he : Real.exp (-selectedDirectedExposure fixtureN fixtureC fixtureH fixtureR coin 0 1) =
      Real.exp (Real.log (1/2 : ℝ)) := by
    rw [Real.exp_log (show (0 : ℝ) < 1/2 by norm_num)]
    exact fixture_selected_survival coin
  have h := Real.exp_injective he
  linarith

lemma fixture_normalized_survival (coin : CommonSeed fixtureN) :
    directedSurvival (weightedNormalize fixtureN fixtureC fixtureH fixtureR coin) 0 1 =
      (1/2 : ℝ) := by
  unfold directedSurvival
  rw [weightedNormalize_directedExposure]
  exact fixture_selected_survival coin

def fixtureNaturalMasks : Unit → OriginalMask fixtureN := fun _ _ => none

def fixtureNu : PMF Unit := PMF.pure ()

lemma fixture_masked_survival (cfg : Unit) (coin : CommonSeed fixtureN) :
    directedSurvival
      (maskedNormalizedTree fixtureN fixtureC fixtureH fixtureR
        (fixtureNaturalMasks cfg) coin) 0 1 = (1/2 : ℝ) := by
  have ho : overrideBank fixtureN (fixtureNaturalMasks cfg) coin = coin := by
    funext h
    rfl
  rw [maskedNormalizedTree, ho]
  exact fixture_normalized_survival coin

/-- One fixed original source tuple supplies every positive legal copy level. -/
theorem fixture_actual_legal_moment (k : Nat) (hk : 0 < k) :
    randomizedLegalCombMoment fixtureN fixtureC fixtureH fixtureP fixtureR
      fixtureNu fixtureNaturalMasks 0 1 k = (1/2 : ℝ)^(k.choose 2) := by
  rw [actual_randomized_legal_moment fixtureN fixtureC fixtureH fixtureP fixtureR
    fixtureNu fixtureNaturalMasks 0 1 k hk]
  unfold finiteBankMoment
  simp_rw [fixture_masked_survival]
  rw [configurationBankPMF_sum]
  have hb : (∑ coin : CommonSeed fixtureN,
      ((originalRegisterMeasure fixtureN fixtureP).toPMF coin).toReal *
        (1/2 : ℝ)^(k.choose 2)) = (1/2 : ℝ)^(k.choose 2) := by
    rw [← Finset.sum_mul]
    have h := DotG4.ActualObservableBankCertificate.coinWeight_sum fixtureN fixtureP
    change (∑ coin : CommonSeed fixtureN,
      ((originalRegisterMeasure fixtureN fixtureP).toPMF coin).toReal) = 1 at h
    rw [h, one_mul]
  simp only [hb]
  simp [fixtureNu]

theorem fixture_actual_row_one :
    randomizedLegalCombMoment fixtureN fixtureC fixtureH fixtureP fixtureR
      fixtureNu fixtureNaturalMasks 0 1 1 = 1 := by
  have h := fixture_actual_legal_moment 1 (by decide)
  norm_num [Nat.choose] at h ⊢
  exact h

theorem fixture_actual_row_two :
    randomizedLegalCombMoment fixtureN fixtureC fixtureH fixtureP fixtureR
      fixtureNu fixtureNaturalMasks 0 1 2 = (1/2 : ℝ) := by
  have h := fixture_actual_legal_moment 2 (by decide)
  norm_num [Nat.choose] at h ⊢
  exact h

theorem fixture_actual_row_three :
    randomizedLegalCombMoment fixtureN fixtureC fixtureH fixtureP fixtureR
      fixtureNu fixtureNaturalMasks 0 1 3 = (1/8 : ℝ) := by
  have h := fixture_actual_legal_moment 3 (by decide)
  norm_num [Nat.choose] at h ⊢
  exact h

/-- Literal completed full-panel event, followed by the accepted passive pruning. -/
def fixtureRawCombProbability (k : Nat) : ℝ :=
  (((randomizedFullForestLaw fixtureN fixtureC fixtureH fixtureP fixtureR
    fixtureNu fixtureNaturalMasks (paddedSample k (0 : Fin 4) 1)).map
      (pruneForest (paddedKeep k)))
      {toUnranked (comb (paddedB (X := Fin 4) k).val
        ((paddedA k).map Subtype.val))}).toReal

theorem fixture_actual_raw_mass (k : Nat) (hk : 0 < k) :
    fixtureRawCombProbability k =
      DotG4.WholeProfileDetermination.combCoefficient k * (1/2 : ℝ)^(k.choose 2) := by
  have h := fixture_actual_legal_moment k hk
  change fixtureRawCombProbability k /
    DotG4.WholeProfileDetermination.combCoefficient k = (1/2 : ℝ)^(k.choose 2) at h
  have hm := (div_eq_iff (ne_of_gt
    (DotG4.WholeProfileDetermination.combCoefficient_pos k))).mp h
  simpa only [mul_comm] using hm

theorem fixture_actual_raw_one : fixtureRawCombProbability 1 = 1 := by
  have h := fixture_actual_raw_mass 1 (by decide)
  norm_num [DotG4.WholeProfileDetermination.combCoefficient, Nat.choose] at h ⊢
  exact h

theorem fixture_actual_raw_two : fixtureRawCombProbability 2 = (1/6 : ℝ) := by
  have h := fixture_actual_raw_mass 2 (by decide)
  norm_num [DotG4.WholeProfileDetermination.combCoefficient, Nat.choose] at h ⊢
  exact h

theorem fixture_actual_raw_three : fixtureRawCombProbability 3 = (1/144 : ℝ) := by
  have h := fixture_actual_raw_mass 3 (by decide)
  norm_num [DotG4.WholeProfileDetermination.combCoefficient, Nat.choose] at h ⊢
  exact h

#print axioms fixture_A_route
#print axioms fixture_selected_exposure_half
#print axioms fixture_actual_legal_moment
#print axioms fixture_actual_raw_mass

end
end DotG3.PhysicalFixture
