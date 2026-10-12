import G4ActualFirstMeetingExposureScaling
import UnifiedLean.Source.SourceCompletedUnrankedTree

/-!
# Original once-drawn COMMON-bank comb moments

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED draft.
This composes the checked fixed-bank full-calendar mass and same-bank scaling
with the existing natural completed observation. The COMMON prior is exactly
(originalRegisterMeasure N p).toPMF on Hybrid N → Bool, not the independently
indexed NativeCoinSeed carrier. No conditioned-cut prior is substituted.
The survival coordinate is proved positive and at most one; strictly positive
exposure for distinct taxa, larger-panel acquisition and general G4 closure
remain separate. The arbitrary-k hand moment formula is inherited work.
-/
namespace DotG4.ActualNaturalCombMoments
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G5.SafePrefixRouteBridge
open DotG34.SpecifiedCombEvent DotG4.ActualBankFirstMeeting
open DotG4.ActualFirstMeetingExposureScaling
open scoped Classical NNReal ENNReal BigOperators
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma reference_exposure_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    0 ≤ referenceExposure N r ops s := by
  induction ops generalizing s with
  | nil => exact le_refl _
  | cons op ops ih =>
    cases op with
    | interval t =>
      exact add_nonneg (mul_nonneg (totalRate_nonnegative N r s) t.property) (ih s)
    | boundary b => exact ih (fixedRegisterBoundary N b s)

/-- One original-bank coordinate, independent of the repeated-panel arity.
Its exposure carrier has two A copies and one B; the cut has one A and one B. -/
noncomputable def bankSurvival (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-bankExclusiveExposure N C H (originalGamma p) r coin i j))

lemma bankSurvival_positive (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) :
    0 < bankSurvival N C H p r coin i j :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos _)

lemma bankSurvival_le_one (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) :
    bankSurvival N C H p r coin i j ≤ 1 := by
  apply ENNReal.ofReal_le_one.mpr
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (reference_exposure_nonnegative N r _ _)

/-- Canonical ordered A labels; no enumeration hypothesis is left to the
consumer of the natural all-level moment identity. -/
def canonicalA (k : Nat) : List (Fin k ⊕ Unit) := (List.finRange k).map Sum.inl

lemma canonicalA_cover (k : Nat) (x : Fin k ⊕ Unit) :
    x = Sum.inr () ∨ x ∈ canonicalA k := by
  cases x with
  | inl x => exact Or.inr (List.mem_map.mpr ⟨x,List.mem_finRange x,rfl⟩)
  | inr x => cases x; exact Or.inl rfl

lemma canonicalA_nodup (k : Nat) : (canonicalA k).Nodup :=
  (List.nodup_finRange k).map Sum.inl_injective

lemma canonicalA_excludes_B (k : Nat) : Sum.inr () ∉ canonicalA k := by
  simp [canonicalA]

lemma canonicalA_nonempty (k : Nat) (hk : 0 < k) : canonicalA k ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [canonicalA,List.length_map,List.length_finRange,List.length_nil] at hl
  omega

/-- The original full-calendar fixed-bank probability, with explicit
canonical labels, is coefficient times a power of the same bank coordinate. -/
theorem actual_fixed_bank_canonical_comb_power (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (k : Nat) (hk : 0 < k) :
    (((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => true))
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).bind
      (completionKernel N r)).map (fun d => sourceUnrankedForest (state d) Finset.univ))
      {toUnranked (comb (Sum.inr ()) (canonicalA k))} =
    ENNReal.ofReal (2^k / ((Nat.factorial (k+1) : ℝ) * (Nat.factorial k : ℝ))) *
      (bankSurvival N C H p r coin i j)^(k.choose 2) := by
  have h := actual_fixed_bank_completed_comb_scaled_mass N C H (originalGamma p) r coin i j k
    (canonicalA k) (canonicalA_cover k) (canonicalA_nodup k) (canonicalA_excludes_B k)
    (canonicalA_nonempty k hk)
  have hlen : (canonicalA k).length = k := by simp [canonicalA]
  rw [hlen] at h
  rw [h]
  congr 1
  unfold bankSurvival bankExclusiveExposure
  rw [show -((k.choose 2 : ℝ) * referenceExposure N r
      ((compiledCalendarProgram N C H (originalGamma p) (fun _ => true)).take
        (bankFirstMeetingIndex N C H (originalGamma p) r coin i j))
      (initialCode N (repeatedSample 2 i j) (originalRegister N coin))) =
      (k.choose 2 : ℝ) * (-referenceExposure N r
      ((compiledCalendarProgram N C H (originalGamma p) (fun _ => true)).take
        (bankFirstMeetingIndex N C H (originalGamma p) r coin i j))
      (initialCode N (repeatedSample 2 i j) (originalRegister N coin))) by ring,
    Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le]

/-- Actual passive completed-topology mass is one average over the ORIGINAL
once-drawn COMMON bank, simultaneously for every positive repeated-copy arity.
The sum uses the full prior, never a refitted or conditioned interior law. -/
theorem actual_natural_completed_comb_moment (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (i j : X) (k : Nat) (hk : 0 < k) :
    naturalCompletedUnrankedLaw N C (repeatedSample k i j) H p (fun _ => true) r
      {toUnranked (comb (Sum.inr ()) (canonicalA k))} =
    ENNReal.ofReal (2^k / ((Nat.factorial (k+1) : ℝ) * (Nat.factorial k : ℝ))) *
      ∑' coin : Hybrid N → Bool, (originalRegisterMeasure N p).toPMF coin *
        (bankSurvival N C H p r coin i j)^(k.choose 2) := by
  rw [naturalCompletedUnrankedLaw,naturalCompletedLaw,naturalCalendarLaw,
    originalRegisterPMF,PMF.bind_map,PMF.bind_bind,PMF.map_bind,PMF.bind_apply,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro coin
  simp only [Function.comp_apply]
  have h := actual_fixed_bank_canonical_comb_power N C H p r coin i j k hk
  change (((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => true))
    (initialCode N (repeatedSample k i j) (originalRegister N coin))).bind
    (ancestralCompletion N r (Fintype.card (Fin k ⊕ Unit)))).map
    (fun d => sourceUnrankedForest (state d) Finset.univ))
    {toUnranked (comb (Sum.inr ()) (canonicalA k))} =
    ENNReal.ofReal (2^k / ((Nat.factorial (k+1) : ℝ) * (Nat.factorial k : ℝ))) *
      (bankSurvival N C H p r coin i j)^(k.choose 2) at h
  rw [h]
  ac_rfl

/-- Finite original-bank version of the same moment identity. -/
theorem actual_natural_completed_comb_finite_moment (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (i j : X) (k : Nat) (hk : 0 < k) :
    naturalCompletedUnrankedLaw N C (repeatedSample k i j) H p (fun _ => true) r
      {toUnranked (comb (Sum.inr ()) (canonicalA k))} =
    ENNReal.ofReal (2^k / ((Nat.factorial (k+1) : ℝ) * (Nat.factorial k : ℝ))) *
      ∑ coin : Hybrid N → Bool, (originalRegisterMeasure N p).toPMF coin *
        (bankSurvival N C H p r coin i j)^(k.choose 2) := by
  simpa only [tsum_fintype] using actual_natural_completed_comb_moment N C H p r i j k hk

#print axioms bankSurvival_positive
#print axioms bankSurvival_le_one
#print axioms actual_natural_completed_comb_moment
end DotG4.ActualNaturalCombMoments
