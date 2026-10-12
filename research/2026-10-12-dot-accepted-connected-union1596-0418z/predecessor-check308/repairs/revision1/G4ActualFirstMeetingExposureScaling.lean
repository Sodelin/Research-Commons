import G4ActualFirstMeetingCombMass
import ActualPopulationRate

/-!
# Same-bank cross-arity exposure at the original physical first meeting

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED draft.
The clock denominator is the accepted actual population choose-two law.
This consumer identifies the original repeated-copy populations along the
same fixed-register prefix, then accumulates their actual rates. It introduces
no bank resampling, independent-copy assumption or alternate cut. Strict
positive exposure and natural-bank averaging are separate obligations.
The inherited hand moment formula is reused; no novelty is claimed.
-/
namespace DotG4.ActualFirstMeetingExposureScaling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCompletionHarmonic UnifiedLean.Source.UnrankedGenealogyObservation
open DotG34.SpecifiedCombEvent
open GProgram.G5.SafePrefixRouteBridge
open DotG4.ActualBankFirstMeeting DotG34.ActualPopulationRate
open scoped Classical NNReal BigOperators
variable {V E X Copy Other : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [DecidableEq Other] [Fintype Other]

lemma fixed_boundary_live (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) :
    (state (fixedRegisterBoundary N b s)).live = (state s).live := by
  cases b <;> rfl

lemma fixed_prefix_live (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) :
    (state (fixedRegisterPrefix N ops s)).live = (state s).live := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | interval t => exact ih s
    | boundary b => exact (ih (fixedRegisterBoundary N b s)).trans (fixed_boundary_live N b s)

lemma initial_reference_live (N : RootedBinary V E X) (sample : Copy → X)
    (reg : V → Bool) (ops : List (ProgramStep N)) :
    (state (fixedRegisterPrefix N ops (initialCode N sample reg))).live = Finset.univ := by
  rw [fixed_prefix_live]
  rfl

/-- Only the A population has a possible pair; the separate B population is
one singleton. This is a finite-set calculation on the original state. -/
lemma repeated_population_choose (k : Nat) (s : State V E (Fin k ⊕ Unit))
    (a b place : Location V E) (hsep : a ≠ b)
    (hlive : s.live = Finset.univ)
    (ha : ∀ x : Fin k, s.location (Sum.inl x) = a)
    (hb : s.location (Sum.inr ()) = b) :
    (populationRoots s place).card.choose 2 = if a = place then k.choose 2 else 0 := by
  by_cases hap : a = place
  · have hbp : b ≠ place := by intro h; exact hsep (hap.trans h.symm)
    have he : populationRoots s place = (Finset.univ : Finset (Fin k)).image Sum.inl := by
      ext x
      cases x with
      | inl x => simp [populationRoots,hlive,ha,hap]
      | inr x => cases x; simp [populationRoots,hlive,hb,hbp]
    rw [he,Finset.card_image_of_injective _ Sum.inl_injective,Finset.card_univ]
    simp [hap]
  · by_cases hbp : b = place
    · have he : populationRoots s place = {Sum.inr ()} := by
        ext x
        cases x with
        | inl x => simp [populationRoots,hlive,ha,hap]
        | inr x => cases x; simp [populationRoots,hlive,hb,hbp]
      simp [he,hap]
    · have he : populationRoots s place = ∅ := by
        ext x
        cases x with
        | inl x => simp [populationRoots,hlive,ha,hap]
        | inr x => cases x; simp [populationRoots,hlive,hb,hbp]
      simp [he,hap]

lemma repeated_actual_rate (N : RootedBinary V E X) (r : PositivePairRates E)
    (k : Nat) {sample : Fin k ⊕ Unit → X} (s : Code N sample)
    (a b : Location V E) (hsep : a ≠ b)
    (hlive : (state s).live = Finset.univ)
    (ha : ∀ x : Fin k, (state s).location (Sum.inl x) = a)
    (hb : (state s).location (Sum.inr ()) = b) :
    totalRate N r s = (k.choose 2 : ℝ) *
      ∑ i : Option E, if a = originalPlace N i then pairRate r i else 0 := by
  rw [actual_rate_choose_two,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [repeated_population_choose k (state s) a b (originalPlace N i) hsep hlive ha hb]
  by_cases h : a = originalPlace N i
  · simp only [if_pos h]
    exact mul_comm _ _
  · simp [h]

/-- Rates are compared in the same original bank and literal pair-derived
prefix. This also retains the zero-A and one-A controls. -/
theorem actual_prefix_rate_cross_arity (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (k q : Nat) (hq : q < bankFirstMeetingIndex N C H gamma r coin i j) :
    totalRate N r (fixedRegisterPrefix N
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take q)
      (initialCode N (repeatedSample k i j) (originalRegister N coin))) =
    (k.choose 2 : ℝ) * totalRate N r (fixedRegisterPrefix N
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take q)
      (initialCode N (repeatedSample 2 i j) (originalRegister N coin))) := by
  let P := (compiledCalendarProgram N C H gamma (fun _ => true)).take q
  let a := copyLocation (state (pairReference N C H gamma coin i j q)) true
  let b := copyLocation (state (pairReference N C H gamma coin i j q)) false
  have hsep : a ≠ b := before_bankFirstMeeting_separated N C H gamma r coin i j q hq
  have hrate (n : Nat) :
      totalRate N r (fixedRegisterPrefix N P
        (initialCode N (repeatedSample n i j) (originalRegister N coin))) =
      (n.choose 2 : ℝ) * ∑ e : Option E, if a = originalPlace N e then pairRate r e else 0 := by
    let s := fixedRegisterPrefix N P
      (initialCode N (repeatedSample n i j) (originalRegister N coin))
    have hl : (state s).live = Finset.univ := initial_reference_live N _ _ P
    have hanc (x : Fin n ⊕ Unit) : (state s).ancestor x = x :=
      s.property.forest.representative x (by rw [hl]; exact Finset.mem_univ x)
    apply repeated_actual_rate N r n s a b hsep hl
    · intro x
      have h := initial_reference_location_cross_carrier N (repeatedSample n i j)
        (pairSample i j) (originalRegister N coin) P (Sum.inl x) true (by simp [repeatedSample,pairSample])
      change copyLocation (state s) (Sum.inl x) = a at h
      simpa only [copyLocation,hanc] using h
    · have h := initial_reference_location_cross_carrier N (repeatedSample n i j)
        (pairSample i j) (originalRegister N coin) P (Sum.inr ()) false (by simp [repeatedSample,pairSample])
      change copyLocation (state s) (Sum.inr ()) = b at h
      simpa only [copyLocation,hanc] using h
  change totalRate N r (fixedRegisterPrefix N P _) = _
  rw [hrate k,hrate 2]
  norm_num

/-- Accumulate a pointwise comparison of actual deterministic-prefix rates.
Both carriers use the same literal operation word and interval durations. -/
lemma reference_exposure_scale_of_prefix_rates (N : RootedBinary V E X)
    {sample : Copy → X} {sample' : Other → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (s : Code N sample) (z : Code N sample') (c : ℝ)
    (hr : ∀ q < ops.length,
      totalRate N r (fixedRegisterPrefix N (ops.take q) s) =
        c * totalRate N r (fixedRegisterPrefix N (ops.take q) z)) :
    referenceExposure N r ops s = c * referenceExposure N r ops z := by
  induction ops generalizing s z with
  | nil => simp [referenceExposure]
  | cons op ops ih =>
    cases op with
    | interval t =>
      have h0 := hr 0 (by simp)
      simp only [List.take_zero,fixedRegisterPrefix] at h0
      have ht : ∀ q < ops.length,
          totalRate N r (fixedRegisterPrefix N (ops.take q) s) =
            c * totalRate N r (fixedRegisterPrefix N (ops.take q) z) := by
        intro q hq
        have h := hr (q+1) (by simpa using Nat.succ_lt_succ hq)
        simpa only [List.take_succ_cons,fixedRegisterPrefix] using h
      simp only [referenceExposure]
      rw [h0,ih s z ht]
      ring
    | boundary b =>
      apply ih (fixedRegisterBoundary N b s) (fixedRegisterBoundary N b z)
      intro q hq
      have h := hr (q+1) (by simpa using Nat.succ_lt_succ hq)
      simpa only [List.take_succ_cons,fixedRegisterPrefix] using h

/-- The actual k-copy exposure is the same bank's two-A exposure scaled by
choose(k,2), at the same constructed physical operation-index cut. -/
theorem actual_first_meeting_exposure_cross_arity (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) (k : Nat) :
    referenceExposure N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N (repeatedSample k i j) (originalRegister N coin)) =
    (k.choose 2 : ℝ) * referenceExposure N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N (repeatedSample 2 i j) (originalRegister N coin)) := by
  apply reference_exposure_scale_of_prefix_rates
  intro q hq
  have hm : q < bankFirstMeetingIndex N C H gamma r coin i j :=
    lt_of_lt_of_le hq (List.length_take_le _ _)
  have ht : (((compiledCalendarProgram N C H gamma (fun _ => true)).take
      (bankFirstMeetingIndex N C H gamma r coin i j)).take q) =
      (compiledCalendarProgram N C H gamma (fun _ => true)).take q := by
    rw [List.take_take,Nat.min_eq_left (Nat.le_of_lt hm)]
  rw [ht]
  exact actual_prefix_rate_cross_arity N C H gamma r coin i j k q hm

/-- Original fixed-bank completed specified-comb mass with one common
bank-dependent exposure coordinate for every labelled repeated-copy arity. -/
theorem actual_fixed_bank_completed_comb_scaled_mass (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) (k : Nat)
    (as : List (Fin k ⊕ Unit))
    (hcover : ∀ x, x = Sum.inr () ∨ x ∈ as) (hnodup : as.Nodup)
    (hb : Sum.inr () ∉ as) (hnonempty : as ≠ []) :
    (((sourceProgram N r (compiledCalendarProgram N C H gamma (fun _ => true))
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).bind
      (completionKernel N r)).map (fun d => sourceUnrankedForest (state d) Finset.univ))
      {toUnranked (comb (Sum.inr ()) as)} =
    ENNReal.ofReal (2^as.length /
      ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) *
      ENNReal.ofReal (Real.exp (-((k.choose 2 : ℝ) * referenceExposure N r
        ((compiledCalendarProgram N C H gamma (fun _ => true)).take
          (bankFirstMeetingIndex N C H gamma r coin i j))
        (initialCode N (repeatedSample 2 i j) (originalRegister N coin))))) := by
  rw [DotG4.ActualFirstMeetingCombMass.actual_fixed_bank_completed_comb_mass
    N C H gamma r coin i j k as hcover hnodup hb hnonempty]
  rw [actual_first_meeting_exposure_cross_arity N C H gamma r coin i j k]

#print axioms actual_fixed_bank_completed_comb_scaled_mass
#print axioms actual_prefix_rate_cross_arity
#print axioms actual_first_meeting_exposure_cross_arity
end DotG4.ActualFirstMeetingExposureScaling
