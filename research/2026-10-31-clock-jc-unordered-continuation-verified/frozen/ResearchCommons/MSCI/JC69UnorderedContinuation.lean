import ResearchCommons.MSCI.JC69OrderedPathExpansion

/-! Actual orientation and complete-root continuation interface.
UNCOMPILED, dot (OpenAI), 31 October 2026. Original ordered source choices
are reversed, not replaced. Pairing is justified by full weighted future
readout equality, not just endpoint equality. No canonical path-count,
calendar or full finite-window theorem is asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69UnorderedContinuation
open MeasureTheory Set Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.LiteralMarkedClockTrace
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69CurrentPartition
open ResearchCommons.MSCI.JC69SourceRootQuotient ResearchCommons.MSCI.JC69EndpointWeight
open ResearchCommons.MSCI.JC69EndpointQuotient ResearchCommons.MSCI.JC69WeightedTrace
open ResearchCommons.MSCI.JC69RootResolvent ResearchCommons.MSCI.JC69OrderedPathExpansion
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Reverse the two ACTUAL original roots in their unchanged population. -/
def reverseChoice (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) : Choice N s :=
  ⟨p.1, ⟨(p.2.val.2,p.2.val.1), by
    obtain ⟨ha,hb,hab⟩ := Finset.mem_offDiag.mp p.2.property
    exact Finset.mem_offDiag.mpr ⟨hb,ha,hab.symm⟩⟩⟩

lemma reverseChoice_involutive (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Function.Involutive (reverseChoice N s) := by
  intro p
  rcases p with ⟨i,⟨⟨a,b⟩,hp⟩⟩
  rfl

lemma reverseChoice_ne (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) : reverseChoice N s p ≠ p := by
  intro he
  have hab := (Finset.mem_offDiag.mp p.2.property).2.2
  have h := congrArg (fun z : Choice N s => z.2.val.1) he
  exact hab h.symm

lemma reverseChoice_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    choiceRate N r s (reverseChoice N s p) = choiceRate N r s p := rfl

/-- The ORIGINAL unordered rate, with no change to total holding rate. -/
theorem actual_orientation_rate_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    choiceRate N r s p + choiceRate N r s (reverseChoice N s p) = pairRate r p.1 := by
  rw [reverseChoice_rate]
  unfold choiceRate
  ring

/-- Coding does not erase the already-proved raw orientation symmetry. -/
theorem actual_orientation_destination_observation (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s) :
    observeCode N (stepDestination N s (some p)) =
      observeCode N (stepDestination N s (some (reverseChoice N s p))) := by
  apply Prod.ext
  · change currentBlocks (state (stepDestination N s (some p))) =
      currentBlocks (state (stepDestination N s (some (reverseChoice N s p))))
    rw [actual_coded_merge_blocks,actual_coded_merge_blocks]
    exact actual_merge_orientation_blocks (state s) s.property.forest
      (population_pair_is_source_legal _ _ (originalPlace_not_node N p.1) p.2.property)
  · funext x
    exact (actual_coded_merge_copyLocation N s p x).trans
      (actual_coded_merge_copyLocation N s (reverseChoice N s p) x).symm

/-- Whole SAME-target finite-fuel continuation, not raw trace equality. -/
theorem actual_orientation_resolved_continuation (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (p : Choice N s) (T : ℝ≥0)
    (target : BlockPopulationObservation Copy V E) :
    actualResolvedWeight N r L q n (stepDestination N s (some p)) T target =
      actualResolvedWeight N r L q n (stepDestination N s (some (reverseChoice N s p))) T target :=
  actual_resolved_weight_quotient N r L q n _ _ T target
    (actual_orientation_destination_observation N s p)

/-- Pointwise pairing on the actual renewal's [0,T] domain. Its inherited
Bochner integrability is supplied by the accepted real-source bridge. -/
theorem actual_orientation_real_integrand_sum (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (p : Choice N s) (T : ℝ≥0)
    (target : BlockPopulationObservation Copy V E) (u : ℝ) (hu : u ∈ Icc 0 (T:ℝ)) :
    choiceRate N r s p * Real.exp (-holdingRate N r L q s*u) *
        (actualResolvedWeight N r L q n (stepDestination N s (some p)) ((T:ℝ)-u) target).toReal +
      choiceRate N r s (reverseChoice N s p) * Real.exp (-holdingRate N r L q s*u) *
        (actualResolvedWeight N r L q n (stepDestination N s (some (reverseChoice N s p))) ((T:ℝ)-u) target).toReal =
      pairRate r p.1 * Real.exp (-holdingRate N r L q s*u) *
        (actualResolvedWeight N r L q n (stepDestination N s (some p)) ((T:ℝ)-u) target).toReal := by
  have h := actual_orientation_resolved_continuation N r L q n s p
    (⟨(T:ℝ)-u,sub_nonneg.mpr hu.2⟩ : ℝ≥0) target
  change actualResolvedWeight N r L q n (stepDestination N s (some p)) ((T:ℝ)-u) target = _ at h
  rw [← h,reverseChoice_rate]
  unfold choiceRate
  ring

lemma observation_liveCard_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s t : Code N sample) (hobs : observeCode N s = observeCode N t) : liveCard s = liveCard t := by
  have hB : currentBlocks (state s) = currentBlocks (state t) := congrArg Prod.fst hobs
  have h := Fintype.card_congr (liveRootEquiv (state s) (state t) s.property.forest t.property.forest hB)
  simpa only [LiveRoot,Fintype.card_coe] using h

lemma observation_ancestralRoot (N : RootedBinary V E X) {sample : Copy → X}
    (s t : Code N sample) (hobs : observeCode N s = observeCode N t)
    (hs : AncestralRoot N s) : AncestralRoot N t := by
  intro x
  have h := congrFun (congrArg Prod.snd hobs) x
  exact h.symm.trans (hs x)

/-- Actual COMPLETE root readout factors through the same observation.
This follows from the accepted root equation by decreasing live-card induction,
not by assuming an infinite continuation equality from a finite endpoint law.
The SAME original copy/site balance is retained at every destination. -/
theorem actual_root_weight_observation [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (s t : Code N sample)
    (hobs : observeCode N s = observeCode N t) (hs : AncestralRoot N s) :
    rootWeight N r L q s = rootWeight N r L q t := by
  suffices H : ∀ k, ∀ s t : Code N sample, liveCard s = k →
      observeCode N s = observeCode N t → AncestralRoot N s →
      rootWeight N r L q s = rootWeight N r L q t by
    exact H _ s t rfl hobs hs
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro s t hk hobs hs
      have hc := observation_liveCard_eq N s t hobs
      have ht := observation_ancestralRoot N s t hobs hs
      by_cases hterm : liveCard s ≤ 1
      · rw [actual_terminal_root_weight N r L q s hterm,
          actual_terminal_root_weight N r L q t (by omega)]
      · have hgt : 1 < liveCard s := lt_of_not_ge hterm
        have hgt' : 1 < liveCard t := by omega
        have hB : currentBlocks (state s) = currentBlocks (state t) := congrArg Prod.fst hobs
        have hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x :=
          fun x => congrFun (congrArg Prod.snd hobs) x
        let e := actualChoiceEquiv N s t hB hLoc
        rw [actual_root_resolvent N r L q hbal s hs hgt,
          actual_root_resolvent N r L q hbal t ht hgt']
        rw [← e.sum_comp (fun p : Choice N t =>
          ENNReal.ofReal (choiceRate N r t p/(totalRate N r t+locusKill N L q t)) *
            rootWeight N r L q (stepDestination N t (some p)))]
        apply Finset.sum_congr rfl
        intro p _
        have hR := actualChoiceEquiv_rate N r s t hB hLoc p
        have hC := actual_totalRate_eq N r s t hB hLoc
        have hK := actual_locusKill_eq N L q s t hB
        have hd := merger_destination_card N s p
        have ho := actual_matched_destinations_observation N s t hB hLoc p
        have ha := ancestral_merger_preserved N s hs p
        have hi := ih (liveCard (stepDestination N s (some p))) (by omega)
          (stepDestination N s (some p)) (stepDestination N t (some (e p))) rfl ho ha
        rw [hR,hC,hK,hi]

/-- Root orientations agree in COMPLETE weighted future, with balance and
ancestry retained. Terminal stopped weight1 is not an unbalanced limit claim. -/
theorem actual_orientation_root_continuation [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (s : Code N sample) (hs : AncestralRoot N s)
    (p : Choice N s) :
    rootWeight N r L q (stepDestination N s (some p)) =
      rootWeight N r L q (stepDestination N s (some (reverseChoice N s p))) :=
  actual_root_weight_observation N r L q hbal _ _
    (actual_orientation_destination_observation N s p) (ancestral_merger_preserved N s hs p)

/-- Actual root-resolvent summands combine to the ORIGINAL unordered rate.
This theorem has a Choice premise and therefore never divides terminal0/0. -/
theorem actual_orientation_root_summand_sum [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (s : Code N sample) (hs : AncestralRoot N s)
    (p : Choice N s) :
    ENNReal.ofReal (choiceRate N r s p/holdingRate N r L q s) *
        rootWeight N r L q (stepDestination N s (some p)) +
      ENNReal.ofReal (choiceRate N r s (reverseChoice N s p)/holdingRate N r L q s) *
        rootWeight N r L q (stepDestination N s (some (reverseChoice N s p))) =
      ENNReal.ofReal (pairRate r p.1/holdingRate N r L q s) *
        rootWeight N r L q (stepDestination N s (some p)) := by
  rw [← actual_orientation_root_continuation N r L q hbal s hs p,reverseChoice_rate,← add_mul]
  have hd : 0 < holdingRate N r L q s := actual_choice_killed_positive N r L q s p
  have hn : 0 ≤ choiceRate N r s p/holdingRate N r L q s :=
    div_nonneg (le_of_lt (actual_choiceRate_positive N r s p)) (le_of_lt hd)
  rw [← ENNReal.ofReal_add hn hn]
  congr 2
  unfold choiceRate
  ring

#print axioms actual_orientation_rate_sum
#print axioms actual_orientation_destination_observation
#print axioms actual_orientation_resolved_continuation
#print axioms actual_orientation_real_integrand_sum
#print axioms actual_root_weight_observation
#print axioms actual_orientation_root_continuation
#print axioms actual_orientation_root_summand_sum
end ResearchCommons.MSCI.JC69UnorderedContinuation
