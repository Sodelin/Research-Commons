import ResearchCommons.MSCI.JC69CommonCountIndex

/-! Actual complete-root canonical ratio paths. UNCOMPILED candidate,
dot (OpenAI), 31 October 2026. Terminal stop is one, nonterminal stop zero;
no stop evaluates a denominator. This is not whole-calendar composition. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69RootCanonicalRatios
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceAncestralCompletion
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69RootResolvent
open ResearchCommons.MSCI.JC69OrderedPathExpansion ResearchCommons.MSCI.JC69UnorderedContinuation
open ResearchCommons.MSCI.JC69CanonicalPathCount ResearchCommons.MSCI.JC69CanonicalWeightedSum
open ResearchCommons.MSCI.JC69CommonCountIndex
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Product of ORIGINAL unordered pair-rate/actual killed-rate ratios.
Only a real Choice introduces a factor; stop contributes the empty product. -/
def rootRatioProduct (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base) :
    (fuel : ℕ) → (s : Code N sample) → OrderedPath N fuel s → ℝ
  | 0, _, _ => 1
  | _+1, _, .inl _ => 1
  | fuel+1, s, .inr ⟨p,h⟩ =>
      (pairRate r p.1 / holdingRate N r L q s) *
        rootRatioProduct N r L q fuel (stepDestination N s (some p)) h

/-- Keep exactly terminal paths, including an already-terminal empty path. -/
def rootCoefficient (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (h : OrderedPath N fuel s) : ℝ :=
  rootRatioProduct N r L q fuel s h *
    (if liveCard (pathEnd N fuel s h) ≤ 1 then 1 else 0)

lemma actual_root_ratio_nonneg (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (h : OrderedPath N fuel s) :
    0 ≤ rootRatioProduct N r L q fuel s h := by
  induction fuel generalizing s with
  | zero => simp [rootRatioProduct]
  | succ fuel ih =>
    cases h with
    | inl h => simp [rootRatioProduct]
    | inr h =>
      obtain ⟨p,h⟩ := h
      exact mul_nonneg (div_nonneg (le_of_lt (pairRate_pos r p.1))
        (le_of_lt (actual_choice_killed_positive N r L q s p))) (ih _ h)

lemma rootCoefficient_nonneg (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (h : OrderedPath N fuel s) :
    0 ≤ rootCoefficient N r L q fuel s h := by
  unfold rootCoefficient
  apply mul_nonneg (actual_root_ratio_nonneg N r L q fuel s h)
  split_ifs <;> norm_num

lemma rootCoefficient_stop {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) :
    rootCoefficient N r L q (fuel+1) s (canonicalStop e N fuel s).val =
      if liveCard s ≤ 1 then 1 else 0 := by
  simp [rootCoefficient,rootRatioProduct,canonicalStop,pathEnd]

lemma rootCoefficient_jump {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (p : CanonicalChoice e N s)
    (h : CanonicalPath e N fuel (stepDestination N s (some p.val))) :
    rootCoefficient N r L q (fuel+1) s (canonicalJump e N fuel s p h).val =
      (pairRate r p.val.1 / holdingRate N r L q s) *
        rootCoefficient N r L q fuel (stepDestination N s (some p.val)) h.val := by
  simp [rootCoefficient,rootRatioProduct,canonicalJump,pathEnd,mul_assoc]

lemma sum_canonical_path_succ_ennreal {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (fuel : ℕ) (s : Code N sample)
    (f : CanonicalPath e N (fuel+1) s → ℝ≥0∞) :
    (∑ h, f h) = f (canonicalStop e N fuel s) +
      ∑ p : CanonicalChoice e N s,
        ∑ h : CanonicalPath e N fuel (stepDestination N s (some p.val)),
          f (canonicalJump e N fuel s p h) := by
  rw [← (canonicalPathSuccEquiv e N fuel s).symm.sum_comp f]
  simp [Fintype.sum_sum_type,Fintype.sum_sigma,canonicalPathSuccEquiv]

/-- Finite ratio expansion of the ACTUAL complete-root expectation. The
adequate budget is derived at each actual destination by exact live-card descent. -/
theorem actual_root_canonical_ratio_sum [Nonempty Copy] {n : ℕ}
    (e : Copy ≃ Fin n) (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (fuel : ℕ) (s : Code N sample)
    (hs : AncestralRoot N s) (hbudget : liveCard s ≤ fuel+1) :
    rootWeight N r L q s = ∑ h : CanonicalPath e N fuel s,
      ENNReal.ofReal (rootCoefficient N r L q fuel s h.val) := by
  induction fuel generalizing s with
  | zero =>
      have ht : liveCard s ≤ 1 := by simpa using hbudget
      rw [actual_terminal_root_weight N r L q s ht]
      simp [CanonicalPath,CanonicalPathPred,OrderedPath,rootCoefficient,rootRatioProduct,pathEnd,ht]
  | succ fuel ih =>
      rw [sum_canonical_path_succ_ennreal,rootCoefficient_stop]
      by_cases ht : liveCard s ≤ 1
      · letI := choice_empty_of_terminal_card N s ht
        rw [actual_terminal_root_weight N r L q s ht]
        simp [ht,CanonicalChoice]
      · have hg : 1 < liveCard s := lt_of_not_ge ht
        rw [actual_root_resolvent N r L q hbal s hs hg]
        simp only [ht,ite_false,ENNReal.ofReal_zero,zero_add]
        change (∑ p : Choice N s,
          ENNReal.ofReal (choiceRate N r s p/holdingRate N r L q s) *
            rootWeight N r L q (stepDestination N s (some p))) = _
        rw [sum_choice_orientations e N s]
        apply Finset.sum_congr rfl
        intro p _
        rw [actual_orientation_root_summand_sum N r L q hbal s hs p.val]
        have hd := merger_destination_card N s p.val
        have hb : liveCard (stepDestination N s (some p.val)) ≤ fuel+1 := by omega
        rw [ih _ (ancestral_merger_preserved N s hs p.val) hb,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        rw [rootCoefficient_jump]
        exact (ENNReal.ofReal_mul (div_nonneg (le_of_lt (pairRate_pos r p.val.1))
          (le_of_lt (actual_choice_killed_positive N r L q s p.val)))).symm

/-- Genuine real coefficients for subsequent denominator algebra; finiteness
is supplied by the finite sum of ofReal terms, not an assumed root integrability. -/
theorem actual_root_canonical_real_sum [Nonempty Copy] {n : ℕ}
    (e : Copy ≃ Fin n) (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (fuel : ℕ) (s : Code N sample)
    (hs : AncestralRoot N s) (hbudget : liveCard s ≤ fuel+1) :
    (rootWeight N r L q s).toReal = ∑ h : CanonicalPath e N fuel s,
      rootCoefficient N r L q fuel s h.val := by
  rw [actual_root_canonical_ratio_sum e N r L q hbal fuel s hs hbudget]
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro h _
  exact ENNReal.toReal_ofReal (rootCoefficient_nonneg N r L q fuel s h.val)

/-- Source-fixed root representation with at most E terms, independent of
site counts/characters. Original Copy is not replicated. No terminal 0/0. -/
theorem actual_root_ratio_representation [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (s : Code N sample) (hs : AncestralRoot N s) :
    (rootWeight N r L q s).toReal =
        ∑ h : CanonicalPath e N (Fintype.card Copy) s,
          rootCoefficient N r L q (Fintype.card Copy) s h.val ∧
      Fintype.card (CanonicalPath e N (Fintype.card Copy) s) ≤
        ∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k := by
  constructor
  · apply actual_root_canonical_real_sum e N r L q hbal _ s hs
    have hc : liveCard s ≤ Fintype.card Copy := Finset.card_le_univ s.val.live
    omega
  · exact actual_canonical_path_card_le e N _ s

/-- Replication of already balanced original-copy characters retains the
actual complete-root balance premise; it is not a replacement scalar source. -/
theorem replicated_character_balance {A : Type*} [Fintype A]
    (v : A → ℕ) (chi : A → Copy → Base) (hchi : ∀ a, ∑ x, chi a x = 0) :
    ∀ j, ∑ x, replicatedQ v chi j x = 0 := by
  intro j
  exact hchi ((replicaEquiv v j).1)

#print axioms actual_root_ratio_nonneg
#print axioms actual_root_canonical_ratio_sum
#print axioms actual_root_canonical_real_sum
#print axioms actual_root_ratio_representation
#print axioms replicated_character_balance
end ResearchCommons.MSCI.JC69RootCanonicalRatios
