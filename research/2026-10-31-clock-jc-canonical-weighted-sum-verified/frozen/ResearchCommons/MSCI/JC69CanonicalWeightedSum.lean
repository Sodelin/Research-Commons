import ResearchCommons.MSCI.JC69CanonicalPathCount

/-! Actual canonical weighted-source sum and the single-epoch nE bound.
UNCOMPILED, dot (OpenAI), 31 October 2026. The two orientation integrands
are combined through accepted full continuation equality. Stop/no-event is
never doubled. No full-calendar M or count-polynomial representation assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69CanonicalWeightedSum
open MeasureTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69WeightedTrace
open ResearchCommons.MSCI.JC69EndpointWeight ResearchCommons.MSCI.JC69ResolvedRealVolterra
open ResearchCommons.MSCI.JC69OrderedPathExpansion ResearchCommons.MSCI.JC69UnorderedContinuation
open ResearchCommons.MSCI.JC69CanonicalPathCount
open scoped Classical BigOperators NNReal ENNReal Interval
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- A genuine source Choice equivalence, not division of a cardinality. -/
def choiceOrientationEquiv {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) : Choice N s ≃ CanonicalChoice e N s × Bool where
  toFun p := if h : IsCanonical e N s p then (⟨p,h⟩,true)
    else (⟨reverseChoice N s p,(canonical_reverse_iff e N s p).mpr h⟩,false)
  invFun z := if z.2 then z.1.val else reverseChoice N s z.1.val
  left_inv p := by
    by_cases h : IsCanonical e N s p <;> simp [h,reverseChoice_involutive]
  right_inv z := by
    rcases z with ⟨⟨p,hp⟩,b⟩
    cases b <;> simp [hp,canonical_reverse_iff,reverseChoice_involutive]

lemma sum_choice_orientations {A : Type*} [AddCommMonoid A] {n : ℕ}
    (e : Copy ≃ Fin n) (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (f : Choice N s → A) :
    (∑ p, f p) = ∑ p : CanonicalChoice e N s, (f p.val + f (reverseChoice N s p.val)) := by
  rw [← (choiceOrientationEquiv e N s).symm.sum_comp f]
  simp [Fintype.sum_prod_type,Fintype.sum_bool,choiceOrientationEquiv]

/-- Actual real renewal with ORIGINAL unordered pair rates. The same final
target and decremented fuel remain attached to each actual destination. -/
theorem actual_resolved_canonical_real_renewal {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (T : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    (actualResolvedWeight N r L q (fuel+1) s T target).toReal =
      Real.exp (-holdingRate N r L q s*(T:ℝ)) * (if observeCode N s = target then 1 else 0) +
      ∑ p : CanonicalChoice e N s, ∫ u in Icc (0:ℝ) (T:ℝ),
        pairRate r p.val.1 * Real.exp (-holdingRate N r L q s*u) *
          (actualResolvedWeight N r L q fuel (stepDestination N s (some p.val)) ((T:ℝ)-u) target).toReal := by
  rw [actual_resolved_real_renewal]
  apply congrArg₂ (· + ·)
  · simp only [holdingRate,neg_mul]
  · rw [sum_choice_orientations e N s]
    apply Finset.sum_congr rfl
    intro p _
    have h1 := actual_resolved_real_branch_integrable N r L q fuel s T target p.val
    have h2 := actual_resolved_real_branch_integrable N r L q fuel s T target (reverseChoice N s p.val)
    rw [← integral_add h1 h2]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    simpa only [holdingRate,neg_mul] using
      actual_orientation_real_integrand_sum N r L q fuel s p.val T target u hu

def canonicalStop {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) : CanonicalPath e N (fuel+1) s :=
  ⟨.inl PUnit.unit,True.intro⟩

def canonicalJump {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) (p : CanonicalChoice e N s)
    (h : CanonicalPath e N fuel (stepDestination N s (some p.val))) : CanonicalPath e N (fuel+1) s :=
  ⟨.inr ⟨p.val,h.val⟩,⟨p.property,h.property⟩⟩

/-- Decompose the actual canonical SUBTYPE, retaining each coded destination. -/
def canonicalPathSuccEquiv {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) :
    CanonicalPath e N (fuel+1) s ≃
      PUnit ⊕ (Σ p : CanonicalChoice e N s, CanonicalPath e N fuel (stepDestination N s (some p.val))) where
  toFun h := by
    rcases h with ⟨h,hh⟩
    cases h with
    | inl x => exact .inl x
    | inr h => exact .inr ⟨⟨h.1,hh.1⟩,⟨h.2,hh.2⟩⟩
  invFun z := match z with
    | .inl _ => canonicalStop e N fuel s
    | .inr ⟨p,h⟩ => canonicalJump e N fuel s p h
  left_inv h := by
    rcases h with ⟨h,hh⟩
    cases h with
    | inl x => cases x; rfl
    | inr h => rfl
  right_inv z := by
    cases z with
    | inl x => cases x; rfl
    | inr z => rcases z with ⟨⟨p,hp⟩,⟨h,hh⟩⟩; rfl

lemma sum_canonical_path_succ {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) (f : CanonicalPath e N (fuel+1) s → ℝ) :
    (∑ h, f h) = f (canonicalStop e N fuel s) +
      ∑ p : CanonicalChoice e N s, ∑ h : CanonicalPath e N fuel (stepDestination N s (some p.val)),
        f (canonicalJump e N fuel s p h) := by
  rw [← (canonicalPathSuccEquiv e N fuel s).symm.sum_comp f]
  simp [Fintype.sum_sum_type,Fintype.sum_sigma,canonicalPathSuccEquiv]

/-- Exactly one factor2 per JUMP, not per holding interval or stop. -/
def canonicalMass {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (h : CanonicalPath e N fuel s) (T : ℝ) : ℝ :=
  (2:ℝ)^(pathLength N fuel s h.val) * pathMass N r L q fuel s h.val T

lemma canonicalMass_stop {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (T : ℝ) :
    canonicalMass e N r L q (fuel+1) s (canonicalStop e N fuel s) T =
      Real.exp (-holdingRate N r L q s*T) := by
  simp [canonicalMass,canonicalStop,pathLength,pathMass]

lemma canonicalMass_jump {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (p : CanonicalChoice e N s)
    (h : CanonicalPath e N fuel (stepDestination N s (some p.val))) (T : ℝ) :
    canonicalMass e N r L q (fuel+1) s (canonicalJump e N fuel s p h) T =
      pairRate r p.val.1 * ∫ u in (0:ℝ)..T, Real.exp (-holdingRate N r L q s*u) *
        canonicalMass e N r L q fuel (stepDestination N s (some p.val)) h (T-u) := by
  unfold canonicalMass
  simp only [canonicalJump,pathLength,pathMass,pow_add,pow_one]
  have hf : (fun u : ℝ => Real.exp (-holdingRate N r L q s*u) *
      ((2:ℝ)^pathLength N fuel (stepDestination N s (some p.val)) h.val *
        pathMass N r L q fuel (stepDestination N s (some p.val)) h.val (T-u))) =
      fun u => (2:ℝ)^pathLength N fuel (stepDestination N s (some p.val)) h.val *
        (Real.exp (-holdingRate N r L q s*u) * pathMass N r L q fuel (stepDestination N s (some p.val)) h.val (T-u)) := by
    funext u; ring
  rw [hf,intervalIntegral.integral_const_mul]
  unfold choiceRate
  ring

lemma canonicalMass_continuous {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (h : CanonicalPath e N fuel s) :
    Continuous (canonicalMass e N r L q fuel s h) :=
  continuous_const.mul (pathMass_continuous N r L q fuel s h.val)

/-- Original endpoint-resolved source = actual canonical weighted path sum.
Derived by original renewal plus orbit pairing, not assumed from E counting. -/
theorem actual_resolved_canonical_path_sum {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (T : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    (actualResolvedWeight N r L q fuel s T target).toReal =
      ∑ h : CanonicalPath e N fuel s, canonicalMass e N r L q fuel s h T *
        (if observeCode N (pathEnd N fuel s h.val) = target then 1 else 0) := by
  induction fuel generalizing s T with
  | zero =>
      simpa [CanonicalPath,CanonicalPathPred,OrderedPath,canonicalMass,pathMass,pathLength,pathEnd,holdingRate,neg_mul]
        using actual_resolved_real_zero N r L q s T target
  | succ fuel ih =>
      rw [actual_resolved_canonical_real_renewal e,sum_canonical_path_succ]
      apply congrArg₂ (· + ·)
      · simp only [canonicalMass_stop,canonicalStop,pathEnd]
      · apply Finset.sum_congr rfl
        intro p _
        simp only [canonicalMass_jump,canonicalJump,pathEnd]
        erw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
          (f := fun u : ℝ => pairRate r p.val.1 * Real.exp (-holdingRate N r L q s*u) *
            (actualResolvedWeight N r L q fuel (stepDestination N s (some p.val)) ((T:ℝ)-u) target).toReal)
          (μ := volume) T.property]
        let d := stepDestination N s (some p.val)
        let terminal : CanonicalPath e N fuel d → ℝ := fun h =>
          if observeCode N (pathEnd N fuel d h.val) = target then 1 else 0
        have hi : (∫ u in (0:ℝ)..(T:ℝ), pairRate r p.val.1 * Real.exp (-holdingRate N r L q s*u) *
            (actualResolvedWeight N r L q fuel d ((T:ℝ)-u) target).toReal) =
            ∫ u in (0:ℝ)..(T:ℝ), ∑ h : CanonicalPath e N fuel d,
              pairRate r p.val.1 * Real.exp (-holdingRate N r L q s*u) *
                (canonicalMass e N r L q fuel d h ((T:ℝ)-u) * terminal h) := by
          apply intervalIntegral.integral_congr
          intro u hu
          erw [uIcc_of_le T.property] at hu
          have hh := ih d (⟨(T:ℝ)-u,sub_nonneg.mpr hu.2⟩ : ℝ≥0)
          change (actualResolvedWeight N r L q fuel d ((T:ℝ)-u) target).toReal = _ at hh
          change pairRate r p.val.1 * Real.exp (-holdingRate N r L q s*u) *
            (actualResolvedWeight N r L q fuel d ((T:ℝ)-u) target).toReal = _
          erw [hh,Finset.mul_sum]
          rfl
        erw [hi,intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro h _
          change (∫ u in (0:ℝ)..(T:ℝ), pairRate r p.val.1 * Real.exp (-holdingRate N r L q s*u) *
              (canonicalMass e N r L q fuel d h ((T:ℝ)-u) * terminal h)) =
            (pairRate r p.val.1 * ∫ u in (0:ℝ)..(T:ℝ),
              Real.exp (-holdingRate N r L q s*u) * canonicalMass e N r L q fuel d h ((T:ℝ)-u)) * terminal h
          have hf : (fun u : ℝ => pairRate r p.val.1 * Real.exp (-holdingRate N r L q s*u) *
                (canonicalMass e N r L q fuel d h ((T:ℝ)-u) * terminal h)) =
              fun u => pairRate r p.val.1 *
                (Real.exp (-holdingRate N r L q s*u) * canonicalMass e N r L q fuel d h ((T:ℝ)-u)) * terminal h := by
            funext u; ring
          erw [hf,intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
        · intro h _
          have hc := canonicalMass_continuous e N r L q fuel d h
          exact (by fun_prop : Continuous (fun u : ℝ => pairRate r p.val.1 * Real.exp (-holdingRate N r L q s*u) *
            (canonicalMass e N r L q fuel d h ((T:ℝ)-u) * terminal h))).intervalIntegrable 0 T

/-- Concrete term index, independent of the horizon T, allowing zero endpoint
coefficients and repeated rates. No minimal spectral representation claimed. -/
abbrev CanonicalTermIndex {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) :=
  Σ h : CanonicalPath e N fuel s, Fin (pathTerms N r L q fuel s h.val).size

def termRate {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (i : CanonicalTermIndex e N r L q fuel s) : ℝ :=
  (pathTerms N r L q fuel s i.1.val).rate i.2

def termCoefficient {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (target : BlockPopulationObservation Copy V E)
    (i : CanonicalTermIndex e N r L q fuel s) : ℝ :=
  (2:ℝ)^pathLength N fuel s i.1.val * (pathTerms N r L q fuel s i.1.val).coefficient i.2 *
    (if observeCode N (pathEnd N fuel s i.1.val) = target then 1 else 0)

/-- CONSTRUCTED original finite-fuel single-epoch exponential sum. -/
theorem actual_resolved_canonical_exponential_sum {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (T : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    (actualResolvedWeight N r L q fuel s T target).toReal =
      ∑ i : CanonicalTermIndex e N r L q fuel s,
        termCoefficient e N r L q fuel s target i * Real.exp (-termRate e N r L q fuel s i*(T:ℝ)) := by
  rw [actual_resolved_canonical_path_sum e,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro h _
  unfold canonicalMass
  rw [actual_path_mass_expansion]
  unfold ExpTerms.eval
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [termCoefficient,termRate]
  ring

/-- The original nE per-epoch overcount, derived from actual source indices. -/
theorem actual_canonical_term_card_le [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) :
    Fintype.card (CanonicalTermIndex e N r L q fuel s) ≤
      Fintype.card Copy * ∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k := by
  simp only [CanonicalTermIndex,Fintype.card_sigma,Fintype.card_fin]
  calc
    (∑ h : CanonicalPath e N fuel s, (pathTerms N r L q fuel s h.val).size) ≤
        ∑ _h : CanonicalPath e N fuel s, Fintype.card Copy :=
      Finset.sum_le_sum (fun h _ => pathTerms_size_le_original_copies N r L q fuel s h.val)
    _ = Fintype.card (CanonicalPath e N fuel s) * Fintype.card Copy := by simp
    _ ≤ (∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k) * Fintype.card Copy :=
      Nat.mul_le_mul_right _ (actual_canonical_path_card_le e N fuel s)
    _ = _ := Nat.mul_comm _ _

#print axioms choiceOrientationEquiv
#print axioms actual_resolved_canonical_real_renewal
#print axioms actual_resolved_canonical_path_sum
#print axioms actual_resolved_canonical_exponential_sum
#print axioms actual_canonical_term_card_le
end ResearchCommons.MSCI.JC69CanonicalWeightedSum
