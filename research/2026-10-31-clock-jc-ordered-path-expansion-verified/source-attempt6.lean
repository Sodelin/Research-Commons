import ResearchCommons.MSCI.JC69ResolvedRealVolterra
import ResearchCommons.MSCI.JC69HoldingConvolution

/-! Actual ordered-choice endpoint path expansion. UNCOMPILED candidate.
Dot (OpenAI), 31 October 2026. The auxiliary path convolution uses oriented
real intervals; its identification with the source is ONLY for t ≥ 0.
Ordered half-rate choices are not identified with unordered histories here.
No calendar-boundary, root-path count, or finite-window theorem is claimed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69OrderedPathExpansion
open MeasureTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceMergerClockCatalogue
open GProgram.G2.LiteralMarkedClockTrace
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69WeightedTrace ResearchCommons.MSCI.JC69EndpointWeight
open ResearchCommons.MSCI.JC69ResolvedRealVolterra ResearchCommons.MSCI.JC69HoldingConvolution
open scoped Classical BigOperators NNReal ENNReal Interval
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Same-epoch source killing rate; no bank or quotient representative is chosen. -/
def holdingRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (s : Code N sample) : ℝ := totalRate N r s + locusKill N L q s

lemma locusKill_merger_le (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (s : Code N sample) (p : Choice N s) :
    locusKill N L q (stepDestination N s (some p)) ≤ locusKill N L q s := by
  unfold locusKill
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro j _
  unfold codeCharge
  exact_mod_cast actual_merger_charge_count_nonincreasing N s p (fun x (_ : Unit) => q j x)

/-- Only an ACTUAL comparable merger supplies strict separation. -/
theorem holdingRate_strict_merger (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (s : Code N sample) (p : Choice N s) :
    holdingRate N r L q (stepDestination N s (some p)) < holdingRate N r L q s :=
  add_lt_add_of_lt_of_le (actual_totalRate_strict_merger N r s p)
    (locusKill_merger_le N L q s p)

/-- Stop now, or take one actual ordered half-rate choice and continue with
one less unit of the ORIGINAL finite fuel. The stop branch remains at fuel 0. -/
def OrderedPath (N : RootedBinary V E X) {sample : Copy → X} :
    ℕ → Code N sample → Type _
  | 0, _ => PUnit
  | n+1, s => PUnit ⊕ (Σ p : Choice N s, OrderedPath N n (stepDestination N s (some p)))

instance pathFintype (N : RootedBinary V E X) {sample : Copy → X}
    (n : ℕ) (s : Code N sample) : Fintype (OrderedPath N n s) := by
  induction n generalizing s with
  | zero => change Fintype PUnit; infer_instance
  | succ n ih =>
      change Fintype (PUnit ⊕ (Σ p : Choice N s, OrderedPath N n (stepDestination N s (some p))))
      letI : ∀ p : Choice N s, Fintype (OrderedPath N n (stepDestination N s (some p))) :=
        fun p => ih (stepDestination N s (some p))
      infer_instance

def pathEnd (N : RootedBinary V E X) {sample : Copy → X} :
    (n : ℕ) → (s : Code N sample) → OrderedPath N n s → Code N sample
  | 0, s, _ => s
  | _+1, s, .inl _ => s
  | n+1, s, .inr ⟨p,h⟩ => pathEnd N n (stepDestination N s (some p)) h

def pathLength (N : RootedBinary V E X) {sample : Copy → X} :
    (n : ℕ) → (s : Code N sample) → OrderedPath N n s → ℕ
  | 0, _, _ => 0
  | _+1, _, .inl _ => 0
  | n+1, s, .inr ⟨p,h⟩ => 1 + pathLength N n (stepDestination N s (some p)) h

lemma pathLength_le_fuel (N : RootedBinary V E X) {sample : Copy → X}
    (n : ℕ) (s : Code N sample) (h : OrderedPath N n s) : pathLength N n s h ≤ n := by
  induction n generalizing s with
  | zero => simp [pathLength]
  | succ n ih =>
      cases h with
      | inl h => simp [pathLength]
      | inr h => obtain ⟨p,h⟩ := h; simpa [pathLength, Nat.add_comm] using Nat.succ_le_succ (ih _ h)

/-- Exact cardinal descent, with the actual end state retained. -/
theorem pathLength_add_liveCard (N : RootedBinary V E X) {sample : Copy → X}
    (n : ℕ) (s : Code N sample) (h : OrderedPath N n s) :
    pathLength N n s h + liveCard (pathEnd N n s h) = liveCard s := by
  induction n generalizing s with
  | zero => simp [pathLength,pathEnd]
  | succ n ih =>
      cases h with
      | inl h => simp [pathLength,pathEnd]
      | inr h =>
          obtain ⟨p,h⟩ := h
          have hi := ih (stepDestination N s (some p)) h
          have hd := merger_destination_card N s p
          simp only [pathLength,pathEnd]
          omega

/-- Each path mass is its ordered product of ACTUAL choice rates and holding
convolutions. No endpoint indicator is moved into an intermediate state. -/
def pathMass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base) :
    (n : ℕ) → (s : Code N sample) → OrderedPath N n s → ℝ → ℝ
  | 0, s, _, T => Real.exp (-holdingRate N r L q s*T)
  | _+1, s, .inl _, T => Real.exp (-holdingRate N r L q s*T)
  | n+1, s, .inr ⟨p,h⟩, T => choiceRate N r s p *
      ∫ u in (0:ℝ)..T, Real.exp (-holdingRate N r L q s*u) *
        pathMass N r L q n (stepDestination N s (some p)) h (T-u)

/-- Explicit finite exponential expansion; repeated rates in OTHER paths
are harmless. All rates of one path are actual successive holding rates. -/
structure ExpTerms where
  size : ℕ
  rate : Fin size → ℝ
  coefficient : Fin size → ℝ

def ExpTerms.eval (a : ExpTerms) (T : ℝ) : ℝ :=
  ∑ i, a.coefficient i * Real.exp (-a.rate i*T)

def singletonTerms (a : ℝ) : ExpTerms := ⟨1,fun _ => a,fun _ => 1⟩

def prependTerms (a rp : ℝ) (b : ExpTerms) : ExpTerms where
  size := b.size+1
  rate := Fin.cons a b.rate
  coefficient := Fin.cons (-rp*(∑ i, b.coefficient i/(a-b.rate i)))
    (fun i => rp*(b.coefficient i/(a-b.rate i)))

def pathTerms (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base) :
    (n : ℕ) → (s : Code N sample) → OrderedPath N n s → ExpTerms
  | 0, s, _ => singletonTerms (holdingRate N r L q s)
  | _+1, s, .inl _ => singletonTerms (holdingRate N r L q s)
  | n+1, s, .inr ⟨p,h⟩ => prependTerms (holdingRate N r L q s) (choiceRate N r s p)
      (pathTerms N r L q n (stepDestination N s (some p)) h)

lemma pathTerms_size (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (h : OrderedPath N n s) :
    (pathTerms N r L q n s h).size = pathLength N n s h + 1 := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      cases h with
      | inl h => rfl
      | inr h => obtain ⟨p,h⟩ := h; simp [pathTerms,prependTerms,pathLength,ih,Nat.add_assoc,Nat.add_comm]

lemma pathTerms_rate_le (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (h : OrderedPath N n s) :
    ∀ i, (pathTerms N r L q n s h).rate i ≤ holdingRate N r L q s := by
  induction n generalizing s with
  | zero => intro i; exact le_rfl
  | succ n ih =>
      cases h with
      | inl h => intro i; exact le_rfl
      | inr h =>
          obtain ⟨p,h⟩ := h
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact le_rfl
          · exact (ih _ h j).trans (le_of_lt (holdingRate_strict_merger N r L q s p))

lemma prependTerms_eval (a rp T : ℝ) (b : ExpTerms) :
    (prependTerms a rp b).eval T = rp *
      ((∑ i, b.coefficient i/(a-b.rate i)*Real.exp (-b.rate i*T)) -
       (∑ i, b.coefficient i/(a-b.rate i))*Real.exp (-a*T)) := by
  simp only [ExpTerms.eval,prependTerms,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  rw [mul_sub,Finset.mul_sum Finset.univ
    (fun i => b.coefficient i/(a-b.rate i)*Real.exp (-b.rate i*T)) rp]
  simp_rw [mul_assoc]
  ring

/-- Constructed finite expansion, not an assumed likelihood representation.
Every denominator is parent holding rate minus a comparable descendant rate. -/
theorem actual_path_mass_expansion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (h : OrderedPath N n s) (T : ℝ) :
    pathMass N r L q n s h T = (pathTerms N r L q n s h).eval T := by
  induction n generalizing s T with
  | zero => simp [pathMass,pathTerms,singletonTerms,ExpTerms.eval]
  | succ n ih =>
      cases h with
      | inl h => simp [pathMass,pathTerms,singletonTerms,ExpTerms.eval]
      | inr h =>
          obtain ⟨p,h⟩ := h
          simp only [pathMass,pathTerms]
          simp_rw [ih _ h]
          rw [prependTerms_eval]
          congr 1
          exact convolve_finite_exponential_sum _ _ _ _ (fun i =>
            (pathTerms_rate_le N r L q n _ h i).trans_lt (holdingRate_strict_merger N r L q s p))

lemma pathMass_continuous (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (h : OrderedPath N n s) :
    Continuous (pathMass N r L q n s h) := by
  have heq := funext (actual_path_mass_expansion N r L q n s h)
  rw [heq]
  unfold ExpTerms.eval
  fun_prop

lemma liveCard_pos [Nonempty Copy] (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : 0 < liveCard s := by
  obtain ⟨x⟩ := ‹Nonempty Copy›
  apply Finset.card_pos.mpr
  exact ⟨(state s).ancestor x, s.property.forest.ancestor_live x⟩

/-- The bound counts ORIGINAL gene copies, not replicated site characters. -/
theorem pathLength_lt_original_copies [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (n : ℕ) (s : Code N sample) (h : OrderedPath N n s) :
    pathLength N n s h < Fintype.card Copy := by
  have hp := liveCard_pos N (pathEnd N n s h)
  have he := pathLength_add_liveCard N n s h
  have hs : liveCard s ≤ Fintype.card Copy := Finset.card_le_univ s.val.live
  omega

theorem pathTerms_size_le_original_copies [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (h : OrderedPath N n s) :
    (pathTerms N r L q n s h).size ≤ Fintype.card Copy := by
  rw [pathTerms_size]
  exact pathLength_lt_original_copies N n s h

/-- Explicit Fintype split: stop/no-event plus all ACTUAL ordered choices. -/
lemma sum_path_succ (N : RootedBinary V E X) {sample : Copy → X}
    (n : ℕ) (s : Code N sample) (f : OrderedPath N (n+1) s → ℝ) :
    (∑ h, f h) = f (.inl PUnit.unit) +
      ∑ p : Choice N s, ∑ h : OrderedPath N n (stepDestination N s (some p)), f (.inr ⟨p,h⟩) := by
  change (∑ h : PUnit ⊕ (Σ p : Choice N s, OrderedPath N n (stepDestination N s (some p))), f h) = _
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,Fintype.sum_sigma]

/-- Actual source identification. The endpoint test is at the END of each
path, and the zero-fuel/no-choice branches retain their no-event success mass.
No negative-horizon or signed-ENNReal identification is made. -/
theorem actual_resolved_ordered_path_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    (actualResolvedWeight N r L q n s t target).toReal =
      ∑ h : OrderedPath N n s, pathMass N r L q n s h t *
        (if observeCode N (pathEnd N n s h) = target then 1 else 0) := by
  induction n generalizing s t with
  | zero => simpa only [OrderedPath,pathMass,pathEnd,holdingRate,Fintype.sum_unique,neg_mul] using actual_resolved_real_zero N r L q s t target
  | succ n ih =>
      rw [actual_resolved_real_renewal,sum_path_succ]
      apply congrArg₂ (· + ·)
      · simp only [pathMass,pathEnd,holdingRate,neg_mul]
      · apply Finset.sum_congr rfl
        intro p _
        simp only [pathMass,pathEnd]
        erw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le
          (f := fun u : ℝ => choiceRate N r s p *
            Real.exp (-((totalRate N r s+locusKill N L q s)*u)) *
            (actualResolvedWeight N r L q n (stepDestination N s (some p)) ((t:ℝ)-u) target).toReal)
          (μ := volume) t.property]
        let d := stepDestination N s (some p)
        let terminal : OrderedPath N n d → ℝ := fun h =>
          if observeCode N (pathEnd N n d h) = target then 1 else 0
        have hi : (∫ u in (0:ℝ)..(t:ℝ), choiceRate N r s p *
            Real.exp (-((totalRate N r s+locusKill N L q s)*u)) *
            (actualResolvedWeight N r L q n d ((t:ℝ)-u) target).toReal) =
            ∫ u in (0:ℝ)..(t:ℝ), ∑ h : OrderedPath N n d,
              choiceRate N r s p * Real.exp (-holdingRate N r L q s*u) *
                (pathMass N r L q n d h ((t:ℝ)-u) * terminal h) := by
          apply intervalIntegral.integral_congr
          intro u hu
          erw [uIcc_of_le t.property] at hu
          have hh := ih d (⟨(t:ℝ)-u,sub_nonneg.mpr hu.2⟩ : ℝ≥0)
          change (actualResolvedWeight N r L q n d ((t:ℝ)-u) target).toReal = _ at hh
          change choiceRate N r s p * Real.exp (-((totalRate N r s+locusKill N L q s)*u)) *
            (actualResolvedWeight N r L q n d ((t:ℝ)-u) target).toReal =
              ∑ h : OrderedPath N n d, choiceRate N r s p * Real.exp (-holdingRate N r L q s*u) *
                (pathMass N r L q n d h ((t:ℝ)-u) * terminal h)
          erw [hh,Finset.mul_sum]
          simp only [holdingRate,neg_mul]
        erw [hi,intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro h _
          change (∫ u in (0:ℝ)..(t:ℝ), choiceRate N r s p *
              Real.exp (-holdingRate N r L q s*u) *
                (pathMass N r L q n d h ((t:ℝ)-u) * terminal h)) =
            (choiceRate N r s p * ∫ u in (0:ℝ)..(t:ℝ),
              Real.exp (-holdingRate N r L q s*u) * pathMass N r L q n d h ((t:ℝ)-u)) * terminal h
          have hf : (fun u : ℝ => choiceRate N r s p * Real.exp (-holdingRate N r L q s*u) *
                (pathMass N r L q n d h ((t:ℝ)-u) * terminal h)) =
              fun u => choiceRate N r s p *
                (Real.exp (-holdingRate N r L q s*u) * pathMass N r L q n d h ((t:ℝ)-u)) * terminal h := by
            funext u; ring
          erw [hf,intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
        · intro h _
          have hc := pathMass_continuous N r L q n d h
          exact (by fun_prop : Continuous (fun u : ℝ => choiceRate N r s p *
            Real.exp (-holdingRate N r L q s*u) *
              (pathMass N r L q n d h ((t:ℝ)-u) * terminal h))).intervalIntegrable 0 t

/-- The actual finite-fuel endpoint readout is now a CONSTRUCTED signed
finite exponential sum. This statement alone supplies no uniform quotient
path count, no denominator polynomial bound and no whole-calendar expansion. -/
theorem actual_resolved_finite_exponential_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (n : ℕ) (s : Code N sample) (t : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    (actualResolvedWeight N r L q n s t target).toReal =
      ∑ h : OrderedPath N n s, (pathTerms N r L q n s h).eval t *
        (if observeCode N (pathEnd N n s h) = target then 1 else 0) := by
  rw [actual_resolved_ordered_path_sum]
  exact Finset.sum_congr rfl (fun h _ => by rw [actual_path_mass_expansion])

#print axioms holdingRate_strict_merger
#print axioms pathLength_add_liveCard
#print axioms actual_path_mass_expansion
#print axioms pathLength_lt_original_copies
#print axioms pathTerms_size_le_original_copies
#print axioms actual_resolved_ordered_path_sum
#print axioms actual_resolved_finite_exponential_sum
end ResearchCommons.MSCI.JC69OrderedPathExpansion
