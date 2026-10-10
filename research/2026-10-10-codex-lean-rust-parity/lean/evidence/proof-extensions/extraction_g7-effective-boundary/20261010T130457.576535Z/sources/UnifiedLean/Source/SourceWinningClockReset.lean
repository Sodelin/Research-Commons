import UnifiedLean.Source.SourceExponentialResiduals

/-!
# Winning-clock time and independent residuals of every surviving coordinate

Contributor: dot, 2026-10-02. The actual product clock measure is restricted
to an actual winning coordinate and mapped to its time plus all competitors'
residual clocks. Factorization is derived, not a supplied reset-law field.
Original source destination/reset catalogue and successive path assembly are
subsequent bindings; latent clock records are not added physical observations.
-/
namespace UnifiedLean.Source.SourceWinningClockReset
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceExponentialRaceDensity
open UnifiedLean.Source.SourceExponentialResiduals
open scoped Classical BigOperators NNReal ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Literal winning time and every original competitor's remaining clock. -/
noncomputable def resetClock (p : I) : (I → ℝ) ≃ᵐ (ℝ × (Other p → ℝ)) where
  toFun c := (c p,fun q => c q.val-c p)
  invFun z q := if h : q = p then z.1 else z.1+z.2 ⟨q,h⟩
  left_inv c := by
    funext q
    by_cases h : q = p
    · subst q; simp
    · simp [h]
  right_inv z := by
    apply Prod.ext
    · simp
    · funext q; simp [q.property]
  measurable_toFun := by
    change Measurable (fun c : I → ℝ => (c p,fun q : Other p => c q.val-c p))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × (Other p → ℝ) => fun q : I =>
      if h : q = p then z.1 else z.1+z.2 ⟨q,h⟩)
    apply measurable_pi_lambda
    intro q
    by_cases h : q = p
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop

def winningRegion (p : I) : Set (I → ℝ) :=
  {c | 0 ≤ c p ∧ ∀ q : Other p, c p < c q.val}

lemma measurable_winningRegion (p : I) : MeasurableSet (winningRegion p) := by
  have h1 : MeasurableSet {c : I → ℝ | 0 ≤ c p} :=
    measurableSet_le measurable_const (measurable_pi_apply p)
  have h2 : MeasurableSet (⋂ q : Other p, {c : I → ℝ | c p < c q.val}) :=
    MeasurableSet.iInter (fun q => measurableSet_lt (measurable_pi_apply p) (measurable_pi_apply q.val))
  simpa only [winningRegion,Set.setOf_and,Set.setOf_forall] using h1.inter h2

def splitResetEvent (p : I) (A : Set ℝ) (B : Set (Other p → ℝ)) :
    Set (ℝ × (Other p → ℝ)) :=
  {z | z.1 ∈ A ∧ 0 ≤ z.1 ∧
    (fun q : Other p => z.2 q-z.1) ∈ B ∧ ∀ q : Other p, z.1 < z.2 q}

lemma measurable_split_reset (p : I) (A : Set ℝ) (B : Set (Other p → ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) : MeasurableSet (splitResetEvent p A B) := by
  have h1 : MeasurableSet {z : ℝ × (Other p → ℝ) | z.1 ∈ A} := hA.preimage measurable_fst
  have h2 : MeasurableSet {z : ℝ × (Other p → ℝ) | 0 ≤ z.1} :=
    measurableSet_le measurable_const measurable_fst
  have h3 : MeasurableSet {z : ℝ × (Other p → ℝ) | (fun q : Other p => z.2 q-z.1) ∈ B} := hB.preimage (by fun_prop :
    Measurable (fun z : ℝ × (Other p → ℝ) => fun q => z.2 q-z.1))
  have h4 : MeasurableSet (⋂ q : Other p, {z : ℝ × (Other p → ℝ) | z.1 < z.2 q}) :=
    MeasurableSet.iInter (fun q => measurableSet_lt measurable_fst
      ((measurable_pi_apply q).comp measurable_snd))
  simpa only [splitResetEvent,Set.setOf_and,Set.setOf_forall] using
    h1.inter (h2.inter (h3.inter h4))

lemma actual_reset_event_fubini (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I)
    (A : Set ℝ) (B : Set (Other p → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.pi (fun i => expMeasure (rate i)))
      ((resetClock p) ⁻¹' (A ×ˢ B) ∩ winningRegion p) =
      ∫⁻ x in A ∩ Ici 0,
        ENNReal.ofReal (Real.exp (-((∑ q : Other p, rate q.val)*x))) *
          (Measure.pi (fun q : Other p => expMeasure (rate q.val))) B ∂expMeasure (rate p) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  have hp : (resetClock p) ⁻¹' (A ×ˢ B) ∩ winningRegion p =
      (splitClock p) ⁻¹' splitResetEvent p A B := by
    ext c
    simp only [mem_inter_iff,mem_preimage,mem_prod,resetClock,splitClock,
      MeasurableEquiv.coe_mk,winningRegion,splitResetEvent,mem_setOf_eq]
    tauto
  rw [hp,(splitClock_measurePreserving (fun i => expMeasure (rate i)) p).measure_preimage_equiv,
    Measure.prod_apply (measurable_split_reset p A B hA hB)]
  have hs : ∀ x : ℝ, (Prod.mk x) ⁻¹' splitResetEvent p A B =
      if x ∈ A ∩ Ici 0 then
        (fun c : Other p → ℝ => fun q => c q-x) ⁻¹' B ∩
          Set.univ.pi (fun _ : Other p => Ioi x) else ∅ := by
    intro x
    by_cases hx : x ∈ A ∩ Ici 0
    · rw [if_pos hx]
      ext c
      simp only [mem_preimage,splitResetEvent,mem_setOf_eq,mem_inter_iff,mem_pi,
        mem_univ,true_implies,mem_Ioi]
      exact ⟨fun h => ⟨h.2.2.1,h.2.2.2⟩,fun h => ⟨hx.1,hx.2,h.1,h.2⟩⟩
    · rw [if_neg hx]
      ext c
      simp only [mem_preimage,splitResetEvent,mem_setOf_eq,mem_empty_iff_false]
      exact ⟨fun h => hx ⟨h.1,h.2.1⟩,False.elim⟩
  simp_rw [hs]
  rw [← lintegral_indicator (hA.inter measurableSet_Ici)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A ∩ Ici 0
  · simp only [if_pos hx,Set.indicator_of_mem hx]
    exact actual_survivor_residual_event (fun q : Other p => rate q.val)
      (fun q => hr q.val) ⟨x,hx.2⟩ B hB
  · simp only [if_neg hx,measure_empty,Set.indicator_of_notMem hx]

lemma exponential_nonnegative_support {r : ℝ} (hr : 0 < r) :
    (expMeasure r).restrict (Ici 0) = expMeasure r := by
  letI := isProbabilityMeasure_expMeasure hr
  have hz : (expMeasure r) (Iic 0) = 0 := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    change ENNReal.ofReal ((expMeasure r).real (Iic 0)) = 0
    rw [exponential_real_Iic hr]
    simp
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  apply measure_mono_null _ hz
  intro x hx
  simp only [mem_setOf_eq,mem_Ici,not_le] at hx
  exact hx.le

lemma residual_pdf_factor (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) (x : ℝ) :
    exponentialPDF (rate p) x *
      ENNReal.ofReal (Real.exp (-((∑ q : Other p, rate q.val)*x))) =
      ENNReal.ofReal (rate p/(∑ i, rate i)) * exponentialPDF (∑ i, rate i) x := by
  by_cases hx : 0 ≤ x
  · have hh := actual_race_pdf_factor rate hr p x
    rw [competitor_tail rate hr p hx] at hh
    exact hh
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx),
      zero_mul,mul_zero]

/-- Joint probability of the actual winning time and ANY measurable event
of all residual competitor clocks factors exactly. This is stronger than
the winner CDF or scalar no-event memorylessness. -/
theorem actual_winner_residual_rectangle (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I)
    (A : Set ℝ) (B : Set (Other p → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.pi (fun i => expMeasure (rate i)))
      ((resetClock p) ⁻¹' (A ×ˢ B) ∩ winningRegion p) =
      ENNReal.ofReal (rate p/(∑ i, rate i)) * (expMeasure (∑ i, rate i)) A *
        (Measure.pi (fun q : Other p => expMeasure (rate q.val))) B := by
  have htotal := race_total_positive rate hr p
  rw [actual_reset_event_fubini rate hr p A B hA hB]
  change (∫⁻ x in A ∩ Ici 0, _ ∂volume.withDensity (exponentialPDF (rate p))) = _
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
    (by unfold exponentialPDF; fun_prop) _ (hA.inter measurableSet_Ici)
    (Filter.Eventually.of_forall (fun x => by unfold exponentialPDF; exact ENNReal.ofReal_lt_top))]
  simp only [Pi.mul_apply]
  have hf : ∀ x : ℝ, exponentialPDF (rate p) x *
      (ENNReal.ofReal (Real.exp (-((∑ q : Other p, rate q.val)*x))) *
        (Measure.pi (fun q : Other p => expMeasure (rate q.val))) B) =
      (ENNReal.ofReal (rate p/(∑ i, rate i)) *
        (Measure.pi (fun q : Other p => expMeasure (rate q.val))) B) *
          exponentialPDF (∑ i, rate i) x := by
    intro x
    rw [← mul_assoc,residual_pdf_factor rate hr p]
    ac_rfl
  simp_rw [hf]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop)]
  have hmass : (∫⁻ x in A ∩ Ici 0, exponentialPDF (∑ i, rate i) x) =
      (expMeasure (∑ i, rate i)) A := by
    change _ = (volume.withDensity (exponentialPDF (∑ i, rate i))) A
    rw [withDensity_apply _ hA]
    have hh := congrArg (fun mu : Measure ℝ => mu A) (exponential_nonnegative_support htotal)
    rw [Measure.restrict_apply hA] at hh
    change (volume.withDensity (exponentialPDF (∑ i, rate i))) (A ∩ Ici 0) =
      (volume.withDensity (exponentialPDF (∑ i, rate i))) A at hh
    rw [withDensity_apply _ (hA.inter measurableSet_Ici),withDensity_apply _ hA] at hh
    exact hh
  rw [hmass]
  ac_rfl

/-- Full joint reset measure: after an actual winning coordinate p, every
remaining clock is independently exponential at its SAME original rate and
independent of the winning time. The winning mass is the original rate
fraction; neither factorization nor a conditional reset law is assumed. -/
theorem actual_winner_reset_measure (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) :
    ((Measure.pi (fun i => expMeasure (rate i))).restrict (winningRegion p)).map (resetClock p) =
      (ENNReal.ofReal (rate p/(∑ i, rate i)) • expMeasure (∑ i, rate i)).prod
        (Measure.pi (fun q : Other p => expMeasure (rate q.val))) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  letI := isProbabilityMeasure_expMeasure (race_total_positive rate hr p)
  letI := Measure.smul_finite (expMeasure (∑ i, rate i))
    (show ENNReal.ofReal (rate p/(∑ i, rate i)) ≠ ∞ from ENNReal.ofReal_ne_top)
  apply (Measure.prod_eq _).symm
  intro A B hA hB
  rw [(resetClock p).map_apply,Measure.restrict_apply ((hA.prod hB).preimage (resetClock p).measurable),
    actual_winner_residual_rectangle rate hr p A B hA hB,Measure.smul_apply,smul_eq_mul]

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- SOURCE INSTANCE of the full winning-time/residual law. All original
CURRENT competitor IDs and their original population half-rates are retained.
An actual winner yields independent original-rate residuals, independent of
its time. This discharges the clock-memoryless reset implication; choosing
the merged destination's persistent/new pair catalogue and composing all
successive paths remain the connected original-source assembly. -/
theorem original_current_winner_reset (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    ((currentPairClockMeasure N r s).restrict (winningRegion p)).map (resetClock p) =
      (ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).prod
        (Measure.pi (fun q : Other p => expMeasure (choiceRate N r s q.val))) := by
  apply actual_winner_reset_measure
  intro q
  exact div_pos (pairRate_pos r q.1) (by norm_num)

#print axioms actual_reset_event_fubini
#print axioms actual_winner_residual_rectangle
#print axioms actual_winner_reset_measure
#print axioms original_current_winner_reset
end UnifiedLean.Source.SourceWinningClockReset
