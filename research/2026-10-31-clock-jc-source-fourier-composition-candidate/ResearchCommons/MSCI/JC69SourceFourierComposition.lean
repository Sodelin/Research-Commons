import ResearchCommons.MSCI.JC69CompleteClockComposition
import ResearchCommons.MSCI.JC69ObservedFourier

/-! Actual observed-source Fourier to original calendar/root-clock occupation.
UNCOMPILED candidate, dot (OpenAI), 31 October 2026. The actual endpoint fibres
are not normalized; original flags/clocks and initial potential are retained.
No finite exponential-polynomial expansion or source quotient is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69SourceFourierComposition
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.NativeParentRouting
open GProgram.G2.ActualCalendarTrace GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.FiniteAncestralTrace
open GProgram.G2.FaithfulPairAgeDecoration
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Tree
open ResearchCommons.MSCI.JC69Observation ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69Source ResearchCommons.MSCI.JC69ObservedFourier
open ResearchCommons.MSCI.JC69CompleteClockComposition
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- The original PMF's conditional Fourier sum, with its total fallback intact. -/
def pointFourier (L : ℕ) (N : RootedBinary V E X) {sample : Copy → X}
    (q : Fin L → Copy → Base) (leafAge : Copy → ℝ)
    (z : Code N sample × (Copy → Copy → ℝ)) : ℝ :=
  ∑ p, (conditionalLocusKernel L N leafAge z p).toReal * originalCharacter L q p

lemma point_fourier_measurable (L : ℕ) (N : RootedBinary V E X) {sample : Copy → X}
    (q : Fin L → Copy → Base) (leafAge : Copy → ℝ) :
    Measurable (pointFourier L N (sample := sample) q leafAge) := by
  apply Finset.measurable_sum Finset.univ
  intro p _
  exact (conditional_locus_mass_measurable L N leafAge p).ennreal_toReal.mul measurable_const

/-- Integrability comes from actual original PMF masses before any occupation
substitution. Thus no infinite ENNReal integral is hidden by toReal. -/
theorem actual_point_fourier_integrable (L : ℕ) (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (q : Fin L → Copy → Base) :
    Integrable (fun z => pointFourier L N q (fun x => C.age (N.leaf (sample x)))
      (originalPoint N C sample register H gamma common z))
      (completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register)) := by
  apply integrable_finsetSum Finset.univ
  intro p _
  exact (original_mass_integrable L N C sample register H gamma common r p).mul_const
    (originalCharacter L q p)

/-- Accepted original-label probability, applied at its actual timed support. -/
lemma conditional_mass_toReal (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (z : Code N sample × (Copy → Copy → ℝ))
    (hz : GoodPoint N leafAge z) (p : Copy → Base) :
    (conditionalKernel N leafAge z p).toReal =
      rootLikelihood ((state z.1).genealogy (selectedRoot N z.1))
        (clockSurvivals leafAge _ (decode z.2 _))
        (labelPattern ((state z.1).genealogy (selectedRoot N z.1)) p) := by
  rw [conditionalKernel,dif_pos hz]
  exact actual_original_label_probability (state z.1) z.1.property.forest hz.1
    leafAge z.2 (hz.2.choose : ℝ) hz.2.choose_spec
    (selectedRoot N z.1) (selected_root_live N z.1) p

theorem point_fourier_eq_labelled (L : ℕ) (N : RootedBinary V E X)
    {sample : Copy → X} (q : Fin L → Copy → Base) (leafAge : Copy → ℝ)
    (z : Code N sample × (Copy → Copy → ℝ)) (hz : GoodPoint N leafAge z) :
    pointFourier L N q leafAge z =
      labelledTreeFourier L q leafAge ((state z.1).genealogy (selectedRoot N z.1)) z.2 := by
  unfold pointFourier labelledTreeFourier
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  change (∏ j, conditionalKernel N leafAge z (p j)).toReal = _
  rw [ENNReal.toReal_prod]
  unfold locusLikelihood
  exact Finset.prod_congr rfl (fun j _ => conditional_mass_toReal N leafAge z hz (p j))

/-- The complementary original character patterns vanish by the actual
stationary-root projection, not by extrapolating killing above the MRCA. -/
theorem point_fourier_unbalanced (L : ℕ) (N : RootedBinary V E X)
    {sample : Copy → X} (q : Fin L → Copy → Base) (leafAge : Copy → ℝ)
    (z : Code N sample × (Copy → Copy → ℝ)) (hz : GoodPoint N leafAge z)
    (hbad : ∃ j, ∑ x, q j x ≠ 0) : pointFourier L N q leafAge z = 0 := by
  obtain ⟨j,hj⟩ := hbad
  let t := (state z.1).genealogy (selectedRoot N z.1)
  have ht : t.WellLabelled := z.1.property.forest.wellLabelled _ (selected_root_live N z.1)
  have hfull : t.leaves = Finset.univ := actual_single_root_covers_original_copies
    (state z.1) z.1.property.forest hz.1 _ (selected_root_live N z.1)
  have hc : totalCharge (q j) t ≠ 0 := by
    rw [totalCharge_eq_original_leaves _ _ ht,hfull]
    exact hj
  let e : (Fin L → Copy → Base) ≃ (Fin L → Pattern t) :=
    Equiv.piCongrRight (fun _ => fullPatternEquiv t ht hfull)
  rw [point_fourier_eq_labelled L N q leafAge z hz]
  unfold labelledTreeFourier
  calc
    _ = ∑ p : Fin L → Copy → Base,
        locusLikelihood L t (clockSurvivals leafAge t (decode z.2 t)) (e p) *
          ∏ k, patternCharacter (q k) t (e p k) := by
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      change (∏ x, character (q k x) (p k x)) =
        patternCharacter (q k) t (labelPattern t (p k))
      rw [label_pattern_character _ _ _ ht,hfull]
    _ = ∑ p : Fin L → Pattern t,
        locusLikelihood L t (clockSurvivals leafAge t (decode z.2 t)) p *
          ∏ k, patternCharacter (q k) t (p k) :=
      e.sum_comp (fun p => locusLikelihood L t (clockSurvivals leafAge t (decode z.2 t)) p *
        ∏ k, patternCharacter (q k) t (p k))
    _ = 0 := by
      rw [locus_fourier]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hc)

theorem actual_observed_unbalanced_zero (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (hbad : ∃ j, ∑ x, q j x ≠ 0) :
    observedFourier L N C sample register H gamma common r q = 0 := by
  rw [actual_observed_fourier_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [actual_original_point_support N C sample register H gamma common r]
    with z hz
  exact point_fourier_unbalanced L N q _ _ hz hbad

/-- Full admitted source support is transported to the ORIGINAL endpoint
fibre and ORIGINAL root-clock measure, without conditioning either measure. -/
theorem actual_branch_good_point (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (d : Code N sample) :
    let ops := compiledCalendarProgram N C H gamma common
    let s := initialCode N sample register
    ∀ᵐ past ∂(actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d},
      ∀ᵐ c ∂currentPairClockMeasure N r d,
        GoodPoint N (fun x => C.age (N.leaf (sample x)))
          (originalPoint N C sample register H gamma common
            (completeClockRecord N ops d past c)) := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have h := actual_original_point_support N C sample register H gamma common r
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff] at h
  have hd := h d (Finset.mem_univ d)
  have hm : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) :=
    measurable_const.prodMk measurable_id
  have hp := ae_ae_of_ae_prod (ae_of_ae_map hm.aemeasurable hd)
  filter_upwards [hp] with past htail
  exact ae_of_ae_map (complete_ancestral_trace_measurable N d).aemeasurable htail

/-- Tonelli for the existing finite complete-calendar sum and its actual
ancestral pushforward. No altered process, flags, or fibre masses. -/
theorem complete_clock_lintegral (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (F : CompleteCalendarRecord N sample ops → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂completeCalendarTraceLaw N r ops s) =
      ∑ d : Code N sample,
        ∫⁻ past, ∫⁻ c, F (completeClockRecord N ops d past c)
          ∂currentPairClockMeasure N r d
          ∂(actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d} := by
  letI := actual_calendar_trace_probability N r ops s
  rw [completeCalendarTraceLaw,lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro d _
  letI := complete_ancestral_trace_probability N r d
  have hm : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) :=
    measurable_const.prodMk measurable_id
  rw [lintegral_map hF hm,lintegral_prod _ (hF.comp hm).aemeasurable]
  apply lintegral_congr
  intro past
  change (∫⁻ z, F (d,past,z) ∂(currentPairClockMeasure N r d).map
    (completeAncestralTrace N d)) = _
  exact lintegral_map (hF.comp (measurable_const.prodMk
    (measurable_const.prodMk measurable_id))) (complete_ancestral_trace_measurable N d)

/-- Actual observed balanced Fourier coefficient equals the original
calendar/root-clock occupation integral. All original source parameters,
complete original-copy labels, shared locus tree and initial potential remain.
This is NOT yet a finite killed-calendar exponential-polynomial expansion. -/
theorem actual_observed_balanced_clock_integral (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (hbal : ∀ j, ∑ x, q j x = 0) :
    let ops := compiledCalendarProgram N C H gamma common
    let s := initialCode N sample register
    let leafAge := fun x : Copy => C.age (N.leaf (sample x))
    let M := fun x (_ : Copy) => leafAge x
    observedFourier L N C sample register H gamma common r q =
      (∑ d : Code N sample,
        ∫⁻ past, ∫⁻ c,
          ENNReal.ofReal (Real.exp (-((4/3:ℝ) * ∑ j,
            (forestPotential (q j) leafAge (state s) M (firstOriginalDate N C) +
              completeClockOccupation N (q j) ops s d past c))))
          ∂currentPairClockMeasure N r d
          ∂(actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d}).toReal := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  let leafAge := fun x : Copy => C.age (N.leaf (sample x))
  let f : CompleteCalendarRecord N sample ops → ℝ := fun z =>
    pointFourier L N q leafAge (originalPoint N C sample register H gamma common z)
  have hf : Measurable f := (point_fourier_measurable L N q leafAge).comp
    (original_point_measurable N C sample register H gamma common)
  have hn : ∀ᵐ z ∂completeCalendarTraceLaw N r ops s, 0 ≤ f z := by
    filter_upwards [actual_original_point_support N C sample register H gamma common r] with z hz
    dsimp only [f]
    rw [point_fourier_eq_labelled L N q leafAge _ hz]
    rw [labelled_complete_locus_fourier L q leafAge _
      (originalPoint N C sample register H gamma common z).1.property.forest hz.1
      _ (selected_root_live N _) hbal _ (0:ℝ)]
    exact (Real.exp_pos _).le
  have hfi : Integrable f (completeCalendarTraceLaw N r ops s) :=
    actual_point_fourier_integrable L N C sample register H gamma common r q
  have hfinite : (∫⁻ z, ENNReal.ofReal (f z) ∂completeCalendarTraceLaw N r ops s) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hn).mp hfi.hasFiniteIntegral
  calc
    _ = ∫ z, f z ∂completeCalendarTraceLaw N r ops s :=
      actual_observed_fourier_integral L N C sample register H gamma common r q
    _ = (∫⁻ z, ENNReal.ofReal (f z) ∂completeCalendarTraceLaw N r ops s).toReal :=
      integral_eq_lintegral_of_nonneg_ae hn hf.aestronglyMeasurable
    _ = _ := by
      rw [complete_clock_lintegral N r ops s _ hf.ennreal_ofReal]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      apply lintegral_congr_ae
      filter_upwards [actual_branch_good_point N C sample register H gamma common r d,
        actual_original_complete_clock_fourier N C sample register H gamma common r L q hbal d]
        with past hp he
      apply lintegral_congr_ae
      filter_upwards [hp,he] with c hc hfourier
      change ENNReal.ofReal (pointFourier L N q leafAge _) = _
      rw [point_fourier_eq_labelled L N q leafAge _ hc,hfourier]

#print axioms actual_point_fourier_integrable
#print axioms actual_observed_unbalanced_zero
#print axioms point_fourier_eq_labelled
#print axioms actual_branch_good_point
#print axioms complete_clock_lintegral
#print axioms actual_observed_balanced_clock_integral
end ResearchCommons.MSCI.JC69SourceFourierComposition
