import ResearchCommons.MSCI.JC69BoundaryWord

/-! UNCOMPILED. Exact signed real expansion of the original interval followed
by a whole boundary word. Dot (OpenAI),31 October2026. The reference Code and
common path-position index can be fixed before counts and the original bank.
No global M/denominator/window theorem is claimed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69StagePathCoefficient
open MeasureTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69EndpointWeight
open ResearchCommons.MSCI.JC69EndpointQuotient ResearchCommons.MSCI.JC69FixedBankBoundary
open ResearchCommons.MSCI.JC69WeightedCalendar ResearchCommons.MSCI.JC69CalendarObservationKernel
open ResearchCommons.MSCI.JC69GuardedCalendarQuotient ResearchCommons.MSCI.JC69BoundaryWord
open ResearchCommons.MSCI.JC69ResolvedRealVolterra ResearchCommons.MSCI.JC69OrderedPathExpansion
open ResearchCommons.MSCI.JC69CanonicalWeightedSum ResearchCommons.MSCI.JC69CommonCountIndex
open scoped Classical BigOperators ENNReal NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Absent admitted fibres are zero. Representatives are selected before
counts, sites, rates and the original bank; only boundary evaluation is re-banked. -/
def boundaryReadout (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (sigma : V → Bool)
    (target o : BlockPopulationObservation Copy V E) : ℝ≥0∞ :=
  if h : ∃ s : Code N sample, observeCode N s = o then
    boundaryCoefficient N bs (reBank N (Classical.choose h) sigma) target else 0

lemma boundary_readout_finite (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (sigma : V → Bool)
    (target o : BlockPopulationObservation Copy V E) : boundaryReadout (sample := sample) N bs sigma target o ≠ ∞ := by
  unfold boundaryReadout
  split_ifs with h
  · exact actual_boundary_coefficient_finite N bs _ target
  · exact ENNReal.zero_ne_top

lemma boundary_readout_actual (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (sigma : V → Bool)
    (target : BlockPopulationObservation Copy V E) (s : Code N sample)
    (hs : (state s).register = sigma) :
    boundaryReadout (sample := sample) N bs sigma target (observeCode N s) = boundaryCoefficient N bs s target := by
  have h : ∃ d : Code N sample, observeCode N d = observeCode N s := ⟨s,rfl⟩
  rw [boundaryReadout,dif_pos h]
  apply actual_boundary_word_quotient
  · exact (actual_reBank_observation N (Classical.choose h) sigma).1.trans (Classical.choose_spec h)
  · exact (actual_reBank_observation N (Classical.choose h) sigma).2.trans hs.symm

lemma boundary_readout_rebank (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (sigma : V → Bool)
    (target : BlockPopulationObservation Copy V E) (s : Code N sample) :
    boundaryReadout (sample := sample) N bs sigma target (observeCode N s) =
      boundaryCoefficient N bs (reBank N s sigma) target := by
  have h := boundary_readout_actual N bs sigma target (reBank N s sigma)
    (actual_reBank_observation N s sigma).2
  simpa only [(actual_reBank_observation N s sigma).1] using h

/-- The physical source coefficient, not an assumed scalar expansion. -/
def intervalBoundaryCoefficient (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (T : ℝ≥0) (bs : List (BoundaryOperation N)) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) : ℝ≥0∞ :=
  calendarValue N r L q (fun d => if observeCode N d = target then 1 else 0)
    (.interval T :: bs.map ProgramStep.boundary) s

/-- Actual unnormalized interval fibres, SAME original bank in the whole
boundary word, and any fixed admitted incoming observation representative. -/
theorem actual_interval_boundary_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (T : ℝ≥0) (bs : List (BoundaryOperation N)) (s reference : Code N sample)
    (ho : observeCode N s = observeCode N reference)
    (target : BlockPopulationObservation Copy V E) :
    intervalBoundaryCoefficient N r L q T bs s target =
      ∑ o : BlockPopulationObservation Copy V E,
        actualResolvedWeight N r L q (Fintype.card Copy) reference T o *
          boundaryReadout (sample := sample) N bs (state s).register target o := by
  let F := boundaryReadout (sample := sample) N bs (state s).register target
  have hs : intervalBoundaryCoefficient N r L q T bs s target =
      ∑ d : Code N sample, segmentFibreWeight N r L q (.interval T) s d * F (observeCode N d) := by
    rw [intervalBoundaryCoefficient,calendarValue]
    apply Finset.sum_congr rfl
    intro d _
    rw [actual_boundary_word_readout]
    by_cases hz : sourceProgramStep N r (.interval T) s d = 0
    · rw [actual_fibre_zero_of_source_zero N r L q (.interval T) s d hz,zero_mul,zero_mul]
    · have hd := program_step_support_register N r (.interval T) s d ((PMF.mem_support_iff _ _).mpr hz)
      exact congrArg (segmentFibreWeight N r L q (.interval T) s d * ·)
        (boundary_readout_actual N bs (state s).register target d hd).symm
  rw [hs,actual_observation_readout_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [actual_interval_observation_weight,
    actual_resolved_weight_quotient N r L q (Fintype.card Copy) s reference T o ho]

lemma interval_boundary_summand_finite (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (T : ℝ≥0) (bs : List (BoundaryOperation N)) (sigma : V → Bool)
    (reference : Code N sample) (target o : BlockPopulationObservation Copy V E) :
    actualResolvedWeight N r L q (Fintype.card Copy) reference T o *
      boundaryReadout (sample := sample) N bs sigma target o ≠ ∞ :=
  ENNReal.mul_ne_top
    (ne_of_lt ((actual_resolved_weight_le_one N r L q (Fintype.card Copy) reference T T.property o).trans_lt
      ENNReal.one_lt_top)) (boundary_readout_finite N bs sigma target o)

/-- Finiteness is proved for the actual coefficient before any toReal step. -/
theorem actual_interval_boundary_finite (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (T : ℝ≥0) (bs : List (BoundaryOperation N)) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) :
    intervalBoundaryCoefficient N r L q T bs s target ≠ ∞ := by
  rw [actual_interval_boundary_sum N r L q T bs s s rfl target]
  exact ENNReal.sum_ne_top.mpr (fun o _ => interval_boundary_summand_finite N r L q T bs _ s target o)

lemma common_coefficient_indicator {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (i : CommonTermIndex e N fuel s) (target : BlockPopulationObservation Copy V E) :
    commonCoefficient e N r L q fuel s target i =
      commonCoefficient e N r L q fuel s (observeCode N (pathEnd N fuel s i.1.val)) i *
        (if observeCode N (pathEnd N fuel s i.1.val) = target then 1 else 0) := by
  simp [commonCoefficient,termCoefficient,commonTermEquiv]

/-- The intermediate observation target collapses at the actual path END.
Signed coefficients remain in R; no ofReal is applied term by term. -/
lemma common_coefficient_readout {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (i : CommonTermIndex e N fuel s) (T : ℝ) (F : BlockPopulationObservation Copy V E → ℝ) :
    (∑ o : BlockPopulationObservation Copy V E,
      (commonCoefficient e N r L q fuel s o i * Real.exp (-commonRate e N r L q fuel s i*T)) * F o) =
      commonCoefficient e N r L q fuel s (observeCode N (pathEnd N fuel s i.1.val)) i *
        F (observeCode N (pathEnd N fuel s i.1.val)) * Real.exp (-commonRate e N r L q fuel s i*T) := by
  rw [Finset.sum_eq_single (observeCode N (pathEnd N fuel s i.1.val))]
  · ring
  · intro o _ hne
    rw [common_coefficient_indicator]
    simp only [Ne.symm hne,if_false,mul_zero,zero_mul]
  · simp

/-- CONSTRUCTED actual interval/whole-boundary coefficient expansion on a
count-independent path-position index. The original bank appears only in the
boundary probability; a fixed reference may have a different bank. -/
theorem actual_interval_boundary_path_expansion {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (T : ℝ≥0)
    (bs : List (BoundaryOperation N)) (s reference : Code N sample)
    (ho : observeCode N s = observeCode N reference)
    (target : BlockPopulationObservation Copy V E) :
    (intervalBoundaryCoefficient N r L q T bs s target).toReal =
      ∑ i : CommonTermIndex e N (Fintype.card Copy) reference,
        commonCoefficient e N r L q (Fintype.card Copy) reference
          (observeCode N (pathEnd N (Fintype.card Copy) reference i.1.val)) i *
        (boundaryCoefficient N bs
          (reBank N (pathEnd N (Fintype.card Copy) reference i.1.val) (state s).register) target).toReal *
        Real.exp (-commonRate e N r L q (Fintype.card Copy) reference i*(T:ℝ)) := by
  rw [actual_interval_boundary_sum N r L q T bs s reference ho target]
  rw [ENNReal.toReal_sum (fun o _ => interval_boundary_summand_finite N r L q T bs _ reference target o)]
  simp_rw [ENNReal.toReal_mul]
  simp_rw [actual_common_index_expansion e N r L q (Fintype.card Copy) reference T,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [common_coefficient_readout,boundary_readout_rebank]

/-- The derived coefficient uses at most nE terms, without an extra
intermediate-state S factor. This is not the global calendar count. -/
theorem actual_interval_boundary_index_card [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    {sample : Copy → X} (reference : Code N sample) :
    Fintype.card (CommonTermIndex e N (Fintype.card Copy) reference) ≤
      Fintype.card Copy * ∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k :=
  actual_common_index_card_le e N (Fintype.card Copy) reference

#print axioms actual_interval_boundary_sum
#print axioms actual_interval_boundary_finite
#print axioms actual_interval_boundary_path_expansion
#print axioms actual_interval_boundary_index_card
end ResearchCommons.MSCI.JC69StagePathCoefficient
