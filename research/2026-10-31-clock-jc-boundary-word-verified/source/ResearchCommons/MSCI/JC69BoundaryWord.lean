import ResearchCommons.MSCI.JC69GuardedCalendarQuotient

/-! UNCOMPILED. Actual whole-boundary observation coefficients on one original
register fibre. Dot (OpenAI), 31 October 2026. No rates/site counts occur in
boundaryLaw or boundaryCoefficient. No bank averaging or path/window claim. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69BoundaryWord
open MeasureTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceBoundaryKernels
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69EndpointWeight
open ResearchCommons.MSCI.JC69FixedBankBoundary ResearchCommons.MSCI.JC69WeightedCalendar
open ResearchCommons.MSCI.JC69GuardedCalendarQuotient
open scoped Classical BigOperators ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Original boundary kernels composed without a new rate or site parameter. -/
def boundaryLaw (N : RootedBinary V E X) {sample : Copy → X} :
    List (BoundaryOperation N) → Code N sample → PMF (Code N sample)
  | [],s => PMF.pure s
  | b::bs,s => (boundaryKernel N b s).bind (boundaryLaw N bs)

def boundaryBackward (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → ℝ≥0∞) : List (BoundaryOperation N) → Code N sample → ℝ≥0∞
  | [],s => f s
  | b::bs,s => ∑ d : Code N sample, boundaryKernel N b s d * boundaryBackward N f bs d

def boundaryCoefficient (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) : ℝ≥0∞ :=
  ((boundaryLaw N bs s).map (observeCode N)) target

theorem actual_boundary_word_source (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bs : List (BoundaryOperation N)) (s : Code N sample) :
    sourceProgram N r (bs.map ProgramStep.boundary) s = boundaryLaw N bs s := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons,sourceProgram,sourceProgramStep,boundaryLaw]
      exact congrArg (fun k => (boundaryKernel N b s).bind k) (funext ih)

lemma boundary_backward_expectation (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → ℝ≥0∞) (bs : List (BoundaryOperation N)) (s : Code N sample) :
    boundaryBackward N f bs s = ∑ d : Code N sample, boundaryLaw N bs s d * f d := by
  induction bs generalizing s with
  | nil => simp [boundaryBackward,boundaryLaw,PMF.pure_apply]
  | cons b bs ih =>
      simp only [boundaryBackward,boundaryLaw,PMF.bind_apply,tsum_fintype,ih]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      exact (mul_assoc _ _ _).symm

lemma pmf_observation_readout (N : RootedBinary V E X) {sample : Copy → X}
    (p : PMF (Code N sample)) (F : BlockPopulationObservation Copy V E → ℝ≥0∞) :
    (∑ d : Code N sample, p d * F (observeCode N d)) =
      ∑ o : BlockPopulationObservation Copy V E, (p.map (observeCode N)) o * F o := by
  simp only [PMF.map_apply,tsum_fintype,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [ite_mul,zero_mul]
  simp

lemma boundary_backward_quotient (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → ℝ≥0∞)
    (hf : ∀ s t, observeCode N s = observeCode N t →
      (state s).register = (state t).register → f s = f t)
    (bs : List (BoundaryOperation N)) (s t : Code N sample)
    (ho : observeCode N s = observeCode N t)
    (hr : (state s).register = (state t).register) :
    boundaryBackward N f bs s = boundaryBackward N f bs t := by
  induction bs generalizing s t with
  | nil => exact hf s t ho hr
  | cons b bs ih =>
      obtain ⟨F,hF⟩ := exists_bank_readout N (boundaryBackward N f bs)
        (fun u v huo hur => ih u v huo hur) (state s).register
      have he (u : Code N sample) (hu : (state u).register = (state s).register) :
          boundaryBackward N f (b::bs) u =
            ∑ o : BlockPopulationObservation Copy V E, ((boundaryKernel N b u).map (observeCode N)) o * F o := by
        rw [boundaryBackward,← pmf_observation_readout]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hz : boundaryKernel N b u d = 0
        · simp only [hz,zero_mul]
        · have hd : (state d).register = (state u).register := by
            have hm : (state d).register ∈ ((boundaryKernel N b u).map (fun v => (state v).register)).support :=
              (PMF.mem_support_map_iff _ _ _).mpr ⟨d,(PMF.mem_support_iff _ _).mpr hz,rfl⟩
            rw [actual_boundary_register_law] at hm
            simpa using hm
          exact congrArg (boundaryKernel N b u d * ·) (hF d (hd.trans hu))
      rw [he s rfl,he t hr.symm,actual_fixed_bank_boundary_quotient N b s t ho hr]

lemma boundary_coefficient_backward (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) :
    boundaryCoefficient N bs s target =
      boundaryBackward N (fun d => if observeCode N d = target then 1 else 0) bs s := by
  rw [boundary_backward_expectation,boundaryCoefficient,PMF.map_apply,tsum_fintype]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : observeCode N d = target
  · simp [h]
  · simp [h,Ne.symm h]

/-- Arbitrary endpoint indicators, not only the specialized guarded root.
The proof derives the whole-word quotient from the original one-step laws. -/
theorem actual_boundary_word_quotient (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (s t : Code N sample)
    (ho : observeCode N s = observeCode N t)
    (hr : (state s).register = (state t).register)
    (target : BlockPopulationObservation Copy V E) :
    boundaryCoefficient N bs s target = boundaryCoefficient N bs t target := by
  rw [boundary_coefficient_backward,boundary_coefficient_backward]
  apply boundary_backward_quotient N _ _ bs s t ho hr
  intro u v huv _
  rw [huv]

/-- Same actual bank, with any fixed admitted observation representative.
No reachability or raw snapshot identity is asserted. -/
theorem actual_boundary_word_representative (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (s representative : Code N sample)
    (ho : observeCode N s = observeCode N representative)
    (target : BlockPopulationObservation Copy V E) :
    boundaryCoefficient N bs s target =
      boundaryCoefficient N bs (reBank N representative (state s).register) target := by
  apply actual_boundary_word_quotient
  · exact ho.trans (actual_reBank_observation N representative (state s).register).1.symm
  · exact (actual_reBank_observation N representative (state s).register).2.symm

/-- Original weighted recursion on a boundary word is this count-independent
ordinary PMF recursion; no interval or failure factor is silently removed. -/
theorem actual_boundary_word_readout (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (bs : List (BoundaryOperation N)) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) :
    calendarValue N r L q (fun d => if observeCode N d = target then 1 else 0)
      (bs.map ProgramStep.boundary) s = boundaryCoefficient N bs s target := by
  rw [boundary_coefficient_backward]
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.map_cons,calendarValue,boundaryBackward,actual_boundary_fibre_weight,ih]

/-- Finite original PMF coefficient; this is not a sign claim for any
finite-epoch exponential coefficient. -/
theorem actual_boundary_coefficient_finite (N : RootedBinary V E X) {sample : Copy → X}
    (bs : List (BoundaryOperation N)) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) : boundaryCoefficient N bs s target ≠ ∞ :=
  PMF.apply_ne_top _ _

#print axioms actual_boundary_word_source
#print axioms actual_boundary_word_quotient
#print axioms actual_boundary_word_representative
#print axioms actual_boundary_word_readout
#print axioms actual_boundary_coefficient_finite
end ResearchCommons.MSCI.JC69BoundaryWord
