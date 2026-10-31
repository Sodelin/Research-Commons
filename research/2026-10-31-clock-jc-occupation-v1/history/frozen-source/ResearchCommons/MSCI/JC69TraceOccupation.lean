import ResearchCommons.MSCI.JC69Occupation
import G2MarkedTraceRenewal

/-! Literal-trace readout of actual charge occupation. Contributor: dot
(OpenAI), 30 October 2026. UNCOMPILED; no weighted source-law assumption.
Inactive padding is ignored. The total readout is not a certificate that an
arbitrary input record is chronological, successful, or source-realizable. -/
noncomputable section
namespace ResearchCommons.MSCI.JC69TraceOccupation
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceWinningClockReset
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualDecorationFold
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open MeasureTheory
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Holding occupation, read from original absolute trace ages. The previous
age is carried explicitly; inactive padding changes neither it nor state. -/
def occupationAt (N : RootedBinary V E X) {sample : Copy → X} (q : Copy → Base) :
    (n : ℕ) → Code N sample → ℝ → ℝ → ClockTrace N sample n → ℝ
  | 0,s,previous,horizon,_ => codeCharge N q s * (horizon-previous)
  | n+1,s,previous,horizon,z =>
      if (z 0).1 = true then
        codeCharge N q s * ((z 0).2.1-previous) +
          occupationAt N q n (z 0).2.2 (z 0).2.1 horizon (fun i => z i.succ)
      else occupationAt N q n s previous horizon (fun i => z i.succ)

lemma occupation_shift (N : RootedBinary V E X) {sample : Copy → X} (q : Copy → Base)
    (n : ℕ) (s : Code N sample) (previous horizon age : ℝ) (z : ClockTrace N sample n) :
    occupationAt N q n s (age+previous) (age+horizon) (shiftTraceAges N age z) =
      occupationAt N q n s previous horizon z := by
  induction n generalizing s previous with
  | zero => simp [occupationAt]
  | succ n ih =>
      by_cases h : (z 0).1 = true
      · simp only [occupationAt,shiftTraceAges,if_pos h]
        change codeCharge N q s * ((age+(z 0).2.1)-(age+previous)) +
          occupationAt N q n (z 0).2.2 (age+(z 0).2.1) (age+horizon)
            (shiftTraceAges N age (fun i => z i.succ)) = _
        rw [ih]
        ring
      · simp only [occupationAt,shiftTraceAges,if_neg h]
        apply ih

lemma occupation_empty (N : RootedBinary V E X) {sample : Copy → X} (q : Copy → Base)
    (n : ℕ) (s : Code N sample) (previous horizon : ℝ) :
    occupationAt N q n s previous horizon (emptyTrace N n s) =
      codeCharge N q s * (horizon-previous) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

lemma occupation_prepend (N : RootedBinary V E X) {sample : Copy → X} (q : Copy → Base)
    (n : ℕ) (s d : Code N sample) (age horizon : ℝ) (z : ClockTrace N sample n) :
    occupationAt N q (n+1) s 0 horizon (prependTrace N age d z) =
      codeCharge N q s*age + occupationAt N q n d 0 (horizon-age) z := by
  change codeCharge N q s*(age-0) +
    occupationAt N q n d age horizon (shiftTraceAges N age z) = _
  have h := occupation_shift N q n d 0 (horizon-age) age z
  have ht : age+(horizon-age) = horizon := by ring
  simp only [add_zero,ht] at h
  rw [h,sub_zero]

/-- The readout of the existing literal trace equals the cost derived in the
actual matrix-fold theorem on the SAME clocks, including all flags/padding. -/
theorem actual_trace_occupation (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ) (c : Choice N s → ℝ) :
    occupationAt N q n s 0 t (literalMarkedTrace N n t s c).2 =
      literalOccupation N q n t s c := by
  induction n generalizing s t with
  | zero => simp [literalMarkedTrace,occupationAt,literalOccupation]
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp [literalMarkedTrace,literalOccupation,hstop,occupation_empty]
      · simp only [literalMarkedTrace,literalOccupation,if_neg hstop]
        cases hw : selectedWinner c with
        | none => simp [occupation_empty]
        | some p =>
            by_cases hp : c p ≤ t
            · simp only [if_pos hp,occupation_prepend]
              rw [ih]
            · simp [hp,occupation_empty]

local instance codeMeasurable (N : RootedBinary V E X) (sample : Copy → X) :
    MeasurableSpace (Code N sample) := ⊤

/-- Joint measurability of the actual record readout. Finite destination
states are treated discretely; real ages retain their Borel sigma algebra. -/
theorem occupation_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (n : ℕ) (s : Code N sample) :
    Measurable (fun z : ℝ × ℝ × ClockTrace N sample n =>
      occupationAt N q n s z.1 z.2.1 z.2.2) := by
  induction n generalizing s with
  | zero => exact measurable_const.mul (measurable_snd.fst.sub measurable_fst)
  | succ n ih =>
      let dispatch : (ℝ × ℝ × ClockTrace N sample n) × Code N sample → ℝ :=
        fun z => occupationAt N q n z.2 z.1.1 z.1.2.1 z.1.2.2
      have hd : Measurable dispatch := by
        apply measurable_from_prod_countable_left
        intro d
        exact ih d
      have hfuture : Measurable (fun z : ℝ × ℝ × ClockTrace N sample (n+1) =>
          occupationAt N q n (z.2.2 0).2.2 (z.2.2 0).2.1 z.2.1
            (fun i => z.2.2 i.succ)) := by
        exact hd.comp (by fun_prop)
      have hrest : Measurable (fun z : ℝ × ℝ × ClockTrace N sample (n+1) =>
          occupationAt N q n s z.1 z.2.1 (fun i => z.2.2 i.succ)) :=
        (ih s).comp (by fun_prop)
      change Measurable (fun z : ℝ × ℝ × ClockTrace N sample (n+1) =>
        if (z.2.2 0).1 = true then
          codeCharge N q s*((z.2.2 0).2.1-z.1) +
            occupationAt N q n (z.2.2 0).2.2 (z.2.2 0).2.1 z.2.1
              (fun i => z.2.2 i.succ)
        else occupationAt N q n s z.1 z.2.1 (fun i => z.2.2 i.succ))
      apply Measurable.ite
      · exact measurableSet_eq_fun (by fun_prop) measurable_const
      · exact (measurable_const.mul (by fun_prop)).add hfuture
      · exact hrest

/-- A success flag is preserved, not conditioned away. Failure records carry
zero weight; the eventual full-mass proof must justify discarding them. -/
def traceWeight (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ)
    (z : Bool × ClockTrace N sample n) : ℝ≥0∞ :=
  if z.1 = true then
    ENNReal.ofReal (Real.exp (-((4/3:ℝ)*occupationAt N q n s 0 t z.2))) else 0

theorem trace_weight_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ) :
    Measurable (traceWeight N q n s t) := by
  have ho : Measurable (fun z : Bool × ClockTrace N sample n =>
      occupationAt N q n s 0 t z.2) :=
    (occupation_joint_measurable N q n s).comp (by fun_prop)
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_fst measurable_const
  · exact (Real.measurable_exp.comp (measurable_const.mul ho).neg).ennreal_ofReal
  · exact measurable_const

/-- All locus columns use one and the same original trace. Exposures are
summed before exponentiation; independent sites never resample the genealogy. -/
def locusTraceWeight (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ)
    (z : Bool × ClockTrace N sample n) : ℝ≥0∞ :=
  if z.1 = true then ENNReal.ofReal
    (Real.exp (-((4/3:ℝ)* ∑ j, occupationAt N (q j) n s 0 t z.2))) else 0

theorem locus_trace_weight_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ) (s : Code N sample) (t : ℝ) :
    Measurable (locusTraceWeight N L q n s t) := by
  have ho : Measurable (fun z : Bool × ClockTrace N sample n =>
      ∑ j, occupationAt N (q j) n s 0 t z.2) := by
    apply Finset.measurable_sum
    intro j _
    exact (occupation_joint_measurable N (q j) n s).comp (by fun_prop)
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_fst measurable_const
  · exact (Real.measurable_exp.comp (measurable_const.mul ho).neg).ennreal_ofReal
  · exact measurable_const

#print axioms occupation_shift
#print axioms occupation_prepend
#print axioms actual_trace_occupation
#print axioms occupation_joint_measurable
#print axioms trace_weight_measurable
#print axioms locus_trace_weight_measurable
end ResearchCommons.MSCI.JC69TraceOccupation
