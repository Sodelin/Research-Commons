import UnifiedLean.G6.ResidualPrefix
import UnifiedLean.G6.HistoryPrefix

/-!
UNCHECKED additive derivative, 7 October 2026.
Translates RESIDUAL-PROGRAM-COMMON-LAW.md (8188491b) and its independent
hand review (715f3f2e). Uses the SAME actual interval means, physical source
bank, entering law, boundary kernels and full finite endpoint vectors.
Numerical upper-mean substitution, physical old-past attachment, executable
tables and positive biological reconstruction are separate obligations.
-/

namespace UnifiedLean.G6.ResidualProgram
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.SourcePrefix
open UnifiedLean.G6.TaylorCertificate
open UnifiedLean.G6.ResidualPrefix UnifiedLean.G6.ProgramPrefix
open UnifiedLean.G6.HistoryPrefix GProgram.G2.SourceFiniteHistory
open scoped Classical BigOperators NNReal ENNReal

/-- Explicit mathematical PMF of the proved finite real residual vector. -/
noncomputable def residualPMF {A : Type*} [Fintype A]
    (q z : PMF A) (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (residualVector q z rho a)) (by
    have hsum : ENNReal.ofReal (∑ a, residualVector q z rho a) =
        ∑ a, ENNReal.ofReal (residualVector q z rho a) :=
      ENNReal.ofReal_sum_of_nonneg (fun a _ => residualVector_nonneg q z rho h0 h1 a)
    rw [← hsum, residualVector_sum]
    simp)

lemma residualPMF_real {A : Type*} [Fintype A]
    (q z : PMF A) (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (a : A) :
    (residualPMF q z rho h0 h1 a).toReal = residualVector q z rho a := by
  change (ENNReal.ofReal (residualVector q z rho a)).toReal = _
  exact ENNReal.toReal_ofReal (residualVector_nonneg q z rho h0 h1 a)

lemma ofReal_scaled_domination {A : Type*} (p q : PMF A) (rho : ℝ)
    (h0 : 0 ≤ rho) (hdom : ∀ a, rho * (q a).toReal ≤ (p a).toReal) (a : A) :
    ENNReal.ofReal rho * q a ≤ p a := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (q.apply_ne_top a))
    (p.apply_ne_top a)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0] using hdom a

lemma residualPMF_domination {A : Type*} [Fintype A]
    (q z : PMF A) (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho ≤ 1) (a : A) :
    ENNReal.ofReal rho * q a ≤ residualPMF q z rho h0 h1 a := by
  apply ofReal_scaled_domination _ _ _ h0
  intro b
  rw [residualPMF_real]
  exact le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr h1) ENNReal.toReal_nonneg)

/-- Both laws dominate one normalized common law; no division by its mass. -/
theorem common_pmf_tv {A : Type*} [Fintype A] (p l q : PMF A) (mu : ℝ≥0∞)
    (hp : ∀ a, mu * q a ≤ p a) (hl : ∀ a, mu * q a ≤ l a) :
    pmfTV p l ≤ 1 - mu.toReal := by
  have hp' (a : A) : mu.toReal * (q a).toReal ≤ (p a).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (p.apply_ne_top a) (hp a)
  have hl' (a : A) : mu.toReal * (q a).toReal ≤ (l a).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (l.apply_ne_top a) (hl a)
  have hsum : (∑ a, mu.toReal * (q a).toReal) = mu.toReal := by
    rw [← Finset.mul_sum, pmf_sum_real, mul_one]
  simpa only [pmfTV, hsum] using common_subprobability_tv _ _ _
    (pmf_sum_real p) (pmf_sum_real l) hp' hl'

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def StepBudget (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) : ProgramStep N → Prop
  | .interval t =>
      2 * ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) ≤ (K : ℝ) + 2
  | .boundary _ => True

noncomputable def residualStepMass (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) : ProgramStep N → ℝ≥0∞
  | .interval t => ENNReal.ofReal
      (residualMass ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K)
  | .boundary _ => 1

noncomputable def residualProgramMass {Copy : Type*} [DecidableEq Copy] [Fintype Copy]
    (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) : List (ProgramStep N) → ℝ≥0∞
  | [] => 1
  | op :: ops => residualStepMass (Copy := Copy) N r K op *
      residualProgramMass (Copy := Copy) N r K ops

noncomputable def residualStepError (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) : ProgramStep N → ℝ
  | .interval t => errorBound
      ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K
  | .boundary _ => 0

noncomputable def residualProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (op : ProgramStep N)
    (s : Code N sample) : PMF (Code N sample) :=
  match op with
  | .interval t => residualPMF (finiteSourcePrefix N r t K s) (sourceIteration N r 0 s)
      (residualMass ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K)
      (residualMass_bounds _ K).1 (residualMass_bounds _ K).2
  | .boundary b => sourceProgramStep N r (.boundary b) s

noncomputable def residualProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) :
      List (ProgramStep N) → Code N sample → PMF (Code N sample)
  | [], s => PMF.pure s
  | op :: ops, s => (residualProgramStep N r K op s).bind (residualProgram N r K ops)

lemma residualStepMass_le_one (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) (op : ProgramStep N) : residualStepMass (Copy := Copy) N r K op ≤ 1 := by
  cases op with
  | interval t =>
      simpa only [residualStepMass, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal
          (residualMass_bounds (globalClockRate (Copy := Copy) r * t) K).2
  | boundary b => exact le_rfl

lemma residualProgramMass_le_one (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) (ops : List (ProgramStep N)) :
    residualProgramMass (Copy := Copy) N r K ops ≤ 1 := by
  induction ops with
  | nil => exact le_rfl
  | cons op ops ih =>
      change residualStepMass (Copy := Copy) N r K op *
        residualProgramMass (Copy := Copy) N r K ops ≤ 1
      exact (mul_le_mul' (residualStepMass_le_one (Copy := Copy) N r K op) ih).trans
        (by simp)

lemma residual_step_deficit (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) (op : ProgramStep N) :
    1 - (residualStepMass (Copy := Copy) N r K op).toReal =
      residualStepError (Copy := Copy) N r K op := by
  cases op with
  | interval t =>
      rw [residualStepMass, ENNReal.toReal_ofReal (residualMass_bounds _ K).1]
      exact residualMass_deficit _ K
  | boundary b => simp only [residualStepMass, residualStepError,
      ENNReal.toReal_one, sub_self]

theorem residual_program_deficit_le_sum (N : RootedBinary V E X)
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N)) :
    1 - (residualProgramMass (Copy := Copy) N r K ops).toReal ≤
      (ops.map (residualStepError (Copy := Copy) N r K)).sum := by
  induction ops with
  | nil => simp only [residualProgramMass, ENNReal.toReal_one, sub_self,
      List.map_nil, List.sum_nil, le_refl]
  | cons op ops ih =>
      have hstep : (residualStepMass (Copy := Copy) N r K op).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top
          (residualStepMass_le_one (Copy := Copy) N r K op)
      have hrest : (residualProgramMass (Copy := Copy) N r K ops).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top
          (residualProgramMass_le_one (Copy := Copy) N r K ops)
      have hproduct := mul_nonneg (sub_nonneg.mpr hstep) (sub_nonneg.mpr hrest)
      rw [residualProgramMass, ENNReal.toReal_mul, List.map_cons, List.sum_cons,
        ← residual_step_deficit (Copy := Copy) N r K op]
      nlinarith only [hproduct, ih]

lemma actual_step_common_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (op : ProgramStep N)
    (s d : Code N sample) (hbudget : StepBudget (Copy := Copy) N r K op) :
    residualStepMass (Copy := Copy) N r K op * finiteProgramStep N r K op s d ≤
      sourceProgramStep N r op s d := by
  cases op with
  | interval t =>
      apply ofReal_scaled_domination _ _ _ (residualMass_bounds _ K).1
      intro z
      exact (mul_le_mul_of_nonneg_right (residualMass_le_prefixMass _ K hbudget)
        ENNReal.toReal_nonneg).trans (actual_source_prefix_domination N r t K s z)
  | boundary b => simp only [residualStepMass, finiteProgramStep, one_mul, le_refl]

lemma residual_step_common_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (op : ProgramStep N) (s d : Code N sample) :
    residualStepMass (Copy := Copy) N r K op * finiteProgramStep N r K op s d ≤
      residualProgramStep N r K op s d := by
  cases op with
  | interval t => exact residualPMF_domination _ _ _ _ _ d
  | boundary b => simp only [residualStepMass, finiteProgramStep,
      residualProgramStep, one_mul, le_refl]

theorem actual_program_common_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (s d : Code N sample)
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    residualProgramMass (Copy := Copy) N r K ops * finiteProgram N r K ops s d ≤
      sourceProgram N r ops s d := by
  induction ops generalizing s d with
  | nil => simp only [residualProgramMass, finiteProgram, sourceProgram, one_mul, le_refl]
  | cons op ops ih =>
      have hhead := hbudget op (by simp)
      have htail : ∀ q ∈ ops, StepBudget (Copy := Copy) N r K q :=
        fun q hq => hbudget q (List.mem_cons_of_mem op hq)
      change (residualStepMass (Copy := Copy) N r K op *
          residualProgramMass (Copy := Copy) N r K ops) *
        ((finiteProgramStep N r K op s).bind (finiteProgram N r K ops)) d ≤
        ((sourceProgramStep N r op s).bind (sourceProgram N r ops)) d
      exact bind_scaled_domination _ _ _ _ _ _
        (fun d => actual_step_common_domination N r K op s d hhead)
        (fun s d => ih s d htail) d

theorem residual_program_common_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N)) (s d : Code N sample) :
    residualProgramMass (Copy := Copy) N r K ops * finiteProgram N r K ops s d ≤
      residualProgram N r K ops s d := by
  induction ops generalizing s d with
  | nil => simp only [residualProgramMass, finiteProgram, residualProgram, one_mul, le_refl]
  | cons op ops ih =>
      change (residualStepMass (Copy := Copy) N r K op *
          residualProgramMass (Copy := Copy) N r K ops) *
        ((finiteProgramStep N r K op s).bind (finiteProgram N r K ops)) d ≤
        ((residualProgramStep N r K op s).bind (residualProgram N r K ops)) d
      exact bind_scaled_domination _ _ _ _ _ _
        (residual_step_common_domination N r K op s) ih d

theorem same_initial_program_tv (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample))
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    pmfTV (initial.bind (sourceProgram N r ops))
      (initial.bind (residualProgram N r K ops)) ≤
        1 - (residualProgramMass (Copy := Copy) N r K ops).toReal := by
  apply common_pmf_tv _ _ (initial.bind (finiteProgram N r K ops))
  · intro d
    simpa only [one_mul] using bind_scaled_domination initial initial
      (sourceProgram N r ops) (finiteProgram N r K ops) 1
      (residualProgramMass (Copy := Copy) N r K ops) (fun _ => by simp)
      (fun s d => actual_program_common_domination N r K ops s d hbudget) d
  · intro d
    simpa only [one_mul] using bind_scaled_domination initial initial
      (residualProgram N r K ops) (finiteProgram N r K ops) 1
      (residualProgramMass (Copy := Copy) N r K ops) (fun _ => by simp)
      (residual_program_common_domination N r K ops) d

theorem same_initial_program_tv_budget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample))
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    pmfTV (initial.bind (sourceProgram N r ops))
      (initial.bind (residualProgram N r K ops)) ≤
        (ops.map (residualStepError (Copy := Copy) N r K)).sum :=
  (same_initial_program_tv N r K ops initial hbudget).trans
    (residual_program_deficit_le_sum (Copy := Copy) N r K ops)

lemma residual_interval_real (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (t : ℝ≥0) (s d : Code N sample) :
    (residualProgramStep N r K (.interval t) s d).toReal =
      residualSourceVector N r t K s d :=
  residualPMF_real _ _ _ _ _ d

lemma same_initial_common_domination {A B : Type*}
    (initial : PMF A) (p q : A → PMF B) (mu : ℝ≥0∞)
    (hdom : ∀ s d, mu * q s d ≤ p s d) (d : B) :
    mu * (initial.bind q) d ≤ (initial.bind p) d := by
  simpa only [one_mul] using bind_scaled_domination initial initial p q 1 mu
    (fun _ => by simp) hdom d

theorem same_initial_joint_program_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) (readout : Code N sample → O)
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    pmfTV ((initial.bind (sourceProgram N r ops)).map readout)
      ((initial.bind (residualProgram N r K ops)).map readout) ≤
        1 - (residualProgramMass (Copy := Copy) N r K ops).toReal := by
  apply common_pmf_tv _ _ ((initial.bind (finiteProgram N r K ops)).map readout)
  · exact map_scaled_domination _ _ _
      (same_initial_common_domination initial _ _ _
        (fun s d => actual_program_common_domination N r K ops s d hbudget)) readout
  · exact map_scaled_domination _ _ _
      (same_initial_common_domination initial _ _ _
        (residual_program_common_domination N r K ops)) readout

theorem same_initial_joint_program_tv_budget {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) (readout : Code N sample → O)
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    pmfTV ((initial.bind (sourceProgram N r ops)).map readout)
      ((initial.bind (residualProgram N r K ops)).map readout) ≤
        (ops.map (residualStepError (Copy := Copy) N r K)).sum :=
  (same_initial_joint_program_tv N r K ops initial readout hbudget).trans
    (residual_program_deficit_le_sum (Copy := Copy) N r K ops)

noncomputable def residualHistoryLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (s : Code N sample) : PMF (Fin ops.length → Code N sample) :=
  historyLaw (residualProgramStep N r K) ops s

/-- One normalized JOINT history is beneath any stepwise dominating history. -/
theorem history_common_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ)
    (targetStep : ProgramStep N → Code N sample → PMF (Code N sample))
    (ops : List (ProgramStep N)) (s : Code N sample)
    (h : Fin ops.length → Code N sample)
    (hstep : ∀ op ∈ ops, ∀ s d,
      residualStepMass (Copy := Copy) N r K op * finiteProgramStep N r K op s d ≤
        targetStep op s d) :
    residualProgramMass (Copy := Copy) N r K ops * finiteHistoryLaw N r K ops s h ≤
      historyLaw targetStep ops s h := by
  induction ops generalizing s with
  | nil => simp only [residualProgramMass, one_mul, finiteHistoryLaw, historyLaw, le_refl]
  | cons op ops ih =>
      have hhead := hstep op (by simp)
      have htail : ∀ q ∈ ops, ∀ s d,
          residualStepMass (Copy := Copy) N r K q * finiteProgramStep N r K q s d ≤
            targetStep q s d :=
        fun q hq => hstep q (List.mem_cons_of_mem op hq)
      change (residualStepMass (Copy := Copy) N r K op *
          residualProgramMass (Copy := Copy) N r K ops) *
        ((finiteProgramStep N r K op s).bind (fun d =>
          (finiteHistoryLaw N r K ops d).map (Fin.cons d))) h ≤
        ((targetStep op s).bind (fun d =>
          (historyLaw targetStep ops d).map (Fin.cons d))) h
      apply bind_scaled_domination _ _ _ _ _ _ (hhead s)
      intro d z
      exact map_scaled_domination _ _ _ (fun tail => ih d tail htail)
        (fun tail : Fin ops.length → Code N sample =>
          (Fin.cons d tail : Fin (ops.length + 1) → Code N sample)) z

theorem actual_history_common_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (s : Code N sample) (h : Fin ops.length → Code N sample)
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    residualProgramMass (Copy := Copy) N r K ops * finiteHistoryLaw N r K ops s h ≤
      sourceHistoryLaw N r ops s h :=
  history_common_domination N r K (sourceProgramStep N r) ops s h
    (fun op hop s d => actual_step_common_domination N r K op s d (hbudget op hop))

theorem residual_history_common_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (s : Code N sample) (h : Fin ops.length → Code N sample) :
    residualProgramMass (Copy := Copy) N r K ops * finiteHistoryLaw N r K ops s h ≤
      residualHistoryLaw N r K ops s h :=
  history_common_domination N r K (residualProgramStep N r K) ops s h
    (fun op _ s d => residual_step_common_domination N r K op s d)

theorem same_initial_history_tv (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample))
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    pmfTV (initial.bind (sourceHistoryLaw N r ops))
      (initial.bind (residualHistoryLaw N r K ops)) ≤
        1 - (residualProgramMass (Copy := Copy) N r K ops).toReal := by
  apply common_pmf_tv _ _ (initial.bind (finiteHistoryLaw N r K ops))
  · exact same_initial_common_domination initial _ _ _
      (fun s h => actual_history_common_domination N r K ops s h hbudget)
  · exact same_initial_common_domination initial _ _ _
      (residual_history_common_domination N r K ops)

theorem same_initial_history_tv_budget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample))
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    pmfTV (initial.bind (sourceHistoryLaw N r ops))
      (initial.bind (residualHistoryLaw N r K ops)) ≤
        (ops.map (residualStepError (Copy := Copy) N r K)).sum :=
  (same_initial_history_tv N r K ops initial hbudget).trans
    (residual_program_deficit_le_sum (Copy := Copy) N r K ops)

/-- The entering old-past label is retained from the SAME correlated law. -/
lemma retained_past_common_domination {Past S H : Type*}
    (initial : PMF (Past × S)) (p q : S → PMF H) (mu : ℝ≥0∞)
    (hdom : ∀ s h, mu * q s h ≤ p s h) (z : Past × H) :
    mu * retainPast initial q z ≤ retainPast initial p z := by
  unfold retainPast
  exact same_initial_common_domination initial _ _ _
    (fun s => map_scaled_domination _ _ _ (hdom s.2) (Prod.mk s.1)) z

theorem retained_past_joint_history_tv {Past O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Past × Code N sample))
    (readout : (Past × (Fin ops.length → Code N sample)) → O)
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    pmfTV ((retainPast initial (sourceHistoryLaw N r ops)).map readout)
      ((retainPast initial (residualHistoryLaw N r K ops)).map readout) ≤
        1 - (residualProgramMass (Copy := Copy) N r K ops).toReal := by
  apply common_pmf_tv _ _ ((retainPast initial (finiteHistoryLaw N r K ops)).map readout)
  · exact map_scaled_domination _ _ _
      (retained_past_common_domination initial _ _ _
        (fun s h => actual_history_common_domination N r K ops s h hbudget)) readout
  · exact map_scaled_domination _ _ _
      (retained_past_common_domination initial _ _ _
        (residual_history_common_domination N r K ops)) readout

theorem retained_past_joint_history_tv_budget {Past O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Past × Code N sample))
    (readout : (Past × (Fin ops.length → Code N sample)) → O)
    (hbudget : ∀ op ∈ ops, StepBudget (Copy := Copy) N r K op) :
    pmfTV ((retainPast initial (sourceHistoryLaw N r ops)).map readout)
      ((retainPast initial (residualHistoryLaw N r K ops)).map readout) ≤
        (ops.map (residualStepError (Copy := Copy) N r K)).sum :=
  (retained_past_joint_history_tv N r K ops initial readout hbudget).trans
    (residual_program_deficit_le_sum (Copy := Copy) N r K ops)

#print axioms residualPMF
#print axioms residualPMF_real
#print axioms common_pmf_tv
#print axioms actual_program_common_domination
#print axioms residual_program_common_domination
#print axioms history_common_domination
#print axioms actual_history_common_domination
#print axioms residual_history_common_domination
#print axioms retained_past_joint_history_tv
#print axioms retained_past_joint_history_tv_budget

end UnifiedLean.G6.ResidualProgram
