import UnifiedLean.G6.ProgramPrefix
import G2SourceFiniteHistory

/-!
UNCHECKED root draft, 7 October 2026. No compiler result is implied.
Retain the entire endpoint vector, with optional correlated old-past label.
This reuses the inherited actual source-history recursion; it does not identify
a finite-bin observation menu or alter any source/provider definition.
-/
namespace UnifiedLean.G6.HistoryPrefix
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.ProgramPrefix UnifiedLean.G6.FiniteProbability
open GProgram.G2.SourceFiniteHistory
open scoped Classical NNReal ENNReal BigOperators

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def finiteHistoryLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (s : Code N sample) : PMF (Fin ops.length → Code N sample) :=
  historyLaw (finiteProgramStep N r K) ops s

/-- Domination of one JOINT history, without multiplication by its coordinate count. -/
theorem actual_history_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (s : Code N sample) (h : Fin ops.length → Code N sample) :
    programMass (Copy := Copy) N r K ops * finiteHistoryLaw N r K ops s h ≤
      sourceHistoryLaw N r ops s h := by
  induction ops generalizing s with
  | nil => simp only [programMass, one_mul, finiteHistoryLaw, sourceHistoryLaw, le_refl]
  | cons op ops ih =>
      change (stepMass (Copy := Copy) N r K op * programMass (Copy := Copy) N r K ops) *
          ((finiteProgramStep N r K op s).bind (fun d =>
            (finiteHistoryLaw N r K ops d).map (Fin.cons d))) h ≤
        ((sourceProgramStep N r op s).bind (fun d =>
          (sourceHistoryLaw N r ops d).map (Fin.cons d))) h
      apply bind_scaled_domination _ _ _ _ _ _ (actual_step_domination N r K op s)
      intro d z
      exact map_scaled_domination _ _ _ (ih d) (Fin.cons d) z

theorem same_initial_history_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) (h : Fin ops.length → Code N sample) :
    programMass (Copy := Copy) N r K ops * (initial.bind (finiteHistoryLaw N r K ops)) h ≤
      (initial.bind (sourceHistoryLaw N r ops)) h := by
  simpa only [one_mul] using bind_scaled_domination initial initial
    (sourceHistoryLaw N r ops) (finiteHistoryLaw N r K ops) 1
    (programMass (Copy := Copy) N r K ops) (fun _ => by simp)
    (actual_history_domination N r K ops) h

theorem same_initial_history_tv (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) :
    pmfTV (initial.bind (sourceHistoryLaw N r ops))
      (initial.bind (finiteHistoryLaw N r K ops)) ≤
        1 - (programMass (Copy := Copy) N r K ops).toReal := by
  apply pmf_scaled_domination_tv
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K ops)
  · intro h
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ h)
      (same_initial_history_domination N r K ops initial h)

theorem same_initial_history_tv_budget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) :
    pmfTV (initial.bind (sourceHistoryLaw N r ops))
      (initial.bind (finiteHistoryLaw N r K ops)) ≤
        (ops.map (fun op => 1 - (stepMass (Copy := Copy) N r K op).toReal)).sum :=
  (same_initial_history_tv N r K ops initial).trans
    (program_deficit_le_sum (Copy := Copy) N r K ops)

theorem same_initial_joint_history_readout_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) (readout : (Fin ops.length → Code N sample) → O) :
    pmfTV ((initial.bind (sourceHistoryLaw N r ops)).map readout)
      ((initial.bind (finiteHistoryLaw N r K ops)).map readout) ≤
        1 - (programMass (Copy := Copy) N r K ops).toReal := by
  apply pmf_scaled_domination_tv
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K ops)
  · intro o
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ o)
      (map_scaled_domination _ _ _
        (same_initial_history_domination N r K ops initial) readout o)

/-- The old-past label and current state may be arbitrarily correlated.
Its conditional future kernel here is the same actual source kernel. Binding
an actual prior timed history to this interface remains a source-law task. -/
noncomputable def retainPast {Past : Type*}
    {S H : Type*} (initial : PMF (Past × S)) (future : S → PMF H) : PMF (Past × H) :=
  initial.bind (fun z => (future z.2).map (Prod.mk z.1))

theorem retained_past_history_domination {Past : Type*}
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Past × Code N sample)) (h : Past × (Fin ops.length → Code N sample)) :
    programMass (Copy := Copy) N r K ops *
        retainPast initial (finiteHistoryLaw N r K ops) h ≤
      retainPast initial (sourceHistoryLaw N r ops) h := by
  unfold retainPast
  simpa only [one_mul] using bind_scaled_domination initial initial
    (fun z => (sourceHistoryLaw N r ops z.2).map (Prod.mk z.1))
    (fun z => (finiteHistoryLaw N r K ops z.2).map (Prod.mk z.1))
    1 (programMass (Copy := Copy) N r K ops) (fun _ => by simp)
    (fun z h => map_scaled_domination _ _ _
      (actual_history_domination N r K ops z.2) (Prod.mk z.1) h) h

theorem retained_past_joint_history_tv {Past O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Past × Code N sample))
    (readout : (Past × (Fin ops.length → Code N sample)) → O) :
    pmfTV ((retainPast initial (sourceHistoryLaw N r ops)).map readout)
      ((retainPast initial (finiteHistoryLaw N r K ops)).map readout) ≤
        1 - (programMass (Copy := Copy) N r K ops).toReal := by
  apply pmf_scaled_domination_tv
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K ops)
  · intro o
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ o)
      (map_scaled_domination _ _ _
        (retained_past_history_domination N r K ops initial) readout o)

theorem retained_past_joint_history_tv_budget {Past O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Past × Code N sample))
    (readout : (Past × (Fin ops.length → Code N sample)) → O) :
    pmfTV ((retainPast initial (sourceHistoryLaw N r ops)).map readout)
      ((retainPast initial (finiteHistoryLaw N r K ops)).map readout) ≤
        (ops.map (fun op => 1 - (stepMass (Copy := Copy) N r K op).toReal)).sum :=
  (retained_past_joint_history_tv N r K ops initial readout).trans
    (program_deficit_le_sum (Copy := Copy) N r K ops)

#print axioms actual_history_domination
#print axioms same_initial_history_domination
#print axioms same_initial_history_tv
#print axioms same_initial_history_tv_budget
#print axioms same_initial_joint_history_readout_tv
#print axioms retained_past_history_domination
#print axioms retained_past_joint_history_tv
#print axioms retained_past_joint_history_tv_budget
end UnifiedLean.G6.HistoryPrefix
