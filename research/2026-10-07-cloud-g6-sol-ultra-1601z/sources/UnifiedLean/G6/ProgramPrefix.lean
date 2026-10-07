import UnifiedLean.G6.SourcePrefix
import UnifiedLean.Source.SourceProgramTransport

/-!
Product domination for actual finite source programs and the SAME initial
distribution of unranked genealogy/population/register snapshots. COMMON registers are retained
by unchanged boundaryKernel; no epoch redraw is introduced. This does not
identify an arbitrary program or endpoint map with a physical timed-bin menu.
-/
namespace UnifiedLean.G6.ProgramPrefix
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.Conditioning UnifiedLean.G6.FiniteProbability UnifiedLean.G6.SourcePrefix
open scoped Classical NNReal ENNReal BigOperators

theorem bind_scaled_domination {A B : Type*}
    (p q : PMF A) (f g : A → PMF B) (mu nu : ℝ≥0∞)
    (hp : ∀ a, mu * q a ≤ p a) (hf : ∀ a b, nu * g a b ≤ f a b) (b : B) :
    (mu * nu) * (q.bind g) b ≤ (p.bind f) b := by
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro a
  calc
    (mu * nu) * (q a * g a b) = (mu * q a) * (nu * g a b) := by ac_rfl
    _ ≤ p a * f a b := mul_le_mul' (hp a) (hf a b)

theorem map_scaled_domination {A B : Type*}
    (p q : PMF A) (mu : ℝ≥0∞) (hp : ∀ a, mu * q a ≤ p a)
    (readout : A → B) (b : B) : mu * (q.map readout) b ≤ (p.map readout) b := by
  simpa only [mul_one, PMF.bind_pure_comp] using
    bind_scaled_domination p q (PMF.pure ∘ readout) (PMF.pure ∘ readout)
      mu 1 hp (fun _ _ => by simp) b

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def stepMass (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) : ProgramStep N → ℝ≥0∞
  | .interval t => retainedMass (countPMF (globalClockRate (Copy := Copy) r * t))
      (Finset.range (K + 1) : Set ℕ)
  | .boundary _ => 1

noncomputable def programMass {Copy : Type*} [DecidableEq Copy] [Fintype Copy]
    (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) : List (ProgramStep N) → ℝ≥0∞
  | [] => 1
  | op :: ops => stepMass (Copy := Copy) N r K op * programMass (Copy := Copy) N r K ops

noncomputable def finiteProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (op : ProgramStep N) (s : Code N sample) : PMF (Code N sample) :=
  match op with
  | .interval t => finiteSourcePrefix N r t K s
  | .boundary b => sourceProgramStep N r (.boundary b) s

noncomputable def finiteProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) : List (ProgramStep N) → Code N sample → PMF (Code N sample)
  | [], s => PMF.pure s
  | op :: ops, s => (finiteProgramStep N r K op s).bind (finiteProgram N r K ops)

lemma stepMass_le_one (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) (op : ProgramStep N) : stepMass (Copy := Copy) N r K op ≤ 1 := by
  cases op with
  | interval t => exact retainedMass_le_one _ _
  | boundary b => exact le_rfl

lemma programMass_le_one (N : RootedBinary V E X) (r : PositivePairRates E)
    (K : ℕ) (ops : List (ProgramStep N)) : programMass (Copy := Copy) N r K ops ≤ 1 := by
  induction ops with
  | nil => exact le_rfl
  | cons op ops ih =>
      change stepMass (Copy := Copy) N r K op * programMass (Copy := Copy) N r K ops ≤ 1
      exact (mul_le_mul' (stepMass_le_one (Copy := Copy) N r K op) ih).trans (by simp)

lemma actual_step_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (op : ProgramStep N) (s d : Code N sample) :
    stepMass (Copy := Copy) N r K op * finiteProgramStep N r K op s d ≤
      sourceProgramStep N r op s d := by
  cases op with
  | interval t =>
      exact filtered_bind_domination _ _ (prefix_has_support _ K)
        (fun k => sourceIteration N r k s) d
  | boundary b => simp only [stepMass, finiteProgramStep, one_mul, le_refl]

theorem actual_program_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N)) (s d : Code N sample) :
    programMass (Copy := Copy) N r K ops * finiteProgram N r K ops s d ≤ sourceProgram N r ops s d := by
  induction ops generalizing s d with
  | nil => simp only [programMass, finiteProgram, sourceProgram, one_mul, le_refl]
  | cons op ops ih =>
      change (stepMass (Copy := Copy) N r K op * programMass (Copy := Copy) N r K ops) *
        ((finiteProgramStep N r K op s).bind (finiteProgram N r K ops)) d ≤
        ((sourceProgramStep N r op s).bind (sourceProgram N r ops)) d
      exact bind_scaled_domination _ _ _ _ _ _ (actual_step_domination N r K op s) ih d

theorem same_initial_distribution_domination (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) (d : Code N sample) :
    programMass (Copy := Copy) N r K ops * (initial.bind (finiteProgram N r K ops)) d ≤
      (initial.bind (sourceProgram N r ops)) d := by
  simpa only [one_mul] using bind_scaled_domination initial initial
    (sourceProgram N r ops) (finiteProgram N r K ops) 1 (programMass (Copy := Copy) N r K ops)
    (fun _ => by simp) (actual_program_domination N r K ops) d

theorem same_initial_distribution_tv (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N)) (initial : PMF (Code N sample)) :
    pmfTV (initial.bind (sourceProgram N r ops)) (initial.bind (finiteProgram N r K ops)) ≤
      1 - (programMass (Copy := Copy) N r K ops).toReal := by
  apply pmf_scaled_domination_tv
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K ops)
  · intro d
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ d)
      (same_initial_distribution_domination N r K ops initial d)

theorem same_initial_joint_readout_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) (readout : Code N sample → O) :
    pmfTV ((initial.bind (sourceProgram N r ops)).map readout)
      ((initial.bind (finiteProgram N r K ops)).map readout) ≤
      1 - (programMass (Copy := Copy) N r K ops).toReal := by
  apply pmf_scaled_domination_tv
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K ops)
  · intro o
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ o)
      (map_scaled_domination _ _ _
        (same_initial_distribution_domination N r K ops initial) readout o)

theorem same_initial_joint_readout_event {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (K : ℕ) (ops : List (ProgramStep N))
    (initial : PMF (Code N sample)) (readout : Code N sample → O) (event : Finset O) :
    |(∑ o ∈ event, (((initial.bind (sourceProgram N r ops)).map readout) o).toReal) -
      ∑ o ∈ event, (((initial.bind (finiteProgram N r K ops)).map readout) o).toReal| ≤
      1 - (programMass (Copy := Copy) N r K ops).toReal := by
  apply pmf_scaled_domination_event
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (programMass_le_one (Copy := Copy) N r K ops)
  · intro o
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ o)
      (map_scaled_domination _ _ _
        (same_initial_distribution_domination N r K ops initial) readout o)

#print axioms bind_scaled_domination
#print axioms map_scaled_domination
#print axioms actual_step_domination
#print axioms actual_program_domination
#print axioms same_initial_distribution_domination
#print axioms same_initial_distribution_tv
#print axioms same_initial_joint_readout_tv
#print axioms same_initial_joint_readout_event
end UnifiedLean.G6.ProgramPrefix
