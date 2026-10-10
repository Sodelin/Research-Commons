import G7SelectedKernelPolynomial
import G7OriginalInitializationPolynomial
import OriginalCalendarSchema
import Mathlib.Algebra.MvPolynomial.Rename

/-! One shared-bank polynomial table for a supplied original-ID symbolic word,
including its actual once-drawn original-register initialization. Interval slots
share the SAME physical rates on evaluation. No generated-calendar admission or
independence of segment-survival coordinates is assumed. -/
namespace GProgram.G7.SymbolicProgramPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.SelectedKernelPolynomial GProgram.G7.OriginalInitializationPolynomial
open scoped Classical BigOperators NNReal
variable {J V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev WordVariable (N : RootedBinary V E X) (J : Type*) := (J × Option E) ⊕ Hybrid N

noncomputable def instantiateGamma (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (dur : J → ℝ≥0) :
    Symbol J V E → ProgramStep N
  | .interval j => .interval (dur j)
  | .exit e => .boundary (.exit e)
  | .enter v => .boundary (originalNodeOperation N H gamma common v)

noncomputable def wordVariables (N : RootedBinary V E X) (r : PositivePairRates E)
    (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0) : WordVariable N J → ℝ
  | .inl (j,i) => Real.exp (-pairRate r i * (dur j : ℝ))
  | .inr h => (gamma h : ℝ)

noncomputable def wordEval (N : RootedBinary V E X) (r : PositivePairRates E)
    (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (p : MvPolynomial (WordVariable N J) ℚ) : ℝ :=
  MvPolynomial.eval₂ (Rat.castHom ℝ) (wordVariables N r gamma dur) p

noncomputable def stepPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (op : Symbol J V E)
    (a b : SelectedIndex N sample Finset.univ) : MvPolynomial (WordVariable N J) ℚ :=
  match op with
  | .interval j => MvPolynomial.rename (fun i => Sum.inl (j,i)) (epochTable N a b)
  | .exit e => exitTable N e a b
  | .enter v => MvPolynomial.rename Sum.inr (nodeTable N H common v a b)

theorem actual_step_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (op : Symbol J V E)
    (a b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E)
    (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0) :
    wordEval N r gamma dur (stepPolynomial N H common op a b) =
      (selectedProgramStep N r Finset.univ (instantiateGamma N H gamma common dur op) a b).toReal := by
  cases op with
  | interval j =>
    rw [stepPolynomial,wordEval,MvPolynomial.eval₂_rename]
    exact actual_selected_epoch_table N a b r (dur j)
  | exit e =>
    exact actual_selected_exit_table N (wordVariables N r gamma dur) e a b
  | enter v =>
    rw [stepPolynomial,wordEval,MvPolynomial.eval₂_rename]
    exact actual_selected_node_table N H common v a b gamma

noncomputable def wordPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) :
    List (Symbol J V E) → SelectedIndex N sample Finset.univ →
      SelectedIndex N sample Finset.univ → MvPolynomial (WordVariable N J) ℚ
  | [],a,b => if a = b then 1 else 0
  | op :: ops,a,b => ∑ c : SelectedIndex N sample Finset.univ,
      stepPolynomial N H common op a c * wordPolynomial N H common ops c b

theorem actual_word_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (word : List (Symbol J V E))
    (a b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E)
    (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0) :
    wordEval N r gamma dur (wordPolynomial N H common word a b) =
      (selectedProgram N r Finset.univ (word.map (instantiateGamma N H gamma common dur)) a b).toReal := by
  induction word generalizing a with
  | nil =>
    by_cases h : a = b
    · simp [wordPolynomial,wordEval,selectedProgram,PMF.pure_apply,h]
    · simp [wordPolynomial,wordEval,selectedProgram,PMF.pure_apply,h,Ne.symm h]
  | cons op ops ih =>
    rw [wordPolynomial]
    simp only [wordEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul]
    rw [List.map_cons,selectedProgram,bind_probability_real,tsum_fintype]
    apply Finset.sum_congr rfl
    intro c _
    exact congrArg₂ (fun x y : ℝ => x*y)
      (actual_step_polynomial N H common op a c r gamma dur) (ih c)

theorem actual_source_word_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (word : List (Symbol J V E))
    (s : Code N sample) (b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E)
    (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0) :
    wordEval N r gamma dur (wordPolynomial N H common word (projection N Finset.univ s) b) =
      (((sourceProgram N r (word.map (instantiateGamma N H gamma common dur)) s).map
        (projection N Finset.univ)) b).toReal := by
  rw [actual_source_program_projection]
  exact actual_word_polynomial N H common word _ b r gamma dur

noncomputable def initializedWordLaw (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (dur : J → ℝ≥0) (word : List (Symbol J V E)) : PMF (Code N sample) :=
  (originalRegisterPMF N p).bind (fun reg =>
    sourceProgram N r (word.map (instantiateGamma N H (originalGamma p) common dur))
      (initialCode N sample reg))

noncomputable def naturalWordPolynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (word : List (Symbol J V E))
    (b : SelectedIndex N sample Finset.univ) : MvPolynomial (WordVariable N J) ℚ :=
  ∑ a : SelectedIndex N sample Finset.univ,
    MvPolynomial.rename Sum.inr (initialPolynomial N sample a) * wordPolynomial N H common word a b

lemma initializedWordLaw_projected (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (dur : J → ℝ≥0) (word : List (Symbol J V E)) :
    (initializedWordLaw N sample H p common r dur word).map (projection N Finset.univ) =
      (((originalRegisterPMF N p).map (initialCode N sample)).map (projection N Finset.univ)).bind
        (selectedProgram N r Finset.univ (word.map (instantiateGamma N H (originalGamma p) common dur))) := by
  rw [initializedWordLaw,PMF.map_bind]
  simp_rw [actual_source_program_projection]
  simp [PMF.bind_map,Function.comp_def]

/-- One physical bank and one original register mixture serve the whole actual
supplied source word. The polynomial is independent of all bank values/durations. -/
theorem actual_natural_word_polynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (dur : J → ℝ≥0) (word : List (Symbol J V E))
    (b : SelectedIndex N sample Finset.univ) :
    wordEval N r (originalGamma p) dur (naturalWordPolynomial N sample H common word b) =
      (((initializedWordLaw N sample H p common r dur word).map (projection N Finset.univ)) b).toReal := by
  rw [initializedWordLaw_projected,bind_probability_real,tsum_fintype]
  simp only [naturalWordPolynomial,wordEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_rename]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg₂ (fun x y : ℝ => x*y)
    (actual_original_initial_polynomial N sample p a)
    (actual_word_polynomial N H common word a b r (originalGamma p) dur)

end GProgram.G7.SymbolicProgramPolynomial
