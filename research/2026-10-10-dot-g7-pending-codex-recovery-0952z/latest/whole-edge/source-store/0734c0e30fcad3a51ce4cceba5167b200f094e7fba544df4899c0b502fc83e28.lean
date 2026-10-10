import G7SymbolicProgramPolynomial
import UnifiedLean.Source.ControlledUnrankedSourceProjectivity

/-! Fixed ORIGINAL-ID mask substitution into source transition rows. The natural
once-drawn register mixture is outside this substitution and stays unchanged.
Forced sites use the inherited controlledMode, hence actual deterministic
current-owner routing, while unforced COMMON registers are preserved. -/
namespace GProgram.G7.ControlledWordPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonExponential UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.OriginalInitializationPolynomial
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open scoped Classical BigOperators NNReal
variable {J V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def controlVariable (N : RootedBinary V E X) (mask : OriginalMask N) :
    WordVariable N J → MvPolynomial (WordVariable N J) ℚ
  | .inl i => MvPolynomial.X (.inl i)
  | .inr h => match mask h with
    | none => MvPolynomial.X (.inr h)
    | some b => if b then 1 else 0

noncomputable def substituteControl (N : RootedBinary V E X) (mask : OriginalMask N)
    (q : MvPolynomial (WordVariable N J) ℚ) : MvPolynomial (WordVariable N J) ℚ :=
  MvPolynomial.eval₂ MvPolynomial.C (controlVariable N mask) q

lemma controlVariable_eval (N : RootedBinary V E X) (p : HybridProbabilities N)
    (mask : OriginalMask N) (r : PositivePairRates E) (dur : J → ℝ≥0)
    (i : WordVariable N J) :
    wordEval N r (originalGamma p) dur (controlVariable N mask i) =
      wordVariables N r (controlledGamma p mask) dur i := by
  cases i with
  | inl i => simp [controlVariable,wordEval,wordVariables]
  | inr h =>
    cases hm : mask h with
    | none => simp [controlVariable,hm,wordEval,wordVariables,controlledGamma]
    | some b => cases b <;>
        simp [controlVariable,hm,wordEval,wordVariables,controlledGamma,forcedParameter]

lemma substituteControl_eval (N : RootedBinary V E X) (p : HybridProbabilities N)
    (mask : OriginalMask N) (r : PositivePairRates E) (dur : J → ℝ≥0)
    (q : MvPolynomial (WordVariable N J) ℚ) :
    wordEval N r (originalGamma p) dur (substituteControl N mask q) =
      wordEval N r (controlledGamma p mask) dur q := by
  unfold substituteControl wordEval
  rw [← MvPolynomial.eval₂_assoc]
  congr 1
  funext i
  exact controlVariable_eval N p mask r dur i

noncomputable def controlledWordLaw (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (mask : OriginalMask N) (r : PositivePairRates E) (dur : J → ℝ≥0)
    (word : List (Symbol J V E)) : PMF (Code N sample) :=
  (originalRegisterPMF N p).bind (fun reg =>
    sourceProgram N r (word.map (instantiateGamma N H (controlledGamma p mask)
      (controlledMode common mask) dur)) (initialCode N sample reg))

noncomputable def controlledWordPolynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (mask : OriginalMask N)
    (word : List (Symbol J V E)) (b : SelectedIndex N sample Finset.univ) :
    MvPolynomial (WordVariable N J) ℚ :=
  ∑ a : SelectedIndex N sample Finset.univ,
    MvPolynomial.rename Sum.inr (initialPolynomial N sample a) *
      substituteControl N mask (wordPolynomial N H (controlledMode common mask) word a b)

lemma controlledWordLaw_projected (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (mask : OriginalMask N) (r : PositivePairRates E) (dur : J → ℝ≥0)
    (word : List (Symbol J V E)) :
    (controlledWordLaw N sample H p common mask r dur word).map (projection N Finset.univ) =
      (((originalRegisterPMF N p).map (initialCode N sample)).map (projection N Finset.univ)).bind
        (selectedProgram N r Finset.univ (word.map (instantiateGamma N H (controlledGamma p mask)
          (controlledMode common mask) dur))) := by
  rw [controlledWordLaw,PMF.map_bind]
  simp_rw [actual_source_program_projection]
  simp [PMF.bind_map,Function.comp_def]

/-- Evaluation retains natural gamma for initialization and substitutes only
forced transition nodes. This covers every actual original mask and bank. -/
theorem actual_controlled_word_polynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (mask : OriginalMask N) (r : PositivePairRates E) (dur : J → ℝ≥0)
    (word : List (Symbol J V E)) (b : SelectedIndex N sample Finset.univ) :
    wordEval N r (originalGamma p) dur (controlledWordPolynomial N sample H common mask word b) =
      (((controlledWordLaw N sample H p common mask r dur word).map
        (projection N Finset.univ)) b).toReal := by
  rw [controlledWordLaw_projected,bind_probability_real,tsum_fintype]
  simp only [controlledWordPolynomial,wordEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_rename]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg₂ (fun x y : ℝ => x*y)
  · exact actual_original_initial_polynomial N sample p a
  · change wordEval N r (originalGamma p) dur (substituteControl N mask _) = _
    rw [substituteControl_eval]
    exact actual_word_polynomial N H (controlledMode common mask) word a b r
      (controlledGamma p mask) dur

end GProgram.G7.ControlledWordPolynomial
