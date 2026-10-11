import G6SelectedBinHistory
import G7SymbolicProgramPolynomial
import NaturalCalendarPastAdmission

/-!
A finite polynomial consumer for the actual ranked-bin decoder. The state
retains the full selected source view AND the old bin matrix. One natural
initial-register mixture feeds the whole word. Accepted original step tables
supply all rows; no independent per-step source coordinates are presumed.
Contributor: dot / OpenAI, 10 October 2026. Uncompiled candidate.
-/
namespace UnifiedLean.G6.SelectedBinPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonExponential UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompatibility
open CloudG3.ActualObservationCutRefinement
open UnifiedLean.Source.SourceInitializedCalendar
open GProgram.G2.SourceFiniteHistory GProgram.G7.SymbolicProgramPolynomial
open GProgram.G7.OriginalInitializationPolynomial
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open UnifiedLean.G6.SelectedBinHistory
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualCalendarCutContext
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open CloudG6.NaturalCalendarPastAdmission
open scoped Classical BigOperators NNReal
variable {J V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Fintype Tag]

abbrev SelectedTagged (N : RootedBinary V E X) (sample : Copy → X) :=
  SelectedIndex N sample Finset.univ × (Copy → Copy → Tag)

/-- The exact endpoint decoder evaluated by conditional recursion. -/
noncomputable def selectedBinWordLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N × Tag) →
    SelectedTagged (Tag := Tag) N sample → PMF (SelectedTagged (Tag := Tag) N sample)
  | [],a => PMF.pure a
  | q::word,a => (selectedProgramStep N r Finset.univ q.1 a.1).bind (fun d =>
      selectedBinWordLaw N r word (d,selectedStepTags N q.1 q.2 a.1 d a.2))

/-- This recursion is the projection of the SAME full original endpoint
history, rather than a newly postulated process on selected states. -/
theorem actual_selected_history_fold (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (word : List (ProgramStep N × Tag))
    (s : Code N sample) (B : Copy → Copy → Tag) :
    ((sourceHistoryLaw N r (physicalOps N word) s).map
      (fun h => projectTagged N (endpointHistoryReadout N word s B h))) =
      selectedBinWordLaw N r word (projection N Finset.univ s,B) := by
  induction word generalizing s B with
  | nil =>
      change (GProgram.G2.SourceFiniteHistory.historyLaw (sourceProgramStep N r) [] s).map
        (fun _ => (projection N Finset.univ s,B)) = PMF.pure (projection N Finset.univ s,B)
      rw [GProgram.G2.SourceFiniteHistory.historyLaw,PMF.pure_map]
  | cons q word ih =>
      change (GProgram.G2.SourceFiniteHistory.historyLaw (sourceProgramStep N r)
        (q.1 :: physicalOps N word) s).map
          (fun h => projectTagged N (endpointHistoryReadout N (q::word) s B h)) =
        selectedBinWordLaw N r (q::word) (projection N Finset.univ s,B)
      rw [GProgram.G2.SourceFiniteHistory.historyLaw,PMF.map_bind]
      change (sourceProgramStep N r q.1 s).bind (fun d =>
        ((sourceHistoryLaw N r (physicalOps N word) d).map (Fin.cons d)).map
          (fun h : Fin ((physicalOps N word).length+1) → Code N sample =>
            projectTagged N (endpointHistoryReadout N word (h 0)
              (endpointStepTags N q.1 q.2 s (h 0) B) (Fin.tail h)))) = _
      simp only [PMF.map_comp,Function.comp_def,Fin.cons_zero,Fin.tail_cons]
      simp_rw [ih,←actual_step_tags_project N q.1 q.2 s]
      change (sourceProgramStep N r q.1 s).bind
        ((fun d => selectedBinWordLaw N r word
          (d,selectedStepTags N q.1 q.2 (projection N Finset.univ s) d B)) ∘
            projection N Finset.univ) = _
      rw [←PMF.bind_map,actual_program_step_projection]
      rfl

noncomputable def symbolicStepTags (N : RootedBinary V E X) {sample : Copy → X}
    (op : Symbol J V E) (tag : Tag) (a d : SelectedIndex N sample Finset.univ)
    (B : Copy → Copy → Tag) : Copy → Copy → Tag := match op with
  | .interval _ => selectedTagUpdate N a d tag B
  | .exit _ => B
  | .enter _ => B

lemma actual_symbolic_step_tags (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dur : J → ℝ≥0) (op : Symbol J V E)
    (tag : Tag) (a d : SelectedIndex N sample Finset.univ) (B : Copy → Copy → Tag) :
    selectedStepTags N (instantiateGamma N H gamma common dur op) tag a d B =
      symbolicStepTags N op tag a d B := by
  cases op <;> rfl

noncomputable def instantiateTagged (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dur : J → ℝ≥0) (word : List (Symbol J V E × Tag)) :
    List (ProgramStep N × Tag) :=
  word.map (fun q => (instantiateGamma N H gamma common dur q.1,q.2))

noncomputable def binWordPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) :
    List (Symbol J V E × Tag) → SelectedTagged (Tag := Tag) N sample →
      SelectedTagged (Tag := Tag) N sample → MvPolynomial (WordVariable N J) ℚ
  | [],a,b => if a=b then 1 else 0
  | q::word,a,b => ∑ d : SelectedIndex N sample Finset.univ,
      stepPolynomial N H common q.1 a.1 d *
        binWordPolynomial N H common word (d,symbolicStepTags N q.1 q.2 a.1 d a.2) b

/-- The unchanged original epoch and boundary polynomial rows are composed
with deterministic old-bin updates. All physical rates and gammas stay shared. -/
theorem actual_bin_word_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E × Tag)) (a b : SelectedTagged (Tag := Tag) N sample)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0) :
    wordEval N r gamma dur (binWordPolynomial N H common word a b) =
      (selectedBinWordLaw N r (instantiateTagged N H gamma common dur word) a b).toReal := by
  induction word generalizing a with
  | nil =>
      by_cases h : a=b
      · simp [binWordPolynomial,wordEval,instantiateTagged,selectedBinWordLaw,PMF.pure_apply,h]
      · simp [binWordPolynomial,wordEval,instantiateTagged,selectedBinWordLaw,PMF.pure_apply,h,Ne.symm h]
  | cons q word ih =>
      rw [binWordPolynomial]
      simp only [wordEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul]
      change _ = ((selectedProgramStep N r Finset.univ
        (instantiateGamma N H gamma common dur q.1) a.1).bind _ b).toReal
      rw [bind_probability_real,tsum_fintype]
      apply Finset.sum_congr rfl
      intro d _
      rw [actual_symbolic_step_tags]
      exact congrArg₂ (fun x y : ℝ => x*y)
        (actual_step_polynomial N H common q.1 a.1 d r gamma dur) (ih _)

noncomputable def naturalBinWordLaw (N : RootedBinary V E X) (sample : Copy → X)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (word : List (ProgramStep N × Tag)) (B : Copy → Copy → Tag) :
    PMF (SelectedTagged (Tag := Tag) N sample) :=
  ((naturalInitialCodeLaw N sample p).map (projection N Finset.univ)).bind
    (fun a => selectedBinWordLaw N r word (a,B))

noncomputable def naturalBinPolynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E × Tag)) (B : Copy → Copy → Tag)
    (b : SelectedTagged (Tag := Tag) N sample) : MvPolynomial (WordVariable N J) ℚ :=
  ∑ a : SelectedIndex N sample Finset.univ,
    MvPolynomial.rename Sum.inr (initialPolynomial N sample a) *
      binWordPolynomial N H common word (a,B) b

/-- Exactly one original-register draw supplies all subsequent COMMON reads. -/
theorem actual_natural_bin_polynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (dur : J → ℝ≥0) (word : List (Symbol J V E × Tag))
    (B : Copy → Copy → Tag) (b : SelectedTagged (Tag := Tag) N sample) :
    wordEval N r (originalGamma p) dur (naturalBinPolynomial N sample H common word B b) =
      (naturalBinWordLaw N sample p r
        (instantiateTagged N H (originalGamma p) common dur word) B b).toReal := by
  rw [naturalBinWordLaw,bind_probability_real,tsum_fintype]
  simp only [naturalBinPolynomial,wordEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_rename]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg₂ (fun x y : ℝ => x*y)
    (actual_original_initial_polynomial N sample p a)
    (actual_bin_word_polynomial N H common word (a,B) b r (originalGamma p) dur)

section ActualCalendar
variable [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

/-- This law is the projection of the actual naturally initialized clock past.
The legal cut/bin contracts refer to literal source operations, not law fields. -/
theorem actual_natural_past_selected_fold (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C)) :
    (naturalPastJoint N C sample p r bin hbin ops).map (projectTagged N) =
      naturalBinWordLaw N sample p r word (fun x y => bin (leafAgeMatrix N C sample x y)) := by
  rw [actual_natural_past_endpoint_history N C sample p r bin hbin ops word href hword,
    PMF.map_comp]
  unfold initializedEndpointLaw
  rw [PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def]
  simp_rw [actual_selected_history_fold]
  rw [naturalBinWordLaw,PMF.bind_map]
  rfl

/-- Actual clock-bin polynomial for an instantiated original-ID word. A
calendar-cell adapter supplies these grammar contracts and initial bin matrix. -/
theorem actual_natural_clock_bin_polynomial (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (dur : J → ℝ≥0) (word : List (Symbol J V E × Tag))
    (href : CutRefines N ops
      (physicalOps N (instantiateTagged N H (originalGamma p) common dur word)))
    (hword : wordBinContract N bin (instantiateTagged N H (originalGamma p) common dur word)
      (firstOriginalDate N C)) (b : SelectedTagged (Tag := Tag) N sample) :
    wordEval N r (originalGamma p) dur (naturalBinPolynomial N sample H common word
      (fun x y => bin (leafAgeMatrix N C sample x y)) b) =
      (((naturalPastJoint N C sample p r bin hbin ops).map (projectTagged N)) b).toReal := by
  rw [actual_natural_past_selected_fold N C sample p r bin hbin ops _ href hword]
  exact actual_natural_bin_polynomial N sample H p common r dur word _ b

end ActualCalendar
#print axioms actual_selected_history_fold
#print axioms actual_bin_word_polynomial
#print axioms actual_natural_bin_polynomial
#print axioms actual_natural_past_selected_fold
#print axioms actual_natural_clock_bin_polynomial
end UnifiedLean.G6.SelectedBinPolynomial
