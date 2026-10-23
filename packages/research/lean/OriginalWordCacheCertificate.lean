import OriginalWordTableCertificate
import G7SparseWordComposition
import NativePopulationTableCertificate

/-! Finite checked primitive-row cache for the SAME original natural word.
Existing stepRows/polynomial_stepRows, initialRows and followRows are reused.
Cache hits preserve the COMPLETE selected entering view, including the SAME
original register; misses use the unchanged original constructive step.
No desired step/word law is assumed. Every cache entry carries its Boolean
total-fibre check. This changes proof evaluation strategy, not source class,
Copy cap, operations, physical bank or observation. -/
set_option autoImplicit false
namespace Astra.OriginalWordCacheCertificate
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectivePopulationCoefficients GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.EffectiveInitializationCoefficients
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.SymbolicProgramPolynomial
open GProgram.G7.SparseRowProducts GProgram.G7.SparseWordComposition
open GProgram.G7.FullEpochSupport GProgram.G7.FullEpochPolynomial
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.PopulationSelectedSupport
open GProgram.G7.SelectedEpochTableUniqueness GProgram.G7.SelectedKernelPolynomial
open Astra.NativeSparseTableCertificate
open scoped BigOperators NNReal

variable {J Native V E X Copy : Type*}
variable [DecidableEq J] [Fintype J] [DecidableEq Native] [Fintype Native]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

local instance (N : RootedBinary V E X) : DecidablePred N.graph.IsHybrid :=
  hybridDecidable N

def symbolEq : Symbol J V E → Symbol J V E → Bool
  | .interval a, .interval b => decide (a = b)
  | .exit a, .exit b => decide (a = b)
  | .enter a, .enter b => decide (a = b)
  | _, _ => false

@[simp] theorem symbolEq_eq_true (a b : Symbol J V E) :
    symbolEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [symbolEq]

/-- The inherited single-epoch uniqueness receiver applies to ANY complete
active population list. Empty original populations need not be expanded.
No calendar-slot independence or new source polynomial is assumed. -/
theorem active_fullRows_eq_epochTable (N : RootedBinary V E X) {sample : Copy → X}
    (todo : List (Option E)) (s : Code N sample) (hs : ActiveIn N s todo.toFinset)
    (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (fullRows N todo Copy sample s) b) =
      epochTable N (project N Finset.univ s) b := by
  apply polynomial_eq_of_single_epoch_evaluations
  intro r
  change MvPolynomial.eval₂ (Rat.castHom ℝ) (survival r 1)
      (polynomial (readRows (project N Finset.univ) (fullRows N todo Copy sample s) b)) = _
  rw [eval_polynomial, fullRows_actual N todo s hs b r 1,
    constructed_source_time_kernel_projection, project_eq]
  exact (actual_selected_epoch_table N (projection N Finset.univ s) b r 1).symm

/-- The scalar coefficients are the unchanged population certificate's literal
Expr table. Repeated raw Code destinations still contribute their entire sum. -/
def embedPopulationRows (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (rows : Astra.NativePopulationTableCertificate.Table N sample) :
    Rows (Option E) (Code N sample) :=
  rows.map fun row => (row.1, embedExpr i row.2)

lemma population_exprPolynomial_append (p q : Expr) :
    exprPolynomial (p ++ q) = exprPolynomial p + exprPolynomial q := by
  simp only [exprPolynomial, List.map_append, List.sum_append]

lemma population_collect_eval (N : RootedBinary V E X) {sample : Copy → X}
    (rows : Astra.NativePopulationTableCertificate.Table N sample)
    (d : Code N sample) (x : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) x
      (exprPolynomial (Astra.NativePopulationTableCertificate.collect rows d)) =
      (rows.map fun row => if row.1 = d then
        Polynomial.eval₂ (Rat.castHom ℝ) x (exprPolynomial row.2) else 0).sum := by
  induction rows with
  | nil => simp [Astra.NativePopulationTableCertificate.collect, exprPolynomial]
  | cons row rows ih =>
      change Polynomial.eval₂ (Rat.castHom ℝ) x
        (exprPolynomial ((if row.1 = d then row.2 else []) ++
          Astra.NativePopulationTableCertificate.collect rows d)) = _
      rw [population_exprPolynomial_append, Polynomial.eval₂_add, ih]
      by_cases h : row.1 = d <;> simp [h, exprPolynomial]

/-- Scalar total-fibre certificate -> actual selected whole population row.
No full Code carrier is enumerated by either Boolean checker. The finite
sum here is semantic pushforward algebra, not an executable state oracle. -/
theorem checked_population_rows_value (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (rows : Astra.NativePopulationTableCertificate.Table N sample)
    (h : Astra.NativePopulationTableCertificate.check N (Fintype.card Copy) s rows = true)
    (b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) (t : ℝ≥0) :
    value (readRows (project N Finset.univ) (embedPopulationRows N i rows) b)
      (survival r t) =
        (((sourceTimeKernel N r t s).map (projection N Finset.univ)) b).toReal := by
  classical
  let ev : Expr → ℝ := fun p =>
    Polynomial.eval₂ (Rat.castHom ℝ) (survival r t i) (exprPolynomial p)
  have hv (d : Code N sample) :
      ev (Astra.NativePopulationTableCertificate.collect rows d) =
        (sourceTimeKernel N r t s d).toReal :=
    Astra.NativePopulationTableCertificate.checked_actual_population N s rows h d i hs r t
  calc
    _ = (rows.map fun row => ev row.2 *
        (if project N Finset.univ row.1 = b then 1 else 0)).sum := by
      simp only [embedPopulationRows, readRows, List.flatMap_map, value_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro row _
      by_cases hb : project N Finset.univ row.1 = b
      · simp only [hb, if_pos, mul_one]
        exact value_embedExpr i row.2 r t
      · simp only [hb, if_neg, mul_zero, value_nil]
    _ = ∑ d : Code N sample,
        ev (Astra.NativePopulationTableCertificate.collect rows d) *
          (if project N Finset.univ d = b then 1 else 0) := by
      rw [sum_partition rows (fun row => row.1) (fun row => ev row.2)
        (fun d => if project N Finset.univ d = b then 1 else 0)]
      apply Finset.sum_congr rfl
      intro d _
      rw [show ev (Astra.NativePopulationTableCertificate.collect rows d) =
        (rows.map fun row => if row.1 = d then ev row.2 else 0).sum from
          population_collect_eval N rows d (survival r t i)]
    _ = _ := by
      simp_rw [hv, project_eq]
      rw [map_probability_real]

/-- An interval can reuse the existing complete active-panel row or, when
ACTUAL input colocation is proved, the existing scalar population checker. -/
inductive IntervalForm (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample)
  | active (todo : List (Option E)) (complete : ActiveIn N s todo.toFinset)
  | colocated (i : Option E) (at_population : CoLocated N s i)
      (rows : Astra.NativePopulationTableCertificate.Table N sample)

def intervalRows (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :
    IntervalForm N s → Rows (Option E) (Code N sample)
  | .active todo _ => fullRows N todo Copy sample s
  | .colocated i _ rows => embedPopulationRows N i rows

def checkInterval (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :
    IntervalForm N s → Bool
  | .active _ _ => true
  | .colocated _ _ rows =>
      Astra.NativePopulationTableCertificate.check N (Fintype.card Copy) s rows

theorem checked_interval_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (form : IntervalForm N s) (h : checkInterval N s form = true)
    (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (intervalRows N s form) b) =
      epochTable N (project N Finset.univ s) b := by
  cases form with
  | active todo hs => exact active_fullRows_eq_epochTable N todo s hs b
  | colocated i hs rows =>
      apply polynomial_eq_of_single_epoch_evaluations
      intro r
      change MvPolynomial.eval₂ (Rat.castHom ℝ) (survival r 1)
          (polynomial (readRows (project N Finset.univ) (embedPopulationRows N i rows) b)) = _
      rw [eval_polynomial, checked_population_rows_value N s i hs rows h b r 1,
        constructed_source_time_kernel_projection, project_eq]
      exact (actual_selected_epoch_table N (projection N Finset.univ s) b r 1).symm

structure StepEntry (N : RootedBinary V E X) (sample : Copy → X)
    (Native J : Type*) where
  operation : Symbol J V E
  input : Code N sample
  rows : Rows Native (Code N sample)
  interval : IntervalForm N input

def referenceStepRows (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native) (e : StepEntry N sample Native J) :
    Rows Native (Code N sample) :=
  match e.operation with
  | .interval j => renameRows encode (renameRows (fun i => Sum.inl (j,i))
      (intervalRows N e.input e.interval))
  | op => renameRows encode (stepRows N H common op e.input)

def checkStep (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native) (e : StepEntry N sample Native J) : Bool :=
  match e.operation with
  | .interval _ => checkInterval N e.input e.interval &&
      checkRows (project N Finset.univ) (referenceStepRows N sample H common encode e) e.rows
  | _ => checkRows (project N Finset.univ) (referenceStepRows N sample H common encode e) e.rows

lemma bool_and_components (a b : Bool) (h : a && b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem checked_reference_step_polynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native) (e : StepEntry N sample Native J)
    (h : checkStep N sample H common encode e = true)
    (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) e.rows b) =
      MvPolynomial.rename encode
        (stepPolynomial N H common e.operation (project N Finset.univ e.input) b) := by
  cases hop : e.operation with
  | interval j =>
      have hh : checkInterval N e.input e.interval &&
          checkRows (project N Finset.univ) (referenceStepRows N sample H common encode e) e.rows = true := by
        simpa only [checkStep, hop] using h
      obtain ⟨hf, hc⟩ := bool_and_components _ _ hh
      have heq := checkRows_sound (project N Finset.univ)
        (referenceStepRows N sample H common encode e) e.rows hc b
      simp only [referenceStepRows, hop, polynomial_read_renameRows] at heq
      rw [checked_interval_polynomial N e.input e.interval hf b] at heq
      simpa only [hop, stepPolynomial] using heq.symm
  | exit edge =>
      have hc : checkRows (project N Finset.univ)
          (referenceStepRows N sample H common encode e) e.rows = true := by
        simpa only [checkStep, hop] using h
      have heq := checkRows_sound (project N Finset.univ)
        (referenceStepRows N sample H common encode e) e.rows hc b
      simp only [referenceStepRows, hop, polynomial_read_renameRows, polynomial_stepRows] at heq
      simpa only [hop] using heq.symm
  | enter vertex =>
      have hc : checkRows (project N Finset.univ)
          (referenceStepRows N sample H common encode e) e.rows = true := by
        simpa only [checkStep, hop] using h
      have heq := checkRows_sound (project N Finset.univ)
        (referenceStepRows N sample H common encode e) e.rows hc b
      simp only [referenceStepRows, hop, polynomial_read_renameRows, polynomial_stepRows] at heq
      simpa only [hop] using heq.symm

structure CertifiedStep (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native) where
  entry : StepEntry N sample Native J
  checked : checkStep N sample H common encode entry = true

def cachedStep (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native) :
    List (CertifiedStep N sample H common encode) →
      Symbol J V E → Code N sample → Rows Native (Code N sample)
  | [], op, s => renameRows encode (stepRows N H common op s)
  | e :: rest, op, s =>
      if symbolEq e.entry.operation op &&
          decide (project N Finset.univ e.entry.input = project N Finset.univ s)
      then e.entry.rows else cachedStep N sample H common encode rest op s

theorem certified_step_polynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native)
    (e : CertifiedStep N sample H common encode)
    (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) e.entry.rows b) =
      MvPolynomial.rename encode
        (stepPolynomial N H common e.entry.operation (project N Finset.univ e.entry.input) b) :=
  checked_reference_step_polynomial N sample H common encode e.entry e.checked b

/-- Full selected-view equality is sufficient by the EXISTING exact step
polynomial. This is not a quotient by an observed forest or private bit. -/
theorem cached_step_polynomial (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native)
    (cache : List (CertifiedStep N sample H common encode))
    (op : Symbol J V E) (s : Code N sample)
    (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ)
      (cachedStep N sample H common encode cache op s) b) =
        MvPolynomial.rename encode (stepPolynomial N H common op (project N Finset.univ s) b) := by
  induction cache with
  | nil =>
      simp only [cachedStep, polynomial_read_renameRows, polynomial_stepRows]
  | cons e rest ih =>
      dsimp only [cachedStep]
      split
      · rename_i hit
        have hm : symbolEq e.entry.operation op = true ∧
            decide (project N Finset.univ e.entry.input = project N Finset.univ s) = true := by
          cases ha : symbolEq e.entry.operation op <;>
            cases hb : decide (project N Finset.univ e.entry.input = project N Finset.univ s) <;>
              simp_all
        have hop := (symbolEq_eq_true e.entry.operation op).mp hm.1
        have hs : project N Finset.univ e.entry.input = project N Finset.univ s :=
          of_decide_eq_true hm.2
        simpa only [hop, hs] using certified_step_polynomial N sample H common encode e b
      · exact ih

theorem eval_rename_bank (N : RootedBinary V E X)
    (encode : WordVariable N J → Native) (decode : Native → WordVariable N J)
    (hleft : Function.LeftInverse decode encode)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (q : MvPolynomial (WordVariable N J) ℚ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) (fun i => wordVariables N r gamma dur (decode i))
      (MvPolynomial.rename encode q) = wordEval N r gamma dur q := by
  have hx : (fun i => wordVariables N r gamma dur (decode i)) ∘ encode =
      wordVariables N r gamma dur := by
    funext i
    exact congrArg (wordVariables N r gamma dur) (hleft i)
  rw [MvPolynomial.eval₂_rename, hx]
  rfl

theorem cached_step_value (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native) (decode : Native → WordVariable N J)
    (hleft : Function.LeftInverse decode encode)
    (cache : List (CertifiedStep N sample H common encode))
    (op : Symbol J V E) (s : Code N sample)
    (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0) :
    value (readRows (project N Finset.univ)
      (cachedStep N sample H common encode cache op s) b)
        (fun i => wordVariables N r gamma dur (decode i)) =
      (selectedProgramStep N r Finset.univ (instantiateGamma N H gamma common dur op)
        (project N Finset.univ s) b).toReal := by
  rw [← eval_polynomial, cached_step_polynomial,
    eval_rename_bank N encode decode hleft r gamma dur]
  exact actual_step_polynomial N H common op (project N Finset.univ s) b r gamma dur

/-- The original sparse-word composition proof, with an arbitrary finite
coordinate carrier. The public final receiver DERIVES its step premise above. -/
theorem native_follow_value (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (step : Symbol J V E → Code N sample → Rows Native (Code N sample))
    (x : Native → ℝ)
    (hstep : ∀ op s b,
      value (readRows (project N Finset.univ) (step op s) b) x =
        (selectedProgramStep N r Finset.univ (instantiateGamma N H gamma common dur op)
          (project N Finset.univ s) b).toReal)
    (word : List (Symbol J V E)) (s : Code N sample)
    (b : SelectedIndex N sample Finset.univ) :
    value (readRows (project N Finset.univ) (followRows step word s) b) x =
      (selectedProgram N r Finset.univ (word.map (instantiateGamma N H gamma common dur))
        (project N Finset.univ s) b).toReal := by
  classical
  induction word generalizing s with
  | nil =>
      by_cases h : project N Finset.univ s = b
      · simp [followRows, readRows, single, value, selectedProgram, PMF.pure_apply, h]
      · simp [followRows, readRows, single, value, selectedProgram, PMF.pure_apply, h, Ne.symm h]
  | cons op ops ih =>
      rw [followRows, value_read_bindRows]
      simp_rw [ih]
      rw [sum_partition (step op s) (fun row => project N Finset.univ row.1)
        (fun row => value row.2 x)
        (fun c => (selectedProgram N r Finset.univ
          (ops.map (instantiateGamma N H gamma common dur)) c b).toReal)]
      rw [List.map_cons, selectedProgram, bind_probability_real, tsum_fintype]
      apply Finset.sum_congr rfl
      intro c _
      rw [← value_readRows, hstep]

def checkInitial (N : RootedBinary V E X) (sample : Copy → X)
    (encode : WordVariable N J → Native) (rows : Rows Native (Code N sample)) : Bool :=
  checkRows (project N Finset.univ) (initialRows N sample (fun h => encode (.inr h))) rows

structure CertifiedInitial (N : RootedBinary V E X) (sample : Copy → X)
    (encode : WordVariable N J → Native) where
  rows : Rows Native (Code N sample)
  checked : checkInitial N sample encode rows = true

theorem initial_value (N : RootedBinary V E X) (sample : Copy → X)
    (encode : WordVariable N J → Native) (decode : Native → WordVariable N J)
    (hleft : Function.LeftInverse decode encode)
    (initial : CertifiedInitial N sample encode)
    (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates E) (p : HybridProbabilities N) (dur : J → ℝ≥0) :
    value (readRows (project N Finset.univ) initial.rows b)
        (fun i => wordVariables N r (originalGamma p) dur (decode i)) =
      ((((originalRegisterPMF N p).map (initialCode N sample)).map
        (projection N Finset.univ)) b).toReal := by
  have heq := checkRows_sound (project N Finset.univ)
    (initialRows N sample (fun h => encode (.inr h))) initial.rows initial.checked b
  have hev := congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ)
    (fun i => wordVariables N r (originalGamma p) dur (decode i))) heq
  rw [eval_polynomial, eval_polynomial] at hev
  have hx : ∀ h : Hybrid N,
      wordVariables N r (originalGamma p) dur (decode (encode (.inr h))) = p.gamma h := by
    intro h
    rw [hleft]
    rfl
  exact hev.symm.trans (initialRows_actual N sample (fun h => encode (.inr h)) p b
    (fun i => wordVariables N r (originalGamma p) dur (decode i)) hx)

def checkComposedWord (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native)
    (initial : CertifiedInitial N sample encode)
    (cache : List (CertifiedStep N sample H common encode))
    (word : List (Symbol J V E)) (supplied : Rows Native (Code N sample)) : Bool :=
  checkRows (project N Finset.univ)
    (bindRows initial.rows (followRows (cachedStep N sample H common encode cache) word))
    supplied

/-- Actual SAME-bank natural word. All primitive checks and the final total
coefficient-fibre check are present; desired source-law equality is not a
premise. The original natural initialization is integrated ONCE. -/
theorem checked_same_source_natural_word (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (encode : WordVariable N J → Native) (decode : Native → WordVariable N J)
    (hleft : Function.LeftInverse decode encode)
    (initial : CertifiedInitial N sample encode)
    (cache : List (CertifiedStep N sample H common encode))
    (word : List (Symbol J V E)) (supplied : Rows Native (Code N sample))
    (h : checkComposedWord N sample H common encode initial cache word supplied = true)
    (b : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates E) (p : HybridProbabilities N) (dur : J → ℝ≥0) :
    value (readRows (project N Finset.univ) supplied b)
        (fun i => wordVariables N r (originalGamma p) dur (decode i)) =
      (((initializedWordLaw N sample H p common r dur word).map
        (projection N Finset.univ)) b).toReal := by
  classical
  let x : Native → ℝ := fun i => wordVariables N r (originalGamma p) dur (decode i)
  have heq := checkRows_sound (project N Finset.univ)
    (bindRows initial.rows (followRows (cachedStep N sample H common encode cache) word))
    supplied h b
  have hev := congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ) x) heq
  rw [eval_polynomial, eval_polynomial] at hev
  apply hev.symm.trans
  rw [value_read_bindRows]
  simp_rw [native_follow_value N H common r (originalGamma p) dur
    (cachedStep N sample H common encode cache) x
    (fun op s a => cached_step_value N sample H common encode decode hleft cache op s a r
      (originalGamma p) dur)]
  rw [sum_partition initial.rows (fun row => project N Finset.univ row.1)
    (fun row => value row.2 x)
    (fun a => (selectedProgram N r Finset.univ
      (word.map (instantiateGamma N H (originalGamma p) common dur)) a b).toReal)]
  rw [initializedWordLaw_projected, bind_probability_real, tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [← value_readRows, initial_value N sample encode decode hleft initial a r p dur]

end Astra.OriginalWordCacheCertificate
