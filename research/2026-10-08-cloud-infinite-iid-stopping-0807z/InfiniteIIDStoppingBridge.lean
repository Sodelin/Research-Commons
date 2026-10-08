import SequentialPrefixClosureObstruction
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Measure.Dirac

/-!
CLOUD-G6-SOL-ULTRA-20261007. SOURCE candidate only; compiler UNCHECKED.
Construct the genuine infinite iid measure, its finite word marginals, and
the actual eventual-positive event for a deterministic full-prefix rule.
No supplied stopping law or iid marginal equality is a structure field.
General measurable independent random seeds remain a further extension.
This draft is outside every currently authorized compiler selection.
-/
namespace UnifiedLean.G6.InfiniteIIDStoppingBridge

open MeasureTheory
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open UnifiedLean.G6.CorruptionClasses UnifiedLean.G6.ExpandedCorruptionClosure
open UnifiedLean.G6.FiniteReadClosureObstruction
open UnifiedLean.G6.SequentialPrefixClosureObstruction
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

def streamPrefix (n : ℕ) (stream : ℕ → A) : Fin n → A :=
  fun i => stream i.val

theorem measurable_streamPrefix (n : ℕ) : Measurable (streamPrefix (A := A) n) := by
  exact measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)

def rangeToFin (n : ℕ) : (↑(Finset.range n)) ≃ Fin n where
  toFun i := ⟨i.val, Finset.mem_range.mp i.property⟩
  invFun i := ⟨i.val, Finset.mem_range.mpr i.isLt⟩
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

noncomputable def iidStreamLaw (p : PMF A) : Measure (ℕ → A) :=
  Measure.infinitePi (fun _ : ℕ => p.toMeasure)

instance iidStreamLaw_probability (p : PMF A) : IsProbabilityMeasure (iidStreamLaw p) := by
  unfold iidStreamLaw
  infer_instance

theorem finite_pi_eq_iidPMF (p : PMF A) (n : ℕ) :
    Measure.pi (fun _ : Fin n => p.toMeasure) = (iidPMF p n).toMeasure := by
  apply Measure.ext_of_singleton
  intro word
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.prod_ne_top (fun i _ => p.apply_ne_top (word i)))
    ((iidPMF p n).apply_ne_top word)).mp
  rw [ENNReal.toReal_prod, iidPMF_real]
  rfl

/-- The genuine countable-product law has the SAME previously constructed
finite iid word PMF as marginal, including n = 0. -/
theorem iidStreamLaw_prefix_marginal (p : PMF A) (n : ℕ) :
    (iidStreamLaw p).map (streamPrefix n) = (iidPMF p n).toMeasure := by
  let e := rangeToFin n
  let g := MeasurableEquiv.piCongrLeft (fun _ : Fin n => A) e
  have hcomp : g ∘ (Finset.range n).restrict = streamPrefix (A := A) n := by
    funext stream i
    change stream ((e.symm i).val) = stream i.val
    rfl
  rw [← hcomp, ← Measure.map_map g.measurable (Finset.measurable_restrict _)]
  unfold iidStreamLaw
  rw [Measure.infinitePi_map_restrict]
  change (Measure.pi (fun _ : ↑(Finset.range n) => p.toMeasure)).map g =
    (iidPMF p n).toMeasure
  rw [Measure.pi_map_piCongrLeft e (fun _ : Fin n => p.toMeasure)]
  exact finite_pi_eq_iidPMF p n

abbrev DeterministicRule (A : Type*) := (n : ℕ) → (Fin n → A) → StopSignal

def positiveWords (rule : DeterministicRule A) (n : ℕ) : Set (Fin n → A) :=
  {word | firstPositiveBy (fun (_ : Unit) k w => rule k w) () n word}

def positiveBy (rule : DeterministicRule A) (n : ℕ) : Set (ℕ → A) :=
  (streamPrefix n) ⁻¹' positiveWords rule n

def eventualPositive (rule : DeterministicRule A) : Set (ℕ → A) :=
  ⋃ n, positiveBy rule n

noncomputable def deterministicDecisions (rule : DeterministicRule A) : PrefixDecisions A :=
  fun n word => if word ∈ positiveWords rule n then 1 else 0

theorem deterministicDecisions_bounds (rule : DeterministicRule A) (n : ℕ)
    (word : Fin n → A) :
    0 ≤ deterministicDecisions rule n word ∧ deterministicDecisions rule n word ≤ 1 := by
  unfold deterministicDecisions
  split_ifs <;> norm_num

theorem measurable_positiveWords (rule : DeterministicRule A) (n : ℕ) :
    MeasurableSet (positiveWords rule n) := by
  exact (Set.toFinite _).measurableSet

theorem measurable_positiveBy (rule : DeterministicRule A) (n : ℕ) :
    MeasurableSet (positiveBy rule n) := by
  exact (measurable_positiveWords rule n).preimage (measurable_streamPrefix n)

theorem positiveBy_monotone (rule : DeterministicRule A) : Monotone (positiveBy rule) := by
  intro m n hmn stream h
  have hprefix : (fun i : Fin m =>
      streamPrefix n stream (Fin.castLE hmn i)) = streamPrefix m stream := rfl
  apply firstPositiveBy_prefix_mono (fun (_ : Unit) k w => rule k w) () hmn
  simpa only [positiveBy, Set.mem_preimage, positiveWords, Set.mem_setOf_eq, hprefix] using h

theorem measurable_eventualPositive (rule : DeterministicRule A) :
    MeasurableSet (eventualPositive rule) := by
  exact MeasurableSet.iUnion (measurable_positiveBy rule)

/-- The polynomial expectation is the actual finite-cylinder probability,
not a supplied observer response or measure identity. -/
theorem positiveBy_probability (p : PMF A) (rule : DeterministicRule A) (n : ℕ) :
    ((iidStreamLaw p) (positiveBy rule n)).toReal =
      expectedTest p n (deterministicDecisions rule n) := by
  have hm := iidStreamLaw_prefix_marginal p n
  have he : (iidStreamLaw p) (positiveBy rule n) =
      (iidPMF p n).toMeasure (positiveWords rule n) := by
    rw [← hm, Measure.map_apply (measurable_streamPrefix n)
      (measurable_positiveWords rule n)]
    rfl
  rw [he]
  have hi := PMF.integral_eq_sum (iidPMF p n)
    ((positiveWords rule n).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const 1 (measurable_positiveWords rule n)] at hi
  simpa [expectedTest, deterministicDecisions, Set.indicator, measureReal_def,
    smul_eq_mul] using hi

/-- A genuine eventually-positive probability equals the operational
supremum. Finite first-stop events are nested, hence continuity from below
requires no common deterministic or expected read bound. -/
theorem eventualPositive_probability (p : PMF A) (rule : DeterministicRule A) :
    ((iidStreamLaw p) (eventualPositive rule)).toReal =
      eventualAcceptance p (deterministicDecisions rule) := by
  unfold eventualPositive
  rw [(positiveBy_monotone rule).measure_iUnion]
  rw [ENNReal.toReal_iSup (fun n => measure_ne_top (iidStreamLaw p) _)]
  simp_rw [positiveBy_probability]
  rfl

theorem no_uniform_deterministic_event_stopping_at_wrong_closure
    (rule : DeterministicRule A) (p : PMF A) (laws : Set (PMF A))
    (beta alpha : ℝ) (hb : 0 ≤ beta) (halpha : 2 * alpha < 1)
    (hcorrect : ∀ z : PMF A, pmfTV p z ≤ beta →
      1 - alpha ≤ ((iidStreamLaw z) (eventualPositive rule)).toReal)
    (hsound : ∀ q ∈ expanded laws beta,
      ((iidStreamLaw q) (eventualPositive rule)).toReal ≤ alpha)
    (hboundary : ∃ q ∈ tvClosure laws, pmfTV p q ≤ 2 * beta) : False := by
  apply no_uniform_prefix_stopping_at_wrong_closure p laws beta alpha hb halpha
    (deterministicDecisions rule) (deterministicDecisions_bounds rule)
  · intro z hz
    simpa only [eventualPositive_probability] using hcorrect z hz
  · intro q hq
    simpa only [eventualPositive_probability] using hsound q hq
  · exact hboundary

#print axioms measurable_streamPrefix
#print axioms finite_pi_eq_iidPMF
#print axioms iidStreamLaw_prefix_marginal
#print axioms deterministicDecisions_bounds
#print axioms measurable_positiveWords
#print axioms measurable_positiveBy
#print axioms positiveBy_monotone
#print axioms measurable_eventualPositive
#print axioms positiveBy_probability
#print axioms eventualPositive_probability
#print axioms no_uniform_deterministic_event_stopping_at_wrong_closure

end UnifiedLean.G6.InfiniteIIDStoppingBridge
