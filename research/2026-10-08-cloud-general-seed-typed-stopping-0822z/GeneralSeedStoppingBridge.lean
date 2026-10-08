import InfiniteIIDStoppingBridge
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
SOURCE candidate, compiler UNCHECKED. Arbitrary independent once-drawn
probability-space seeds; actual product events and finite rectangle sums.
The explicit section premise is interpreter measurability, not a supplied
observer law, marginal identity or acceptance probability.
Outside the exact181 repair and every authorized compiler selection.
-/
namespace UnifiedLean.G6.GeneralSeedStoppingBridge

open MeasureTheory
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open UnifiedLean.G6.CorruptionClasses UnifiedLean.G6.ExpandedCorruptionClosure
open UnifiedLean.G6.FiniteReadClosureObstruction
open UnifiedLean.G6.SequentialPrefixClosureObstruction
open UnifiedLean.G6.InfiniteIIDStoppingBridge
open scoped BigOperators Classical

variable {A Seed : Type*} [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace Seed]

def positiveSeedSection (rule : StoppingRule Seed A) (n : ℕ)
    (word : Fin n → A) : Set Seed :=
  {seed | firstPositiveBy rule seed n word}

def wordCylinder (n : ℕ) (word : Fin n → A) : Set (ℕ → A) :=
  (streamPrefix n) ⁻¹' {word}

noncomputable def seededDecisions (seedLaw : Measure Seed)
    (rule : StoppingRule Seed A) : PrefixDecisions A :=
  fun n word => (seedLaw (positiveSeedSection rule n word)).toReal

def seededPositiveBy (rule : StoppingRule Seed A) (n : ℕ) :
    Set (Seed × (ℕ → A)) :=
  {x | firstPositiveBy rule x.1 n (streamPrefix n x.2)}

def seededEventualPositive (rule : StoppingRule Seed A) : Set (Seed × (ℕ → A)) :=
  ⋃ n, seededPositiveBy rule n

theorem seededDecisions_bounds (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (rule : StoppingRule Seed A) (n : ℕ) (word : Fin n → A) :
    0 ≤ seededDecisions seedLaw rule n word ∧ seededDecisions seedLaw rule n word ≤ 1 := by
  exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

theorem measurable_wordCylinder (n : ℕ) (word : Fin n → A) :
    MeasurableSet (wordCylinder n word) := by
  exact (measurableSet_singleton word).preimage (measurable_streamPrefix n)

theorem wordCylinder_probability (p : PMF A) (n : ℕ) (word : Fin n → A) :
    (iidStreamLaw p) (wordCylinder n word) = iidPMF p n word := by
  calc
    (iidStreamLaw p) (wordCylinder n word) =
        ((iidStreamLaw p).map (streamPrefix n)) {word} :=
      (Measure.map_apply (measurable_streamPrefix n) (measurableSet_singleton word)).symm
    _ = (iidPMF p n).toMeasure {word} := by rw [iidStreamLaw_prefix_marginal]
    _ = iidPMF p n word :=
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton word)

/-- Literal finite word partition; independence is used only when the
constructed product measure is subsequently evaluated on these rectangles. -/
theorem seededPositiveBy_rectangles (rule : StoppingRule Seed A) (n : ℕ) :
    seededPositiveBy rule n =
      ⋃ word ∈ (Finset.univ : Finset (Fin n → A)),
        positiveSeedSection rule n word ×ˢ wordCylinder n word := by
  ext x
  simp only [seededPositiveBy, positiveSeedSection, wordCylinder, Set.mem_setOf_eq,
    Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_prod,
    Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨streamPrefix n x.2, h, rfl⟩
  · rintro ⟨word, h, heq⟩
    simpa only [heq] using h

theorem seededPositiveBy_monotone (rule : StoppingRule Seed A) :
    Monotone (seededPositiveBy rule) := by
  intro m n hmn x h
  have hprefix : (fun i : Fin m =>
      streamPrefix n x.2 (Fin.castLE hmn i)) = streamPrefix m x.2 := rfl
  apply firstPositiveBy_prefix_mono rule x.1 hmn
  simpa only [seededPositiveBy, Set.mem_setOf_eq, hprefix] using h

/-- The admissibility premise is only that every finite first-positive
seed section is measurable. It follows from measurable finite-word signal
sections by finite unions/intersections; no probability equality is assumed. -/
theorem measurable_seededPositiveBy (rule : StoppingRule Seed A)
    (hsections : ∀ n word, MeasurableSet (positiveSeedSection rule n word)) (n : ℕ) :
    MeasurableSet (seededPositiveBy rule n) := by
  rw [seededPositiveBy_rectangles]
  exact MeasurableSet.iUnion (fun word =>
    MeasurableSet.iUnion (fun _ =>
      (hsections n word).prod (measurable_wordCylinder n word)))

theorem measurable_seededEventualPositive (rule : StoppingRule Seed A)
    (hsections : ∀ n word, MeasurableSet (positiveSeedSection rule n word)) :
    MeasurableSet (seededEventualPositive rule) := by
  exact MeasurableSet.iUnion (measurable_seededPositiveBy rule hsections)

/-- Constructed product event probability equals the previously finite
polynomial expectation with weights derived from the SAME seed law. -/
theorem seededPositiveBy_probability (seedLaw : Measure Seed)
    [IsProbabilityMeasure seedLaw] (p : PMF A) (rule : StoppingRule Seed A)
    (hsections : ∀ n word, MeasurableSet (positiveSeedSection rule n word)) (n : ℕ) :
    ((seedLaw.prod (iidStreamLaw p)) (seededPositiveBy rule n)).toReal =
      expectedTest p n (seededDecisions seedLaw rule n) := by
  let rect := fun word : Fin n → A =>
    positiveSeedSection rule n word ×ˢ wordCylinder n word
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n → A))) rect := by
    intro word _ other _ hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hword : streamPrefix n x.2 = word := hx.2
    have hother : streamPrefix n x.2 = other := hy.2
    exact hne (hword.symm.trans hother)
  have hm : ∀ word ∈ (Finset.univ : Finset (Fin n → A)), MeasurableSet (rect word) := by
    intro word _
    exact (hsections n word).prod (measurable_wordCylinder n word)
  have he : (seedLaw.prod (iidStreamLaw p)) (seededPositiveBy rule n) =
      ∑ word : Fin n → A, (seedLaw.prod (iidStreamLaw p)) (rect word) := by
    rw [seededPositiveBy_rectangles]
    exact measure_biUnion_finset hd hm
  rw [he, ENNReal.toReal_sum (fun word _ => measure_ne_top
    (seedLaw.prod (iidStreamLaw p)) (rect word))]
  unfold expectedTest
  apply Finset.sum_congr rfl
  intro word _
  change ((seedLaw.prod (iidStreamLaw p))
    (positiveSeedSection rule n word ×ˢ wordCylinder n word)).toReal =
      (iidPMF p n word).toReal * (seedLaw (positiveSeedSection rule n word)).toReal
  rw [Measure.prod_prod, ENNReal.toReal_mul, wordCylinder_probability]
  exact mul_comm _ _

theorem seededEventualPositive_probability (seedLaw : Measure Seed)
    [IsProbabilityMeasure seedLaw] (p : PMF A) (rule : StoppingRule Seed A)
    (hsections : ∀ n word, MeasurableSet (positiveSeedSection rule n word)) :
    ((seedLaw.prod (iidStreamLaw p)) (seededEventualPositive rule)).toReal =
      eventualAcceptance p (seededDecisions seedLaw rule) := by
  unfold seededEventualPositive
  rw [(seededPositiveBy_monotone rule).measure_iUnion]
  rw [ENNReal.toReal_iSup (fun n => measure_ne_top (seedLaw.prod (iidStreamLaw p)) _)]
  simp_rw [seededPositiveBy_probability seedLaw p rule hsections]
  rfl

theorem no_uniform_general_seed_event_stopping_at_wrong_closure
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (rule : StoppingRule Seed A)
    (hsections : ∀ n word, MeasurableSet (positiveSeedSection rule n word))
    (p : PMF A) (laws : Set (PMF A)) (beta alpha : ℝ)
    (hb : 0 ≤ beta) (halpha : 2 * alpha < 1)
    (hcorrect : ∀ z : PMF A, pmfTV p z ≤ beta →
      1 - alpha ≤ ((seedLaw.prod (iidStreamLaw z)) (seededEventualPositive rule)).toReal)
    (hsound : ∀ q ∈ expanded laws beta,
      ((seedLaw.prod (iidStreamLaw q)) (seededEventualPositive rule)).toReal ≤ alpha)
    (hboundary : ∃ q ∈ tvClosure laws, pmfTV p q ≤ 2 * beta) : False := by
  apply no_uniform_prefix_stopping_at_wrong_closure p laws beta alpha hb halpha
    (seededDecisions seedLaw rule) (seededDecisions_bounds seedLaw rule)
  · intro z hz
    simpa only [seededEventualPositive_probability seedLaw z rule hsections] using hcorrect z hz
  · intro q hq
    simpa only [seededEventualPositive_probability seedLaw q rule hsections] using hsound q hq
  · exact hboundary

#print axioms seededDecisions_bounds
#print axioms measurable_wordCylinder
#print axioms wordCylinder_probability
#print axioms seededPositiveBy_rectangles
#print axioms seededPositiveBy_monotone
#print axioms measurable_seededPositiveBy
#print axioms measurable_seededEventualPositive
#print axioms seededPositiveBy_probability
#print axioms seededEventualPositive_probability
#print axioms no_uniform_general_seed_event_stopping_at_wrong_closure

end UnifiedLean.G6.GeneralSeedStoppingBridge
