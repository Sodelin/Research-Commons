import UnifiedLean.Source.FiniteSourceSnapshot
import UnifiedLean.Source.NativePairClockLaw
import SourceForestKingmanPopulationProjection
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Field

/-!
# Constructed positive-rate uniformized step of the ORIGINAL source state

Contributor: dot, 2026-10-02. Candidate next finite-time source-kernel gate.
Actual original edge/root populations supply CURRENT legal pairs and their
positive constant rates. A copy-cap/rate-derived global bound constructs a
normalized holding-or-merger choice law; every merger updates the existing
source forest and is encoded back into its admitted finite snapshot. This is
an internal uniformization primitive, not yet a continuous-time/calendar or
timed-path observation theorem. No desired transition law is a contract field.
-/
namespace UnifiedLean.Source.UniformizedSourceStep
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev Code (N : RootedBinary V E X) (sample : Copy → X) := AdmittedSnapshot N sample

noncomputable def state {N : RootedBinary V E X} {sample : Copy → X}
    (s : Code N sample) : State V E Copy := decodeSnapshot N.root s.val

noncomputable def originalPlace (N : RootedBinary V E X) : Option E → Location V E
  | none => .rootPopulation N.root
  | some e => .edge e

lemma originalPlace_not_node (N : RootedBinary V E X) (i : Option E) (v : V) :
    originalPlace N i ≠ .node v := by
  cases i <;> intro h <;> cases h

/-- Ordered pairs have half the population pair rate. Both orientations
encode the same unordered Kingman event; child order remains internal. -/
abbrev Choice (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :=
  Σ i : Option E, {p : Copy × Copy // p ∈ (populationRoots (state s) (originalPlace N i)).offDiag}

noncomputable instance choiceFintype (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Fintype (Choice N s) := by
  unfold Choice
  infer_instance

noncomputable def choiceRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) : ℝ := pairRate r p.1 / 2

noncomputable def totalRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : ℝ := ∑ p : Choice N s, choiceRate N r s p

noncomputable def globalRateBound (r : PositivePairRates E) : ℝ :=
  (1 + ∑ i : Option E, pairRate r i) * (1 + (Fintype.card Copy : ℝ)^2)

lemma globalRateBound_positive (r : PositivePairRates E) :
    0 < globalRateBound (Copy := Copy) r := by
  have hsum : 0 ≤ ∑ i : Option E, pairRate r i :=
    Finset.sum_nonneg (fun i _ => (pairRate_pos r i).le)
  unfold globalRateBound
  positivity

lemma totalRate_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : 0 ≤ totalRate N r s := by
  apply Finset.sum_nonneg
  intro p _
  exact div_nonneg (pairRate_pos r p.1).le (by norm_num)

/-- A genuine explicit rate bound, not an input-supplied source-size or
probability premise. The original graph/rates and copy carrier remain fixed. -/
theorem totalRate_le_globalRateBound (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    totalRate N r s ≤ globalRateBound (Copy := Copy) r := by
  have hsum : 0 ≤ ∑ i : Option E, pairRate r i :=
    Finset.sum_nonneg (fun i _ => (pairRate_pos r i).le)
  have hbound : totalRate N r s ≤
      (∑ i : Option E, pairRate r i) * (Fintype.card Copy : ℝ)^2 := by
    unfold totalRate choiceRate
    rw [Fintype.sum_sigma]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    let pairs := (populationRoots (state s) (originalPlace N i)).offDiag
    have hc : (pairs.card : ℝ) ≤ (Fintype.card Copy : ℝ)^2 := by
      have hh := Finset.card_le_univ pairs
      simpa only [Fintype.card_prod,Nat.cast_mul,pow_two] using
        (show (pairs.card : ℝ) ≤ (Fintype.card (Copy × Copy) : ℝ) by exact_mod_cast hh)
    change (∑ _ : pairs, pairRate r i / 2) ≤ _
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    have hp := pairRate_pos r i
    nlinarith [sq_nonneg (Fintype.card Copy : ℝ)]
  unfold globalRateBound
  nlinarith [sq_nonneg (Fintype.card Copy : ℝ)]

noncomputable def choiceMass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Option (Choice N s) → ℝ
  | none => 1-totalRate N r s/globalRateBound (Copy := Copy) r
  | some p => choiceRate N r s p/globalRateBound (Copy := Copy) r

lemma choiceMass_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Option (Choice N s)) :
    0 ≤ choiceMass N r s p := by
  cases p with
  | none =>
      apply sub_nonneg.mpr
      exact (div_le_one (globalRateBound_positive (Copy := Copy) r)).mpr
        (totalRate_le_globalRateBound N r s)
  | some p =>
      exact div_nonneg (div_nonneg (pairRate_pos r p.1).le (by norm_num))
        (globalRateBound_positive (Copy := Copy) r).le

lemma choiceMass_normalized (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (∑ p : Option (Choice N s), choiceMass N r s p) = 1 := by
  rw [Fintype.sum_option]
  simp only [choiceMass]
  rw [← Finset.sum_div]
  change 1-totalRate N r s/globalRateBound (Copy := Copy) r +
    totalRate N r s/globalRateBound (Copy := Copy) r = 1
  ring

noncomputable def choicePMF (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Option (Choice N s)) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (choiceMass N r s p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => choiceMass_nonnegative N r s p),
      choiceMass_normalized]
    simp)

/-- The destination is built by the inherited ACTUAL legal source merger,
with SourceValid preservation proved there, then exact finite snapshot coding. -/
noncomputable def stepDestination (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Option (Choice N s) → Code N sample
  | none => s
  | some p =>
      admittedCode N sample (merge (state s) p.2.val.1 p.2.val.2)
        (merge_source_valid N sample (state s) s.property
          (population_pair_is_source_legal (state s) (originalPlace N p.1)
            (originalPlace_not_node N p.1) p.2.property))

/-- A normalized, source-valid finite-state step. Dummy holding leaves the
source unchanged; mergers preserve all original graph/sample/registry IDs. -/
noncomputable def sourceStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Code N sample) :=
  (choicePMF N r s).map (stepDestination N s)

#print axioms totalRate_le_globalRateBound
#print axioms choiceMass_nonnegative
#print axioms choiceMass_normalized
#print axioms sourceStep
end UnifiedLean.Source.UniformizedSourceStep
