import G7FixedCalendarPowerDomain
import G7ControlledWordPolynomial

/-! SOURCE ONLY: this complete-import composition has not been elaborated.
The positive-power supplier is separately hosted checked. This receiver uses
the original source rate structure and original WordVariable/wordEval; it does
not identify a native sparse table, captured calendar, parser or readout. -/

namespace Astra.PhysicalPowerWordBank

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.OriginalFixedIDControls
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.ControlledWordPolynomial
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open Astra.FixedCalendarPowerDomain
open scoped Classical NNReal

variable {J V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def populationDuration (N : RootedBinary V E X)
    (C : Calendar N.graph) : Option E → ℝ
  | none => 1
  | some e => C.age (N.graph.source e) - C.age (N.graph.target e)

theorem populationDuration_pos (N : RootedBinary V E X) (C : Calendar N.graph)
    (i : Option E) : 0 < populationDuration N C i := by
  cases i with
  | none => exact zero_lt_one
  | some e => exact sub_pos.mpr (C.edge_older e)

/-- Direct constructor of the existing positive ORIGINAL-edge/ancestral rates.
The none survival names ONE UNIT of ancestral time, not a fixed rate. -/
noncomputable def originalRates (N : RootedBinary V E X) (C : Calendar N.graph)
    (survival : Option E → ℝ) (hX : ∀ i, 0 < survival i ∧ survival i < 1) :
    PositivePairRates E where
  edge e := rate (survival (some e)) (populationDuration N C (some e))
  edge_pos e := rate_pos (hX (some e)).1 (hX (some e)).2
    (populationDuration_pos N C (some e))
  ancestral := rate (survival none) (populationDuration N C none)
  ancestral_pos := rate_pos (hX none).1 (hX none).2
    (populationDuration_pos N C none)

theorem pairRate_originalRates (N : RootedBinary V E X) (C : Calendar N.graph)
    (survival : Option E → ℝ) (hX : ∀ i, 0 < survival i ∧ survival i < 1)
    (i : Option E) :
    pairRate (originalRates N C survival hX) i =
      rate (survival i) (populationDuration N C i) := by
  cases i <;> rfl

noncomputable def bankVariables (N : RootedBinary V E X)
    (Z : J → Option E → ℝ) (gamma : Hybrid N → unitInterval) : WordVariable N J → ℝ
  | .inl (j,i) => Z j i
  | .inr h => (gamma h : ℝ)

theorem bankVariables_eq_wordVariables (N : RootedBinary V E X)
    (C : Calendar N.graph) (survival : Option E → ℝ)
    (hX : ∀ i, 0 < survival i ∧ survival i < 1)
    (Z : J → Option E → ℝ) (hZ : ∀ j i, 0 < Z j i)
    (dur : J → ℝ≥0) (p q : J → Option E → ℕ) (hq : ∀ j i, 0 < q j i)
    (htime : ∀ j i, (q j i : ℝ) * (dur j : ℝ) =
      (p j i : ℝ) * populationDuration N C i)
    (hpowers : ∀ j i, Z j i ^ q j i = survival i ^ p j i)
    (gamma : Hybrid N → unitInterval) :
    bankVariables N Z gamma = wordVariables N (originalRates N C survival hX) gamma dur := by
  funext w
  cases w with
  | inl ji =>
    rcases ji with ⟨j,i⟩
    change Z j i = Real.exp (-pairRate (originalRates N C survival hX) i * (dur j : ℝ))
    rw [pairRate_originalRates]
    exact (positive_power_iff_exp (hX i).1 (hZ j i)
      (populationDuration_pos N C i) (p j i) (q j i) (hq j i) (htime j i)).mp
      (hpowers j i)
  | inr h => rfl

theorem bank_eval_eq_wordEval (N : RootedBinary V E X)
    (C : Calendar N.graph) (survival : Option E → ℝ)
    (hX : ∀ i, 0 < survival i ∧ survival i < 1)
    (Z : J → Option E → ℝ) (hZ : ∀ j i, 0 < Z j i)
    (dur : J → ℝ≥0) (p q : J → Option E → ℕ) (hq : ∀ j i, 0 < q j i)
    (htime : ∀ j i, (q j i : ℝ) * (dur j : ℝ) =
      (p j i : ℝ) * populationDuration N C i)
    (hpowers : ∀ j i, Z j i ^ q j i = survival i ^ p j i)
    (gamma : Hybrid N → unitInterval) (P : MvPolynomial (WordVariable N J) ℚ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) (bankVariables N Z gamma) P =
      wordEval N (originalRates N C survival hX) gamma dur P := by
  rw [bankVariables_eq_wordVariables N C survival hX Z hZ dur p q hq htime hpowers]
  rfl

/-- One original natural bank serves EVERY supplied mask; transition forcing
is already inside the existing controlledWordPolynomial. Empty Copy is allowed.
This is a finite-word endpoint, not an ancestral-completed readout theorem. -/
theorem actual_controlled_word_bank (N : RootedBinary V E X)
    (C : Calendar N.graph) (survival : Option E → ℝ)
    (hX : ∀ i, 0 < survival i ∧ survival i < 1)
    (Z : J → Option E → ℝ) (hZ : ∀ j i, 0 < Z j i)
    (dur : J → ℝ≥0) (p q : J → Option E → ℕ) (hq : ∀ j i, 0 < q j i)
    (htime : ∀ j i, (q j i : ℝ) * (dur j : ℝ) =
      (p j i : ℝ) * populationDuration N C i)
    (hpowers : ∀ j i, Z j i ^ q j i = survival i ^ p j i)
    (sample : Copy → X) (H : OriginalParentRegistry N) (inheritance : HybridProbabilities N)
    (common : Hybrid N → Bool) (mask : OriginalMask N)
    (word : List (Symbol J V E)) (b : SelectedIndex N sample Finset.univ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) (bankVariables N Z (originalGamma inheritance))
      (controlledWordPolynomial N sample H common mask word b) =
      (((controlledWordLaw N sample H inheritance common mask
        (originalRates N C survival hX) dur word).map (projection N Finset.univ)) b).toReal := by
  rw [bank_eval_eq_wordEval N C survival hX Z hZ dur p q hq htime hpowers]
  exact actual_controlled_word_polynomial N sample H inheritance common mask
    (originalRates N C survival hX) dur word b

end Astra.PhysicalPowerWordBank
