import G6RationalAffineWitness
import NaturalCellAffineCompiler

/-!
# A returned rational vector is an actual shared original-source bank

Contributor: Codex / lean_reuse, 10 October 2026.
The caller supplies the original source, a finite typed chart, and its bijective
variable layout. The solver returns one rational age/inverse-rate/coin vector
jointly satisfying every row of that chart. Positivity, contemporaneous tip
ages, chronology, interval constraints and natural inheritance are decoded by
the inherited proved source compiler. Automatic source/chart generation and
nonlinear exact observation-law constraints are separate obligations.
-/
namespace UnifiedLean.G6.RationalNaturalCellWitness

open Nanuq.Source GProgram.G5
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture

variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)

def solveOriginalCell (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : Option (Fin n → ℚ) :=
  solveRational n (compileCell N layout chronology rows coins)

def checkOriginalCellWitness (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ) : Bool :=
  checkRationalWitness (compileCell N layout chronology rows coins) q

/-- A successful exact rational certificate produces the actual jointly shared
bank, with every original-calendar constraint interpreted on that same vector. -/
theorem checkOriginalCellWitness_sound (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    BankConditions N chronology rows coins
      (agesOf N layout (fun i => (q i : ℝ)))
      (inverseRatesOf N layout (fun i => (q i : ℝ)))
      (coinsOf N layout (fun i => (q i : ℝ))) := by
  apply (compileCell_correct N layout chronology rows coins _).mp
  apply rationalWitness_real
  exact (checkRationalWitness_correct _ q).mp hq

theorem solveOriginalCell_sound (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : solveOriginalCell N layout chronology rows coins = some q) :
    BankConditions N chronology rows coins
      (agesOf N layout (fun i => (q i : ℝ)))
      (inverseRatesOf N layout (fun i => (q i : ℝ)))
      (coinsOf N layout (fun i => (q i : ℝ))) := by
  apply checkOriginalCellWitness_sound N layout chronology rows coins q
  exact solveRational_checked _ q hq

/-- Real feasibility of the supplied original-source cell is equivalent to
the actual executable solver returning a rational shared bank. -/
theorem solveOriginalCell_complete (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) :
    (∃ q, solveOriginalCell N layout chronology rows coins = some q) ↔
      originalCellFeasible N chronology rows coins := by
  unfold solveOriginalCell
  exact (solveRational_complete n _).trans
    ((inverse_cell_iff_compiled N layout chronology rows coins).symm.trans
      (original_cell_iff_inverse N chronology rows coins).symm)

theorem solveOriginalCell_none_iff (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) :
    solveOriginalCell N layout chronology rows coins = none ↔
      ¬ originalCellFeasible N chronology rows coins := by
  rw [← solveOriginalCell_complete N layout chronology rows coins]
  cases h : solveOriginalCell N layout chronology rows coins <;> simp

/-- The literal original source carriers, together with all supplied chart
constraints on their one shared physical bank. -/
structure OriginalCellBank (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) where
  calendar : Calendar N.graph
  rates : PositivePairRates E
  inheritance : HybridProbabilities N
  leaf_zero : ∀ x, calendar.age (N.leaf x) = 0
  chronology_holds : ∀ j, (chronology j).holds calendar.age
  coins_holds : ∀ h, (coins h).contains (inheritance.gamma h)
  exposures_hold : ∀ i, (rows i).cell.contains
    (pairRate rates (rows i).population * (rows i).duration calendar.age)

/-- No existence choice occurs in this realization: calendar ages and coins
are the returned coordinates; rates are their positive inverse reciprocals.
The real carrier realization is noncomputable, while the rational solver and
its finite certificate remain executable. -/
noncomputable def checkedOriginalCellBank (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    OriginalCellBank N chronology rows coins := by
  obtain ⟨hedge, htip, hu, hg0, hg1, hchron, hcoins, hrows⟩ :=
    checkOriginalCellWitness_sound N layout chronology rows coins q hq
  refine ⟨calendarOfAges N (agesOf N layout (fun i => (q i : ℝ))) hedge,
    ratesOfInverse (inverseRatesOf N layout (fun i => (q i : ℝ))) hu,
    inheritanceOfValues N (coinsOf N layout (fun i => (q i : ℝ))) hg0 hg1,
    htip, hchron, hcoins, ?_⟩
  exact reconstructed_bank_satisfies rows _ _ hu hrows

theorem checkedOriginalCellBank_ages (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    (checkedOriginalCellBank N layout chronology rows coins q hq).calendar.age =
      agesOf N layout (fun i => (q i : ℝ)) := rfl

theorem checkedOriginalCellBank_rates (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true)
    (e : Option E) :
    pairRate (checkedOriginalCellBank N layout chronology rows coins q hq).rates e =
      (inverseRatesOf N layout (fun i => (q i : ℝ)) e)⁻¹ := by
  exact constructed_pair_rate _ _ e

theorem checkedOriginalCellBank_coins (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    (checkedOriginalCellBank N layout chronology rows coins q hq).inheritance.gamma =
      coinsOf N layout (fun i => (q i : ℝ)) := rfl

/-- Executable output carries the positive checker proof; proof erasure leaves
the exact same rational vector returned by the original solver. -/
def solveOriginalCellCertified (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) :
    Option {q : Fin n → ℚ // checkOriginalCellWitness N layout chronology rows coins q = true} :=
  match h : solveOriginalCell N layout chronology rows coins with
  | none => none
  | some q => some ⟨q, solveRational_checked _ q h⟩

theorem solveOriginalCellCertified_values (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) :
    (solveOriginalCellCertified N layout chronology rows coins).map Subtype.val =
      solveOriginalCell N layout chronology rows coins := by
  unfold solveOriginalCellCertified
  split <;> simp_all

theorem checkedOriginalCellBank_feasible (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    originalCellFeasible N chronology rows coins := by
  let b := checkedOriginalCellBank N layout chronology rows coins q hq
  exact ⟨b.calendar, b.rates, b.inheritance, b.leaf_zero,
    b.chronology_holds, b.coins_holds, b.exposures_hold⟩

#print axioms checkOriginalCellWitness_sound
#print axioms solveOriginalCell_sound
#print axioms solveOriginalCell_complete
#print axioms solveOriginalCell_none_iff
#print axioms checkedOriginalCellBank
#print axioms checkedOriginalCellBank_ages
#print axioms checkedOriginalCellBank_rates
#print axioms checkedOriginalCellBank_coins
#print axioms solveOriginalCellCertified_values
#print axioms checkedOriginalCellBank_feasible

end UnifiedLean.G6.RationalNaturalCellWitness
