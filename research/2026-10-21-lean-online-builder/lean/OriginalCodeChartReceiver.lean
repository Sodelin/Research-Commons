import OriginalCodeChartReflection
import G6NaturalCellOrderedCompiler

/-!
Compose the literal original Code/CHART field construction with the EXISTING
wire certificate and physical-bank receivers. No parser, native validator,
source observation, bounded-search completeness or all-source NO is asserted.
The external contradiction vector still has one entry per ORIGINAL wire row.
-/
namespace Astra.OriginalCodeChartReceiver

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.RationalAffineWitness
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.RationalNaturalCellWitness UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.G6.WireContradictionRefinement
open Astra.OriginalCodeChartReflection

variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]
variable {nt nh nc ni : ℕ}
variable (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
variable (taxonOrder : X ≃ Fin nt) (idOrder : ID ≃ Fin nh)
variable (chronology : Fin nc → AgeConstraint (NV (X:=X) (ID:=ID)))
variable (exposures : Fin ni → Exposure (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)))
variable (coins : Hybrid (sourceOfValid c hb) → RationalInterval) (cap : ℕ)

local notation "D" => vertexCount (Fintype.card X) (Fintype.card ID) +
  edgeCount (Fintype.card X) (Fintype.card ID) + 1 + nh
local notation "N" => sourceOfValid c hb
local notation "L" => Astra.OriginalCodeBankLayout.layout c hb hr idOrder
local notation "R" => GParity.Chart.emitRows
  (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap)

theorem checked_original_witness (x : List Rat)
    (hx : GParity.Affine.checkWitness D R x = true) :
    checkOriginalCellWitness N L chronology exposures coins (decodeVector D x) = true := by
  apply (checkRationalWitness_correct _ _).mpr
  have h := ((checkWitness_correct D R
    (coefficient_lengths_of_code c hb hr taxonOrder idOrder chronology exposures coins cap)
    x).mp hx).2
  simpa only [decoded_emitRows_toFinset_of_code c hb hr taxonOrder idOrder
    chronology exposures coins cap] using h

/-- Ages and inheritance are the same returned coordinates; rates are their
positive reciprocals, using the existing original physical carriers. -/
noncomputable def checked_original_bank (x : List Rat)
    (hx : GParity.Affine.checkWitness D R x = true) :
    OriginalCellBank N chronology exposures coins :=
  checkedOriginalCellBank N L chronology exposures coins (decodeVector D x)
    (checked_original_witness c hb hr taxonOrder idOrder chronology exposures coins cap x hx)

theorem checked_original_bank_rates (x : List Rat)
    (hx : GParity.Affine.checkWitness D R x = true) (e : Option (NE (X:=X) (ID:=ID))) :
    pairRate (checked_original_bank c hb hr taxonOrder idOrder chronology exposures coins cap
      x hx).rates e = (inverseRatesOf N L (fun i => (decodeVector D x i : ℝ)) e)⁻¹ := by
  exact checkedOriginalCellBank_rates N L chronology exposures coins (decodeVector D x)
    (checked_original_witness c hb hr taxonOrder idOrder chronology exposures coins cap x hx) e

theorem checked_original_bank_feasible (x : List Rat)
    (hx : GParity.Affine.checkWitness D R x = true) :
    originalCellFeasible N chronology exposures coins :=
  checkedOriginalCellBank_feasible N L chronology exposures coins (decodeVector D x)
    (checked_original_witness c hb hr taxonOrder idOrder chronology exposures coins cap x hx)

/-- This excludes only the supplied original source CELL, with the complete
ordered external vector. It excludes no unenumerated source or chart. -/
theorem checked_original_exclusion (weights : List Rat)
    (hlen : weights.length = (R).length)
    (hx : GParity.Affine.checkContradiction D R weights = true) :
    ¬ originalCellFeasible N chronology exposures coins := by
  have hn := checkedWireContradiction_excludes_real D R
    (coefficient_lengths_of_code c hb hr taxonOrder idOrder chronology exposures coins cap)
    weights hlen hx
  intro ho
  apply hn
  rw [decoded_emitRows_toFinset_of_code c hb hr taxonOrder idOrder chronology exposures coins cap]
  exact (inverse_cell_iff_compiled N L chronology exposures coins).mp
    ((original_cell_iff_inverse N chronology exposures coins).mp ho)

end Astra.OriginalCodeChartReceiver
