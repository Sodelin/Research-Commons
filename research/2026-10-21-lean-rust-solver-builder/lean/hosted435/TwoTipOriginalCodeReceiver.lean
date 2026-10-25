import OriginalCodeChartReceiver
import TwoTipSourceDeclarations
import Mathlib.Tactic.FinCases

/-!
One literal use-site of the existing Code decoder and physical receiver.
The projection prepends only the retained two-tip graph/source declarations
and literal wire source/input, omitting all five original evaluation commands.
No native process or byte-parser/source-origin relation is asserted.
-/
namespace Astra.TwoTipOriginalCodeReceiver

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.RationalNaturalCellWitness UnifiedLean.G6.WireAffineRefinement
open Astra.OriginalCodeChartReflection Astra.OriginalCodeChartReceiver

abbrev retainedSource := UnifiedLean.G6.TwoTipChartFixture.source

/-- Expected fixture positions, without relying on `encode` numbering. -/
def code : Code (Fin 2) (Fin 0) :=
  (fun _ => ⟨0, by simp [vertexCount]⟩, fun e => e.succ,
    ⟨0, by simp [vertexCount]⟩, Fin.succ, Fin.elim0, Fin.elim0)

theorem binary_valid : BinaryValid code := by
  exact ⟨retainedSource.leaf.injective, retainedSource.at_least_two_taxa,
    retainedSource.root_degrees, retainedSource.leaf_degrees,
    retainedSource.internal_degrees, retainedSource.acyclic,
    retainedSource.rooted, retainedSource.least_stable⟩

theorem registry_valid : RegistryValid code := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro a ha
    exact False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid ⟨a, ha⟩)
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

theorem cut_child : CutChild code := by
  intro e he
  exact False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid ⟨_, he⟩)

theorem decoded_source_eq : sourceOfValid code binary_valid = retainedSource := by
  rfl

def taxonOrder : Fin 2 ≃ Fin 2 := Equiv.refl _
def idOrder : Fin 0 ≃ Fin 0 := Equiv.refl _
def chronology : Fin 0 → AgeConstraint (Fin 3) := Fin.elim0
def exposures : Fin 0 → Exposure (Fin 3) (Fin 2) := Fin.elim0
def coins : Hybrid (sourceOfValid code binary_valid) → RationalInterval :=
  fun h => False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid h)

theorem source_fields_exact :
    sourceOfCode code taxonOrder idOrder = UnifiedLean.G6.TwoTipChartFixture.nativeSource := by
  rfl

theorem input_fields_exact :
    inputOfCode code binary_valid registry_valid taxonOrder idOrder
      chronology exposures coins 4096 = UnifiedLean.G6.TwoTipChartFixture.nativeInput := by
  rfl

theorem original_rows_exact :
    (decodeRows 6 (GParity.Chart.emitRows UnifiedLean.G6.TwoTipChartFixture.nativeInput)).toFinset =
      compileCell (sourceOfValid code binary_valid)
        (Astra.OriginalCodeBankLayout.layout code binary_valid registry_valid idOrder)
        chronology exposures coins := by
  rw [← input_fields_exact]
  exact decoded_emitRows_toFinset_of_code code binary_valid registry_valid taxonOrder idOrder
    chronology exposures coins 4096

theorem supplied_witness_checked (x : List Rat)
    (hx : GParity.Affine.checkWitness 6
      (GParity.Chart.emitRows UnifiedLean.G6.TwoTipChartFixture.nativeInput) x = true) :
    GParity.Affine.checkWitness 6
      (GParity.Chart.emitRows (inputOfCode code binary_valid registry_valid taxonOrder idOrder
        chronology exposures coins 4096)) x = true := by
  rw [input_fields_exact]
  exact hx

noncomputable def bank (x : List Rat)
    (hx : GParity.Affine.checkWitness 6
      (GParity.Chart.emitRows UnifiedLean.G6.TwoTipChartFixture.nativeInput) x = true) :
    OriginalCellBank (sourceOfValid code binary_valid)
    chronology exposures coins :=
  checked_original_bank code binary_valid registry_valid taxonOrder idOrder
    chronology exposures coins 4096 x (supplied_witness_checked x hx)

theorem original_cell_feasible (x : List Rat)
    (hx : GParity.Affine.checkWitness 6
      (GParity.Chart.emitRows UnifiedLean.G6.TwoTipChartFixture.nativeInput) x = true) :
    originalCellFeasible (sourceOfValid code binary_valid) chronology exposures coins :=
  checked_original_bank_feasible code binary_valid registry_valid taxonOrder idOrder
    chronology exposures coins 4096 x (supplied_witness_checked x hx)

end Astra.TwoTipOriginalCodeReceiver
