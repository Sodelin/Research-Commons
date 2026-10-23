import G6RationalNaturalCellWitness
import G6ActualCellObservedTV

/-! Exact retained typed cell/TV components. Automatic chart/source generation,
provider refinement and effective full certification are separate. -/
noncomputable section
namespace ResearchCommons.Claims.G6
abbrev checked_cell_sound := @UnifiedLean.G6.RationalNaturalCellWitness.checkOriginalCellWitness_sound
abbrev cell_solver_complete := @UnifiedLean.G6.RationalNaturalCellWitness.solveOriginalCell_complete
abbrev checked_physical_bank := @UnifiedLean.G6.RationalNaturalCellWitness.checkedOriginalCellBank
abbrev actual_cell_observed_tv := @UnifiedLean.G6.ActualCellObservedTV.actual_cell_completed_observed_tv
end ResearchCommons.Claims.G6
