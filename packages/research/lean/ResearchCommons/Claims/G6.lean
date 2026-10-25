import G6RationalNaturalCellWitness
import G6ActualCellObservedTV
import G6OriginalWholeEdgeChartConsumer

/-! Exact retained typed cell/TV components. Automatic chart/source generation,
provider refinement and effective full certification are separate. -/
noncomputable section
namespace ResearchCommons.Claims.G6
abbrev checked_cell_sound := @UnifiedLean.G6.RationalNaturalCellWitness.checkOriginalCellWitness_sound
abbrev cell_solver_complete := @UnifiedLean.G6.RationalNaturalCellWitness.solveOriginalCell_complete
abbrev checked_physical_bank := @UnifiedLean.G6.RationalNaturalCellWitness.checkedOriginalCellBank
abbrev actual_cell_observed_tv := @UnifiedLean.G6.ActualCellObservedTV.actual_cell_completed_observed_tv
abbrev rational_witness_sound := @UnifiedLean.G6.RationalAffineWitness.solveRational_sound
abbrev rational_witness_complete := @UnifiedLean.G6.RationalAffineWitness.solveRational_complete
abbrev rational_witness_none := @UnifiedLean.G6.RationalAffineWitness.solveRational_none_iff
abbrev ordered_list_refinement := @UnifiedLean.G6.RationalAffineWitness.solveList_eq_solveRational
abbrev whole_edge_coin_chart := @GProgram.G6.OriginalWholeEdgeChartConsumer.whole_edge_original_coin_chart
end ResearchCommons.Claims.G6
