import G7ExactLawResourceGame
import G7ExactLawRankCompression
import G7OriginalFamilyStrategy

/-! Typed exports of retained results. These aliases keep every original
hypothesis and conclusion; they add no proof premise or implementation claim. -/
noncomputable section
namespace ResearchCommons.Claims.G7
abbrev winning_iff_valid_plan := @GProgram.G7.ExactLawResourceGame.winning_iff_valid_plan
abbrev valid_run_identifies := @GProgram.G7.ExactLawResourceGame.valid_run_identifies
abbrev losing_history_pair := @GProgram.G7.ExactLawResourceGame.losing_has_full_history_pair
abbrev total_policy_finite_horizon := @GProgram.G7.ExactLawRankCompression.pointwise_total_strategy_has_finite_informative_horizon
abbrev rank_budget := @GProgram.G7.ExactLawRankCompression.total_strategy_wins_with_rank_budget
abbrev actual_original_policy_plan := @GProgram.G7.OriginalFamilyStrategy.actual_total_original_strategy_has_bounded_plan
abbrev actual_budget_exclusion := @GProgram.G7.OriginalFamilyStrategy.actual_losing_budget_excludes_total_policy
end ResearchCommons.Claims.G7
