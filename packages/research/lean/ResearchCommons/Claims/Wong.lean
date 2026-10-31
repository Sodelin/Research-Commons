import WongMarkedDated
import WongDatedSupport

/-! Continuous-breakpoint actual dated-history endpoints, reused verbatim.
This is not a discrete-link model or a production simulator. -/
noncomputable section
namespace ResearchCommons.Claims.Wong
abbrev intrinsic_count_time_law := @WongMarkedDated.history_count_time_projection
abbrev measurable_valid_history := @WongDatedSupport.measurable_validDated
abbrev actual_history_support := @WongDatedSupport.historyLaw_ae_validDated
end ResearchCommons.Claims.Wong
