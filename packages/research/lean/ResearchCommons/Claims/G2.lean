import UnifiedLean.Source.SourceUnrankedAllPanels
import G2ActualTimedAllPanelLaw
import G2TimedOutputForgetting

/-! Typed exports of retained results. These aliases keep every original
hypothesis and conclusion; they add no proof premise or implementation claim. -/
noncomputable section
namespace ResearchCommons.Claims.G2
abbrev complete_unranked_all_panel_projectivity := @UnifiedLean.Source.SourceUnrankedAllPanels.actual_complete_unranked_all_panel_projectivity
abbrev natural_timed_all_panel_projectivity := @GProgram.G2.ActualTimedAllPanelLaw.actual_natural_complete_timed_all_panel_projectivity
abbrev controlled_timed_all_panel_projectivity := @GProgram.G2.ActualTimedAllPanelLaw.actual_controlled_complete_timed_all_panel_projectivity
abbrev natural_timed_forgetting := @GProgram.G2.TimedOutputForgetting.actual_natural_timed_output_forgets
abbrev controlled_timed_forgetting := @GProgram.G2.TimedOutputForgetting.actual_controlled_timed_output_forgets
end ResearchCommons.Claims.G2
