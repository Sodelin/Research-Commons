import UnifiedLean.Source.SourceForestPulseTransport

/-!
# Same original shared-register pulse under selected genealogy pruning

Contributor: dot, 2026-10-02. COMMON inheritance uses the retained ORIGINAL
hybrid register in both full and selected internal source state. The pulse
commutes deterministically with pruning. It does not marginally replace that
register or claim exterior data/instrumentation access. Random register
initialization and continuous-time/calendar composition remain separate.
-/
namespace UnifiedLean.Source.SourceForestCommonPulse
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestPulseTransport
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def selectedCommonPulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy)
    (keep : Finset Copy) : SelectedView V E Copy :=
  projectedPulse H v keep (fun _ => v.register H.hybrid)

/-- Every current selected block sees the SAME original stored register;
there is no re-coin per copy or fresh marginal component replacement. -/
theorem actual_common_pulse_pruning {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) :
    selectedView (commonPulse H s) keep = selectedCommonPulse H (selectedView s keep) keep := by
  rw [commonPulse,original_pulse_selected_view H s hs keep]
  unfold selectedCommonPulse
  congr 1

#print axioms actual_common_pulse_pruning
end UnifiedLean.Source.SourceForestCommonPulse
