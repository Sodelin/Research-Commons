import G1ActualThreePanelSourceTensor

/-! A source-derived union representative for two physically pure original
panels. No fitted union state or output-law equality is supplied. -/
namespace G1ActualPurePanelJoin
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning
open G1ActualJointGenerator G1JointUnrankedForestAssembly G1SameOriginalExteriorContinuation
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def joinIndex (N : RootedBinary V E X) {sample : Copy → X}
    (left right : Finset Copy) (fallback : Code N sample)
    (data : SelectedIndex N sample left × SelectedIndex N sample right) :
    SelectedIndex N sample (left ∪ right) :=
  if h : ∃ s : Code N sample, PrunedPanelSeparated (state s) left right ∧
      jointProjection N left right s = data then projection N (left ∪ right) (Classical.choose h)
  else projection N (left ∪ right) fallback

/-- True supported pure source interfaces reconstruct the full union selected
state, including original labelled clades/populations/SAME exposed register. -/
theorem actual_join_index_at_pure_source (N : RootedBinary V E X) {sample : Copy → X}
    (left right : Finset Copy) (fallback s : Code N sample)
    (hpure : PrunedPanelSeparated (state s) left right) :
    joinIndex N left right fallback (jointProjection N left right s) = projection N (left ∪ right) s := by
  have hw : ∃ z : Code N sample, PrunedPanelSeparated (state z) left right ∧
      jointProjection N left right z = jointProjection N left right s := ⟨s,hpure,rfl⟩
  rw [joinIndex,dif_pos hw]
  apply Subtype.ext
  change selectedView (state (Classical.choose hw)) (left ∪ right) = selectedView (state s) (left ∪ right)
  have ha : selectedView (state (Classical.choose hw)) (left ∪ right) =
      joinedPanelView left (selectedView (state (Classical.choose hw)) left,
        selectedView (state (Classical.choose hw)) right) :=
    actual_joined_panel_view _ (Classical.choose hw).property.forest left right (Classical.choose_spec hw).1
  have hs : selectedView (state s) (left ∪ right) =
      joinedPanelView left (selectedView (state s) left,selectedView (state s) right) :=
    actual_joined_panel_view _ s.property.forest left right hpure
  have heq := congrArg (fun v : SelectedIndex N sample left × SelectedIndex N sample right =>
    (v.1.val,v.2.val)) (Classical.choose_spec hw).2
  change (selectedView (state (Classical.choose hw)) left,selectedView (state (Classical.choose hw)) right) =
    (selectedView (state s) left,selectedView (state s) right) at heq
  exact ha.trans ((congrArg (joinedPanelView left) heq).trans hs.symm)

#print axioms actual_join_index_at_pure_source
end G1ActualPurePanelJoin
