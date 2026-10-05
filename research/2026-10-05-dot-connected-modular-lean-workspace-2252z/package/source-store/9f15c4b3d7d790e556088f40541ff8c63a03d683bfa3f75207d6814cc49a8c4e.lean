import G1ActualSelectedHistoryEndpoints

/-! Actual three-panel joint checkpoint-history tensor; no marginal-only
replacement or static exterior parameter. -/
namespace G1ActualThreePanelSourceHistoryTensor
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open G1ActualJointEpoch G1ActualJointGenerator G1ActualJointProgram G1ActualJointOpaqueContext
open G1ActualJointStageHistory G1ActualSelectedHistoryEndpoints G1NestedOriginalSourceProjection
open G1ActualThreePanelSourceTensor
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def splitUnionHistory (N : RootedBinary V E X) {sample : Copy → X}
    (left right : Finset Copy) (tr : List (SelectedIndex N sample (left ∪ right))) :=
    (tr.map (subIndex N left (left ∪ right) Finset.subset_union_left),
      tr.map (subIndex N right (left ∪ right) Finset.subset_union_right))

lemma actual_split_union_source_history (N : RootedBinary V E X) {sample : Copy → X}
    (left right : Finset Copy) (tr : List (Code N sample)) :
    splitUnionHistory N left right (tr.map (projection N (left ∪ right))) =
      (tr.map (projection N left),tr.map (projection N right)) := by
  apply Prod.ext
  all_goals simp only [splitUnionHistory,List.map_map,Function.comp_def]
  all_goals apply List.map_congr_left
  all_goals intro s _
  all_goals exact actual_subindex_projection N _ _ _ s

theorem actual_three_panel_stage_history (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (first second third : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample)
    (firstSeparate : SeparatedAgenda N r first (second ∪ third) ops s)
    (otherSeparate : SeparatedAgenda N r second third ops s) :
    (sourceStageHistory N r ops s).map (fun tr =>
      (tr.map (projection N first),tr.map (projection N second),tr.map (projection N third))) =
      independentProduct (selectedStageHistory N r first ops (projection N first s))
        (independentProduct (selectedStageHistory N r second ops (projection N second s))
          (selectedStageHistory N r third ops (projection N third s))) := by
  have hUnion : (selectedStageHistory N r (second ∪ third) ops (projection N (second ∪ third) s)).map
      (splitUnionHistory N second third) =
      independentProduct (selectedStageHistory N r second ops (projection N second s))
        (selectedStageHistory N r third ops (projection N third s)) := by
    rw [←actual_source_stage_history_projection,PMF.map_comp]
    have hfun : splitUnionHistory N (sample := sample) second third ∘
        List.map (projection N (second ∪ third)) =
        fun tr => (tr.map (projection N second),tr.map (projection N third)) := by
      funext tr
      exact actual_split_union_source_history N second third tr
    rw [hfun]
    exact actual_separated_joint_stage_history N r second third ops s otherSeparate
  calc
    _ = ((sourceStageHistory N r ops s).map (fun tr =>
        (tr.map (projection N first),tr.map (projection N (second ∪ third))))).map
          (fun data => (data.1,splitUnionHistory N second third data.2)) := by
      rw [PMF.map_comp]
      congr 1
      funext tr
      simp only [Function.comp_def,actual_split_union_source_history]
    _ = _ := by
      rw [actual_separated_joint_stage_history N r first (second ∪ third) ops s firstSeparate,
        product_map_right,hUnion]

/-- Both private endpoints and every exterior checkpoint remain JOINT under
the three real source marginals, including complete labelled clades/Γ. -/
theorem actual_two_actor_endpoints_exterior_history (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (first second third : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample)
    (firstSeparate : SeparatedAgenda N r first (second ∪ third) ops s)
    (otherSeparate : SeparatedAgenda N r second third ops s) :
    (sourceStageHistory N r ops s).map (fun tr =>
      (projection N first (tr.getLastD s),projection N second (tr.getLastD s),
        (projection N third (tr.getLastD s),tr.map (projection N third)))) =
      independentProduct (selectedProgram N r first ops (projection N first s))
        (independentProduct (selectedProgram N r second ops (projection N second s))
          (selectedObservedHistory N r third ops (projection N third s))) := by
  have h := congrArg (fun law => law.map (fun data : List (SelectedIndex N sample first) ×
      (List (SelectedIndex N sample second) × List (SelectedIndex N sample third)) =>
      (data.1.getLastD (projection N first s),data.2.1.getLastD (projection N second s),
        (data.2.2.getLastD (projection N third s),data.2.2))))
    (actual_three_panel_stage_history N r first second third ops s firstSeparate otherSeparate)
  simp only [PMF.map_comp,Function.comp_def,List.getLastD_map] at h
  have hOuter := independentProduct_map
    (selectedStageHistory N r first ops (projection N first s))
    (independentProduct (selectedStageHistory N r second ops (projection N second s))
      (selectedStageHistory N r third ops (projection N third s)))
    (fun tr => tr.getLastD (projection N first s))
    (fun data => (data.1.getLastD (projection N second s),
      (data.2.getLastD (projection N third s),data.2)))
  have hInner := independentProduct_map
    (selectedStageHistory N r second ops (projection N second s))
    (selectedStageHistory N r third ops (projection N third s))
    (fun tr => tr.getLastD (projection N second s))
    (fun tr => (tr.getLastD (projection N third s),tr))
  rw [hOuter,hInner,actual_selected_history_end,actual_selected_history_end] at h
  simpa only [selectedObservedHistory] using h

#print axioms actual_two_actor_endpoints_exterior_history
end G1ActualThreePanelSourceHistoryTensor
