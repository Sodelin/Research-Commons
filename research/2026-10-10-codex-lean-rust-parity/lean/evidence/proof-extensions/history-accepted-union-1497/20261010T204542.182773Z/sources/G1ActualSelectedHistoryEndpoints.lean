import G1FinitePendingActorPromotion

/-! True selected source history/endpoint rows; every original exterior
checkpoint remains joint with its endpoint. Contributor: dot, 2026-10-03. -/
namespace G1ActualSelectedHistoryEndpoints
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open G1ActualJointEpoch G1ActualJointGenerator G1ActualJointProgram G1ActualJointOpaqueContext
open G1ActualJointStageHistory G1UnrankedExteriorHistoryKInsertion
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma actual_selected_history_end (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (v : SelectedIndex N sample keep) :
    (selectedStageHistory N r keep ops v).map (fun tr => tr.getLastD v) = selectedProgram N r keep ops v := by
  obtain ⟨s,hs⟩ := v.property
  have hv : projection N keep s = v := Subtype.ext hs
  rw [←hv,←actual_source_stage_history_projection,PMF.map_comp]
  have hm : (fun tr : List (SelectedIndex N sample keep) => tr.getLastD (projection N keep s)) ∘
      List.map (projection N keep) = projection N keep ∘ (fun tr : List (Code N sample) => tr.getLastD s) := by
    funext tr
    exact List.getLastD_map
  rw [hm,←PMF.map_comp,actual_source_history_end,actual_source_program_projection]

noncomputable def selectedObservedHistory (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (v : SelectedIndex N sample keep) :=
  (selectedStageHistory N r keep ops v).map (fun tr => (tr.getLastD v,tr))

/-- The ACTUAL inner endpoint and EVERY original outside checkpoint factor,
conditional on the real entering state and its SAME register. -/
theorem actual_actor_endpoint_outside_history (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (hsep : SeparatedAgenda N r inside outside ops s) :
    (sourceStageHistory N r ops s).map (fun tr =>
      (projection N inside (tr.getLastD s),
        ((tr.map (projection N outside)).getLastD (projection N outside s),tr.map (projection N outside)))) =
      independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedObservedHistory N r outside ops (projection N outside s)) := by
  have h := congrArg (fun law => law.map (fun data :
      List (SelectedIndex N sample inside) × List (SelectedIndex N sample outside) =>
      (data.1.getLastD (projection N inside s),
        (data.2.getLastD (projection N outside s),data.2))))
    (actual_separated_joint_stage_history N r inside outside ops s hsep)
  simp only [PMF.map_comp,Function.comp_def,List.getLastD_map] at h
  have hp := independentProduct_map
    (selectedStageHistory N r inside ops (projection N inside s))
    (selectedStageHistory N r outside ops (projection N outside s))
    (fun tr => tr.getLastD (projection N inside s))
    (fun tr => (tr.getLastD (projection N outside s),tr))
  rw [hp,actual_selected_history_end] at h
  simpa only [selectedObservedHistory,List.getLastD_map] using h

#print axioms actual_actor_endpoint_outside_history
end G1ActualSelectedHistoryEndpoints
