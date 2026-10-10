import G1SameOriginalExteriorContinuation

/-!
# Complete actual original-stage history at the joint interface

Contributor: dot, 2026-10-03. Records every original agenda checkpoint's whole
genealogy/population/SAME-register state. Exterior stage history is not replaced
by a static parameter or inferred from only its terminal forest. Individual
within-epoch clock/event times are outside the accepted unranked G1 contract.
-/
namespace G1ActualJointStageHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport
open G1ActualJointGenerator G1ActualJointEpoch G1ActualJointBoundary G1ActualJointProgram
open G1ActualJointOpaqueContext
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def sourceStageHistory (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N) → Code N sample → PMF (List (Code N sample))
  | [], s => PMF.pure [s]
  | op :: ops, s => (sourceProgramStep N r op s).bind (fun d =>
      (sourceStageHistory N r ops d).map (List.cons s))

noncomputable def selectedStageHistory (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    List (ProgramStep N) → SelectedIndex N sample keep → PMF (List (SelectedIndex N sample keep))
  | [], v => PMF.pure [v]
  | op :: ops, v => (selectedProgramStep N r keep op v).bind (fun w =>
      (selectedStageHistory N r keep ops w).map (List.cons v))

theorem actual_source_stage_history_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceStageHistory N r ops s).map (List.map (projection N keep)) =
      selectedStageHistory N r keep ops (projection N keep s) := by
  induction ops generalizing s with
  | nil => simp [sourceStageHistory,selectedStageHistory,PMF.pure_map]
  | cons op ops ih =>
      rw [sourceStageHistory,PMF.map_bind]
      have hcons (d : Code N sample) :
          ((sourceStageHistory N r ops d).map (List.cons s)).map (List.map (projection N keep)) =
            (selectedStageHistory N r keep ops (projection N keep d)).map (List.cons (projection N keep s)) := by
        rw [PMF.map_comp]
        have he : List.map (projection N keep) ∘ List.cons s =
            List.cons (projection N keep s) ∘ List.map (projection N keep) := by funext l; rfl
        rw [he,← PMF.map_comp,ih]
      simp_rw [hcons]
      change (sourceProgramStep N r op s).bind
        ((fun v => (selectedStageHistory N r keep ops v).map (List.cons (projection N keep s))) ∘ projection N keep) = _
      rw [← PMF.bind_map,actual_program_step_projection]
      rfl

/-- The entire joint original-stage trajectory has the product of the two
actual selected source-history laws, conditional on the entering state. -/
theorem actual_separated_joint_stage_history (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (hagenda : SeparatedAgenda N r inside outside ops s) :
    (sourceStageHistory N r ops s).map (fun tr =>
        (tr.map (projection N inside),tr.map (projection N outside))) =
      independentProduct (selectedStageHistory N r inside ops (projection N inside s))
        (selectedStageHistory N r outside ops (projection N outside s)) := by
  induction ops generalizing s with
  | nil => simp [sourceStageHistory,selectedStageHistory,PMF.pure_map,independentProduct_pure]
  | cons op ops ih =>
      obtain ⟨hsep,htail⟩ := hagenda
      rw [sourceStageHistory,PMF.map_bind]
      let prepend := fun v : List (SelectedIndex N sample inside) × List (SelectedIndex N sample outside) =>
        (projection N inside s :: v.1,projection N outside s :: v.2)
      calc
        _ = (sourceProgramStep N r op s).bind (fun d =>
            (independentProduct (selectedStageHistory N r inside ops (projection N inside d))
              (selectedStageHistory N r outside ops (projection N outside d))).map prepend) := by
          apply bind_eq_of_eq_on_support
          intro d hd
          rw [PMF.map_comp]
          have he : (fun tr : List (Code N sample) =>
              (tr.map (projection N inside),tr.map (projection N outside))) ∘ List.cons s =
              prepend ∘ (fun tr => (tr.map (projection N inside),tr.map (projection N outside))) := by
            funext tr
            rfl
          rw [he,← PMF.map_comp,ih d (htail d hd)]
        _ = ((sourceProgramStep N r op s).map (jointProjection N inside outside)).bind (fun v =>
            independentProduct
              ((selectedStageHistory N r inside ops v.1).map (List.cons (projection N inside s)))
              ((selectedStageHistory N r outside ops v.2).map (List.cons (projection N outside s)))) := by
          rw [PMF.bind_map]
          simp only [prepend,independentProduct_map,Function.comp_def,jointProjection]
        _ = _ := by
          rw [actual_separated_joint_step_law N r inside outside op s hsep]
          rw [independentProduct_bind
            (selectedProgramStep N r inside op (projection N inside s))
            (selectedProgramStep N r outside op (projection N outside s))
            (fun v => (selectedStageHistory N r inside ops v).map (List.cons (projection N inside s)))
            (fun v => (selectedStageHistory N r outside ops v).map (List.cons (projection N outside s)))]
          rfl

/-- Exact product of ACTUAL original-source marginal stage histories, rather
than an abstract independent process fitted only to terminal marginals. -/
theorem actual_joint_exterior_history_retained (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (hagenda : SeparatedAgenda N r inside outside ops s) :
    (sourceStageHistory N r ops s).map (fun tr =>
        (tr.map (projection N inside),tr.map (projection N outside))) =
      independentProduct
        ((sourceStageHistory N r ops s).map (List.map (projection N inside)))
        ((sourceStageHistory N r ops s).map (List.map (projection N outside))) := by
  rw [actual_source_stage_history_projection,actual_source_stage_history_projection]
  exact actual_separated_joint_stage_history N r inside outside ops s hagenda

#print axioms actual_separated_joint_stage_history
#print axioms actual_joint_exterior_history_retained
end G1ActualJointStageHistory
