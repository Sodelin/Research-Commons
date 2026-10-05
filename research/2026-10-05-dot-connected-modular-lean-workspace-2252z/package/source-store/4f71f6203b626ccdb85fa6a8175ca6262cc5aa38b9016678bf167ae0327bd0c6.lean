import G1ActualPurePanelJoin

/-! Actual original-source crossing-window fusion. Two private actors span
three chronological windows: A opens first, B opens later, A closes first,
then B closes. Original time/outside processing is never duplicated.
Contributor: dot, 2026-10-03. -/
namespace G1ActualCrossingSourcePendingFusion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open G1ActualJointEpoch G1ActualJointGenerator G1ActualJointProgram
open G1JointUnrankedForestAssembly G1ActualThreePanelSourceTensor G1ActualPurePanelJoin
open G1CrossingActorKernelFusion
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def actualCrossingMarkedRun (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy)
    (preops concurrent suffix : List (ProgramStep N)) (s : Code N sample) :=
  (sourceProgram N r preops s).bind (fun p =>
    (sourceProgram N r concurrent p).bind (fun q =>
      (sourceProgram N r suffix q).map (fun z =>
        (projection N left q,projection N right z,projection N (left ∪ exterior) z))))

noncomputable def actualCrossingPendingRun (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy)
    (preops concurrent suffix : List (ProgramStep N)) (s : Code N sample) :=
  crossingPendingKRun (selectedProgram N r left preops) (selectedProgram N r left concurrent)
    (fun v => (selectedProgram N r (right ∪ exterior) preops v).map (splitUnion N right exterior))
    (selectedProgram N r right concurrent) (selectedProgram N r right suffix)
    (selectedProgram N r exterior concurrent)
    (fun data => selectedProgram N r (left ∪ exterior) suffix (joinIndex N left exterior s data))
    (projection N left s) (projection N (right ∪ exterior) s)

/-- Exact actual source law with both full private actor kernels held pending.
Hypotheses are only physical original population/forest separation at real
reachable states; no source-kernel/output equality is admitted. -/
theorem actual_crossing_source_pending_fusion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy)
    (preops concurrent suffix : List (ProgramStep N)) (s : Code N sample)
    (prefixSeparate : SeparatedAgenda N r left (right ∪ exterior) preops s)
    (concurrentFirst : ∀ p ∈ (sourceProgram N r preops s).support,
      SeparatedAgenda N r left (right ∪ exterior) concurrent p)
    (concurrentOthers : ∀ p ∈ (sourceProgram N r preops s).support,
      SeparatedAgenda N r right exterior concurrent p)
    (suffixSeparate : ∀ p ∈ (sourceProgram N r preops s).support,
      ∀ q ∈ (sourceProgram N r concurrent p).support,
      SeparatedAgenda N r right (left ∪ exterior) suffix q)
    (middlePure : ∀ p ∈ (sourceProgram N r preops s).support,
      ∀ q ∈ (sourceProgram N r concurrent p).support,
      PrunedPanelSeparated (state q) left exterior) :
    actualCrossingMarkedRun N r left right exterior preops concurrent suffix s =
      actualCrossingPendingRun N r left right exterior preops concurrent suffix s := by
  let afterA := fun data : SelectedIndex N sample left × SelectedIndex N sample exterior =>
    selectedProgram N r (left ∪ exterior) suffix (joinIndex N left exterior s data)
  let tail := fun data : SelectedIndex N sample left ×
      (SelectedIndex N sample right × SelectedIndex N sample exterior) =>
    (independentProduct (selectedProgram N r right suffix data.2.1) (afterA (data.1,data.2.2))).map
      (fun last => (data.1,last.1,last.2))
  have hR (p : Code N sample) (hp : p ∈ (sourceProgram N r preops s).support)
      (q : Code N sample) (hq : q ∈ (sourceProgram N r concurrent p).support) :
      (sourceProgram N r suffix q).map (fun z =>
        (projection N left q,projection N right z,projection N (left ∪ exterior) z)) =
        tail (tripleProjection N left right exterior q) := by
    have h := congrArg (fun law => law.map (fun last => (projection N left q,last.1,last.2)))
      (actual_separated_joint_program_law N r right (left ∪ exterior) suffix q (suffixSeparate p hp q hq))
    simp only [PMF.map_comp,Function.comp_def,jointProjection] at h
    rw [h]
    dsimp only [tail,afterA,tripleProjection,jointProjection]
    have hjoin := actual_join_index_at_pure_source N left exterior s q (middlePure p hp q hq)
    simp only [jointProjection] at hjoin
    rw [hjoin]
  have hQ (p : Code N sample) (hp : p ∈ (sourceProgram N r preops s).support) :
      (sourceProgram N r concurrent p).bind (fun q =>
        (sourceProgram N r suffix q).map (fun z =>
          (projection N left q,projection N right z,projection N (left ∪ exterior) z))) =
      (independentProduct (selectedProgram N r left concurrent (projection N left p))
        (independentProduct (selectedProgram N r right concurrent (projection N right p))
          (selectedProgram N r exterior concurrent (projection N exterior p)))).bind tail := by
    calc
      _ = (sourceProgram N r concurrent p).bind (tail ∘ tripleProjection N left right exterior) :=
        bind_eq_of_eq_on_support _ _ _ (fun q hq => hR p hp q hq)
      _ = _ := by
        rw [←PMF.bind_map,actual_three_panel_source_program N r left right exterior concurrent p
          (concurrentFirst p hp) (concurrentOthers p hp)]
  let middle := fun first : SelectedIndex N sample left × SelectedIndex N sample (right ∪ exterior) =>
    (independentProduct (selectedProgram N r left concurrent first.1)
      (independentProduct (selectedProgram N r right concurrent (splitUnion N right exterior first.2).1)
        (selectedProgram N r exterior concurrent (splitUnion N right exterior first.2).2))).bind tail
  have hMicro : actualCrossingMarkedRun N r left right exterior preops concurrent suffix s =
      crossingMicroRun (selectedProgram N r left preops) (selectedProgram N r left concurrent)
        (fun v => (selectedProgram N r (right ∪ exterior) preops v).map (splitUnion N right exterior))
        (selectedProgram N r right concurrent) (selectedProgram N r right suffix)
        (selectedProgram N r exterior concurrent) afterA
        (projection N left s) (projection N (right ∪ exterior) s) := by
    unfold actualCrossingMarkedRun
    calc
      _ = (sourceProgram N r preops s).bind (middle ∘ jointProjection N left (right ∪ exterior)) := by
        apply bind_eq_of_eq_on_support
        intro p hp
        dsimp only [Function.comp_def,middle,jointProjection]
        rw [actual_split_union_projection]
        exact hQ p hp
      _ = _ := by
        rw [←PMF.bind_map,actual_separated_joint_program_law N r left (right ∪ exterior) preops s prefixSeparate]
        simp only [crossingMicroRun,middle,tail,independentProduct,PMF.bind_bind,PMF.bind_map,
          PMF.map_bind,PMF.map_comp,Function.comp_def]
  rw [hMicro,crossing_actual_private_kernels_fuse]
  rfl

#print axioms actual_crossing_source_pending_fusion
end G1ActualCrossingSourcePendingFusion
