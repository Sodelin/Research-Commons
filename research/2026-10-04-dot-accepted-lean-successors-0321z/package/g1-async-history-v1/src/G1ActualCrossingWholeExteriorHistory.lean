import G1ActualThreePanelSourceHistoryTensor

/-! Crossing original-source actors retain EVERY original exterior checkpoint:
outside A before B opens, outside both during concurrency, outside B after A
closes. All three histories remain joint with the two private outputs.
Contributor: dot, 2026-10-03. -/
namespace G1ActualCrossingWholeExteriorHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceProgramTransport
open G1ActualJointEpoch G1ActualJointGenerator G1ActualJointProgram G1ActualJointStageHistory
open G1ActualJointOpaqueContext G1JointUnrankedForestAssembly G1ActualPurePanelJoin
open G1ActualThreePanelSourceTensor G1ActualSelectedHistoryEndpoints G1ActualThreePanelSourceHistoryTensor
open G1ActualHistoryEnrichedKMacro G1CrossingActorKernelFusion
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev CrossingRecord (N : RootedBinary V E X) (sample : Copy → X) (left right exterior : Finset Copy) :=
  List (SelectedIndex N sample (right ∪ exterior)) × List (SelectedIndex N sample exterior) ×
    List (SelectedIndex N sample (left ∪ exterior)) × SelectedIndex N sample (left ∪ exterior)

noncomputable def actualCrossingHistoryRun (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy)
    (preops concurrent suffix : List (ProgramStep N)) (s : Code N sample) :
    PMF (SelectedIndex N sample left × SelectedIndex N sample right × CrossingRecord N sample left right exterior) :=
  (sourceStageHistory N r preops s).bind (fun first =>
    let p := first.getLastD s
    (sourceStageHistory N r concurrent p).bind (fun middle =>
      let q := middle.getLastD p
      (sourceStageHistory N r suffix q).map (fun last =>
        let z := last.getLastD q
        (projection N left q,projection N right z,
          (first.map (projection N (right ∪ exterior)),middle.map (projection N exterior),
            last.map (projection N (left ∪ exterior)),projection N (left ∪ exterior) z)))))

noncomputable def historyOpenB (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (right exterior : Finset Copy) (preops : List (ProgramStep N))
    (v : SelectedIndex N sample (right ∪ exterior)) :=
  (selectedObservedHistory N r (right ∪ exterior) preops v).map (fun out =>
    ((splitUnion N right exterior out.1).1,((splitUnion N right exterior out.1).2,out.2)))

noncomputable def historyConcurrentOutside (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (right exterior : Finset Copy) (concurrent : List (ProgramStep N))
    (data : SelectedIndex N sample exterior × List (SelectedIndex N sample (right ∪ exterior))) :=
  (selectedObservedHistory N r exterior concurrent data.1).map (fun out => (out.1,data.2,out.2))

noncomputable def historyAfterA (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy) (suffix : List (ProgramStep N))
    (fallback : Code N sample) (data : SelectedIndex N sample left ×
      (SelectedIndex N sample exterior × List (SelectedIndex N sample (right ∪ exterior)) ×
        List (SelectedIndex N sample exterior))) :=
  (selectedObservedHistory N r (left ∪ exterior) suffix
      (joinIndex N left exterior fallback (data.1,data.2.1))).map
    (fun out => (data.2.2.1,data.2.2.2,out.2,out.1))

noncomputable def actualCrossingPendingHistoryRun (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (left right exterior : Finset Copy)
    (preops concurrent suffix : List (ProgramStep N)) (s : Code N sample) :=
  crossingPendingKRun (selectedProgram N r left preops) (selectedProgram N r left concurrent)
    (historyOpenB N r right exterior preops) (selectedProgram N r right concurrent)
    (selectedProgram N r right suffix) (historyConcurrentOutside N r right exterior concurrent)
    (historyAfterA N r left right exterior suffix s)
    (projection N left s) (projection N (right ∪ exterior) s)

/-- Exact full joint history law of the ACTUAL original source. Physical
separation/purity at real supported states is the only source-specific input.
Clock times inside epochs are not newly observed. -/
theorem actual_crossing_source_whole_exterior_history (N : RootedBinary V E X) {sample : Copy → X}
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
    actualCrossingHistoryRun N r left right exterior preops concurrent suffix s =
      actualCrossingPendingHistoryRun N r left right exterior preops concurrent suffix s := by
  let tail := fun prefixPath : List (SelectedIndex N sample (right ∪ exterior)) =>
    fun data : SelectedIndex N sample left × SelectedIndex N sample right ×
        (SelectedIndex N sample exterior × List (SelectedIndex N sample exterior)) =>
      (independentProduct (selectedProgram N r right suffix data.2.1)
        (selectedObservedHistory N r (left ∪ exterior) suffix
          (joinIndex N left exterior s (data.1,data.2.2.1)))).map
          (fun last => (data.1,last.1,(prefixPath,data.2.2.2,last.2.2,last.2.1)))
  have hR (p : Code N sample) (hp : p ∈ (sourceProgram N r preops s).support)
      (middle : List (Code N sample)) (hm : middle ∈ (sourceStageHistory N r concurrent p).support)
      (prefixPath : List (SelectedIndex N sample (right ∪ exterior))) :
    let q := middle.getLastD p
    (sourceStageHistory N r suffix q).map (fun last =>
      (projection N left q,projection N right (last.getLastD q),
        (prefixPath,middle.map (projection N exterior),last.map (projection N (left ∪ exterior)),
          projection N (left ∪ exterior) (last.getLastD q)))) =
      tail prefixPath (projection N left q,projection N right q,
        (projection N exterior q,middle.map (projection N exterior))) := by
    dsimp only
    let q := middle.getLastD p
    have hq := real_history_end_support N r concurrent p middle hm
    have h := congrArg (fun law => law.map (fun out : SelectedIndex N sample right ×
        (SelectedIndex N sample (left ∪ exterior) × List (SelectedIndex N sample (left ∪ exterior))) =>
        (projection N left q,out.1,(prefixPath,middle.map (projection N exterior),out.2.2,out.2.1))))
      (actual_actor_endpoint_outside_history N r right (left ∪ exterior) suffix q (suffixSeparate p hp q hq))
    simp only [PMF.map_comp,Function.comp_def,List.getLastD_map] at h
    rw [h]
    dsimp only [tail]
    have hj := actual_join_index_at_pure_source N left exterior s q (middlePure p hp q hq)
    simp only [jointProjection] at hj
    rw [hj]
  have hQ (p : Code N sample) (hp : p ∈ (sourceProgram N r preops s).support)
      (prefixPath : List (SelectedIndex N sample (right ∪ exterior))) :
      (sourceStageHistory N r concurrent p).bind (fun middle =>
        let q := middle.getLastD p
        (sourceStageHistory N r suffix q).map (fun last =>
          (projection N left q,projection N right (last.getLastD q),
            (prefixPath,middle.map (projection N exterior),last.map (projection N (left ∪ exterior)),
              projection N (left ∪ exterior) (last.getLastD q))))) =
      (independentProduct (selectedProgram N r left concurrent (projection N left p))
        (independentProduct (selectedProgram N r right concurrent (projection N right p))
          (selectedObservedHistory N r exterior concurrent (projection N exterior p)))).bind (tail prefixPath) := by
    calc
      _ = ((sourceStageHistory N r concurrent p).map (fun middle =>
          (projection N left (middle.getLastD p),projection N right (middle.getLastD p),
            (projection N exterior (middle.getLastD p),middle.map (projection N exterior))))).bind
              (tail prefixPath) := by
        rw [PMF.bind_map]
        apply bind_eq_of_eq_on_support
        intro middle hm
        exact hR p hp middle hm prefixPath
      _ = _ := by rw [actual_two_actor_endpoints_exterior_history N r left right exterior concurrent p
        (concurrentFirst p hp) (concurrentOthers p hp)]
  let firstTail := fun data : SelectedIndex N sample left ×
      (SelectedIndex N sample (right ∪ exterior) × List (SelectedIndex N sample (right ∪ exterior))) =>
    (independentProduct (selectedProgram N r left concurrent data.1)
      (independentProduct (selectedProgram N r right concurrent (splitUnion N right exterior data.2.1).1)
        (selectedObservedHistory N r exterior concurrent (splitUnion N right exterior data.2.1).2))).bind
          (tail data.2.2)
  have hMicro : actualCrossingHistoryRun N r left right exterior preops concurrent suffix s =
      crossingMicroRun (selectedProgram N r left preops) (selectedProgram N r left concurrent)
        (historyOpenB N r right exterior preops) (selectedProgram N r right concurrent)
        (selectedProgram N r right suffix) (historyConcurrentOutside N r right exterior concurrent)
        (historyAfterA N r left right exterior suffix s)
        (projection N left s) (projection N (right ∪ exterior) s) := by
    unfold actualCrossingHistoryRun
    calc
      _ = ((sourceStageHistory N r preops s).map (fun first =>
          (projection N left (first.getLastD s),
            (projection N (right ∪ exterior) (first.getLastD s),first.map (projection N (right ∪ exterior)))))).bind
              firstTail := by
        rw [PMF.bind_map]
        apply bind_eq_of_eq_on_support
        intro first hf
        dsimp only [Function.comp_def,firstTail]
        rw [actual_split_union_projection]
        exact hQ (first.getLastD s) (real_history_end_support N r preops s first hf) _
      _ = _ := by
        have hP := actual_actor_endpoint_outside_history N r left (right ∪ exterior) preops s prefixSeparate
        simp only [List.getLastD_map] at hP
        rw [hP]
        simp only [crossingMicroRun,historyOpenB,historyConcurrentOutside,historyAfterA,firstTail,tail,
          independentProduct,PMF.bind_bind,PMF.bind_map,PMF.map_bind,PMF.map_comp,Function.comp_def]
  rw [hMicro,crossing_actual_private_kernels_fuse]
  rfl

#print axioms actual_crossing_source_whole_exterior_history
end G1ActualCrossingWholeExteriorHistory
