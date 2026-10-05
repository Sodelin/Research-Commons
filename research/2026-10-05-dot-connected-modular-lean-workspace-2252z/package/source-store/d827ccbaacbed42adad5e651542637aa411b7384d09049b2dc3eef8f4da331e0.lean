import G1OriginalCalendarDecomposition

/-! Literal three-epoch decomposition of the original canonical component phase.
Contributor: dot, 2026-10-03. This is list/date algebra of the unchanged compiler. -/
namespace G1CanonicalThreeEpochList
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarTiming
open G1InitializedFrontierPrefix G1CanonicalComponentSegment G1OriginalCalendarDecomposition
open G1ActualTwoPortBlob
open scoped Classical NNReal
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

/-- Stop BEFORE the final batch, while retaining the complete middle batch. -/
theorem actual_stop_tail_middle_cut (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (dates : List ℝ) (horder : dates.Pairwise (· < ·)) (middle final : ℝ)
    (hmiddle : middle ∈ dates) (hmf : middle < final) (a : ℝ) :
    stopBeforeTail N C H gamma common final a dates =
      stopBeforeTail N C H gamma common middle a dates ++
      boundaryOperations N C H gamma common middle ++
      stopBeforeTail N C H gamma common final middle
        (dates.filter (fun c => decide (middle < c))) := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hmiddle)
  | cons c cs ih =>
      have hp := List.pairwise_cons.mp horder
      by_cases hc : c = middle
      · subst c
        rw [filter_after_head hp.1]
        simp [stopBeforeTail,ne_of_lt hmf,List.append_assoc]
      · have hm : middle ∈ cs := (List.mem_cons.mp hmiddle).resolve_left (Ne.symm hc)
        have hcm := hp.1 _ hm
        have hcf : c ≠ final := ne_of_lt (hcm.trans hmf)
        have hnot : ¬ middle < c := not_lt_of_gt hcm
        have hfilter : (c::cs).filter (fun d => decide (middle < d)) =
            cs.filter (fun d => decide (middle < d)) := by simp [hnot]
        rw [hfilter]
        simp only [stopBeforeTail,if_neg hc,if_neg hcf,List.cons_append]
        rw [ih hp.2 hm c]
        simp only [List.append_assoc]

noncomputable def afterDate (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) : List ℝ :=
  (sortedOriginalDates N C).filter (fun c => decide (a < c))

lemma original_after_ordered (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) :
    (afterDate N C a).Pairwise (· < ·) := (original_dates_strict N C).filter _

lemma original_after_member (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) (v : V)
    (hav : a < C.age v) : C.age v ∈ afterDate N C a := by
  simp only [afterDate,List.mem_filter,decide_eq_true_eq]
  exact ⟨original_date_scheduled N C v,hav⟩

/-- The canonical agenda has precisely the three original component epochs,
with full H and U batches and the closing A0 exit prefix. All other dates
remain interleaved inside the three stop tails. -/
theorem actual_component_agenda_three_epochs (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    componentAgenda N C b A H gamma common =
      nodeOperations N C H gamma common (C.age (N.graph.target A.child)) ++
      stopBeforeTail N C H gamma common (C.age A.fragment.parents.hybrid)
        (C.age (N.graph.target A.child)) (afterDate N C (C.age (N.graph.target A.child))) ++
      (originalExits N C (C.age A.fragment.parents.hybrid)).map (fun e => .boundary (.exit e)) ++
      nodeOperations N C H gamma common (C.age A.fragment.parents.hybrid) ++
      stopBeforeTail N C H gamma common (C.age A.fragment.upper)
        (C.age A.fragment.parents.hybrid) (afterDate N C (C.age A.fragment.parents.hybrid)) ++
      (originalExits N C (C.age A.fragment.upper)).map (fun e => .boundary (.exit e)) ++
      nodeOperations N C H gamma common (C.age A.fragment.upper) ++
      stopBeforeTail N C H gamma common (C.age (N.graph.source A.entry))
        (C.age A.fragment.upper) (afterDate N C (C.age A.fragment.upper)) ++
      ((exitsBeforeEntry N C b A) ++ [A.entry]).map (fun e => .boundary (.exit e)) := by
  have hDH : C.age (N.graph.target A.child) < C.age A.fragment.parents.hybrid := by
    simpa only [A.child_source] using C.edge_older A.child
  have hHU : C.age A.fragment.parents.hybrid < C.age A.fragment.upper := by
    simpa only [A.fragment.parents.target0,show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false] using C.edge_older A.fragment.parents.parent0
  have hUA : C.age A.fragment.upper < C.age (N.graph.source A.entry) := by
    simpa only [A.entry_target] using C.edge_older A.entry
  have h1 := actual_stop_tail_middle_cut N C H gamma common
    (afterDate N C (C.age (N.graph.target A.child))) (original_after_ordered N C _)
    (C.age A.fragment.parents.hybrid) (C.age (N.graph.source A.entry))
    (original_after_member N C _ _ hDH) (hHU.trans hUA) (C.age (N.graph.target A.child))
  have h2 := actual_stop_tail_middle_cut N C H gamma common
    (afterDate N C (C.age A.fragment.parents.hybrid)) (original_after_ordered N C _)
    (C.age A.fragment.upper) (C.age (N.graph.source A.entry))
    (original_after_member N C _ _ hHU) hUA (C.age A.fragment.parents.hybrid)
  have hf1 : ((afterDate N C (C.age (N.graph.target A.child))).filter
      (fun c => decide (C.age A.fragment.parents.hybrid < c))) =
      afterDate N C (C.age A.fragment.parents.hybrid) := filter_after_filter hDH _
  have hf2 : ((afterDate N C (C.age A.fragment.parents.hybrid)).filter
      (fun c => decide (C.age A.fragment.upper < c))) =
      afterDate N C (C.age A.fragment.upper) := filter_after_filter hHU _
  rw [hf1] at h1
  rw [hf2] at h2
  unfold componentAgenda phaseBeforeClosing
  change (nodeOperations N C H gamma common _ ++
    stopBeforeTail N C H gamma common _ _ (afterDate N C _) ++ _) ++ _ = _
  rw [h1,h2]
  have hbatch (a : ℝ) : boundaryOperations N C H gamma common a =
    (originalExits N C a).map (fun e => .boundary (.exit e)) ++ nodeOperations N C H gamma common a := rfl
  rw [hbatch,hbatch]
  simp only [List.map_append,List.map_singleton,List.append_assoc]

end G1CanonicalThreeEpochList
