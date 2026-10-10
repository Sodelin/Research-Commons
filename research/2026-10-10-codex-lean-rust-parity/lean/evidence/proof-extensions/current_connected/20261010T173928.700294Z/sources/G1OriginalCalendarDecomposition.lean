import G1InitializedJointComponentReplacement

/-! Exact ORIGINAL full-calendar frontier/phase/future list decomposition.
Contributor: dot, 2026-10-03. Pure list/date algebra binds the derived canonical
interleaved phase to its actual unchanged complete compiler program. No source
law, desired output or kernel identity is a field or premise. -/
namespace G1OriginalCalendarDecomposition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming UnifiedLean.Source.SourceProgramTransport
open G1ActualTwoPortBlob G1InitializedFrontierPrefix G1CanonicalComponentSegment
open scoped Classical NNReal
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

lemma filter_after_head {a : ℝ} {as : List ℝ} (ha : ∀ c ∈ as, a < c) :
    (a :: as).filter (fun c => decide (a < c)) = as := by
  have hself : as.filter (fun c => decide (a < c)) = as := List.filter_eq_self.mpr (by
    intro c hc; exact decide_eq_true (ha c hc))
  simp [hself]

/-- Exact original temporal tail split BEFORE stop's boundary batch. -/
theorem actual_calendar_tail_cut (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (dates : List ℝ) (horder : dates.Pairwise (· < ·)) (stop : ℝ) (hstop : stop ∈ dates) (a : ℝ) :
    calendarTail N C H gamma common a dates = stopBeforeTail N C H gamma common stop a dates ++
      boundaryOperations N C H gamma common stop ++
      calendarTail N C H gamma common stop (dates.filter (fun c => decide (stop < c))) := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hstop)
  | cons c cs ih =>
      have hp := List.pairwise_cons.mp horder
      by_cases hc : c = stop
      · subst c
        rw [filter_after_head hp.1]
        simp [calendarTail,stopBeforeTail,List.append_assoc]
      · have hm : stop ∈ cs := (List.mem_cons.mp hstop).resolve_left (Ne.symm hc)
        have hlt := hp.1 _ hm
        have hnot : ¬ stop < c := not_lt_of_gt hlt
        have hfilter : (c::cs).filter (fun d => decide (stop < d)) = cs.filter (fun d => decide (stop < d)) := by simp [hnot]
        rw [hfilter]
        simp only [calendarTail,stopBeforeTail,if_neg hc,List.cons_append]
        rw [ih hp.2 hm c]
        simp only [List.append_assoc]

/-- The generated initialized BEFORE-node prefix is literally the initial
segment of the unchanged full compiler, ending before stop's full boundary. -/
theorem actual_compiled_calendar_date_cut (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (stop : ℝ) (hstop : stop ∈ sortedOriginalDates N C) :
    compiledCalendarProgram N C H gamma common = beforeBoundaryProgram N C H gamma common stop ++
      boundaryOperations N C H gamma common stop ++ calendarTail N C H gamma common stop
        ((sortedOriginalDates N C).filter (fun c => decide (stop < c))) := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro heq; rw [heq] at hstop; exact List.not_mem_nil hstop
  obtain ⟨a,as,heq⟩ := List.exists_cons_of_ne_nil hne
  have horder := original_dates_strict N C
  rw [heq] at horder hstop
  have hp := List.pairwise_cons.mp horder
  by_cases ha : a = stop
  · subst a
    simp [compiledCalendarProgram,beforeBoundaryProgram,heq,filter_after_head hp.1]
  · have hm : stop ∈ as := (List.mem_cons.mp hstop).resolve_left (Ne.symm ha)
    have hlt := hp.1 _ hm
    have hnot : ¬ stop < a := not_lt_of_gt hlt
    simp only [compiledCalendarProgram,beforeBoundaryProgram,heq,if_neg ha]
    have hc := actual_calendar_tail_cut N C H gamma common as hp.2 stop hm a
    rw [hc]
    simp [hnot,List.append_assoc]

lemma original_exit_list_cut {A : Type*} [DecidableEq A] (es : List A) (e : A) (he : e ∈ es) :
    es = es.takeWhile (fun f => decide (f ≠ e)) ++ [e] ++
      (es.dropWhile (fun f => decide (f ≠ e))).tail := by
  induction es with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons a as ih =>
      by_cases ha : a = e
      · subst a; simp
      · have hm : e ∈ as := (List.mem_cons.mp he).resolve_left (Ne.symm ha)
        simpa [ha,List.append_assoc] using congrArg (List.cons a) (ih hm)

noncomputable def originalExits (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) : List E :=
  (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList

noncomputable def originalFuture (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) : List (ProgramStep N) :=
  ((originalExits N C (C.age (N.graph.source A.entry))).dropWhile (fun e => decide (e ≠ A.entry))).tail.map
    (fun e => .boundary (.exit e)) ++
      nodeOperations N C H gamma common (C.age (N.graph.source A.entry)) ++
      calendarTail N C H gamma common (C.age (N.graph.source A.entry))
        ((sortedOriginalDates N C).filter (fun a => decide (C.age (N.graph.source A.entry) < a)))

lemma filter_after_filter {a b : ℝ} (hab : a < b) (dates : List ℝ) :
    (dates.filter (fun c => decide (a < c))).filter (fun c => decide (b < c)) =
      dates.filter (fun c => decide (b < c)) := by
  rw [List.filter_filter]
  congr 1
  funext c
  by_cases hc : b < c
  · simp [hc,hab.trans hc]
  · simp [hc]

/-- The actual complete original compiler is EXACTLY the initialized current
frontier prefix, the canonical component phase, and the SAME original future.
The phase closes at its entry exit; leftover same-date exits are in future. -/
theorem actual_full_calendar_component_decomposition (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    compiledCalendarProgram N C H gamma common =
      actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)) ++
        componentAgenda N C b A H gamma common ++ originalFuture N C b A H gamma common := by
  let start := C.age (N.graph.target A.child)
  let stop := C.age (N.graph.source A.entry)
  let dates := (sortedOriginalDates N C).filter (fun a => decide (start < a))
  have hlt : start < stop := actual_component_dates_strict N C b A
  have horder : dates.Pairwise (· < ·) := (original_dates_strict N C).filter _
  have hstop : stop ∈ dates := by
    simp only [dates,List.mem_filter,decide_eq_true_eq]
    exact ⟨original_date_scheduled N C _,hlt⟩
  have hstart := actual_compiled_calendar_date_cut N C H gamma common start (original_date_scheduled N C _)
  have hmiddle := actual_calendar_tail_cut N C H gamma common dates horder stop hstop start
  have hexit : A.entry ∈ originalExits N C stop := Finset.mem_toList.mpr
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)
  have hexits := original_exit_list_cut (originalExits N C stop) A.entry hexit
  rw [hstart,hmiddle]
  have hfilters := filter_after_filter hlt (sortedOriginalDates N C)
  change (dates.filter (fun c => decide (stop < c))) =
    (sortedOriginalDates N C).filter (fun c => decide (stop < c)) at hfilters
  rw [hfilters]
  unfold actualFrontierProgram componentAgenda phaseBeforeClosing originalFuture exitsBeforeEntry
  have hbatch (a : ℝ) : boundaryOperations N C H gamma common a =
      (originalExits N C a).map (fun e => .boundary (.exit e)) ++ nodeOperations N C H gamma common a := rfl
  have hmaps := congrArg (fun es : List E => es.map (fun e : E => (ProgramStep.boundary (.exit e) : ProgramStep N))) hexits
  rw [List.map_append,List.map_append,List.map_singleton] at hmaps
  rw [hbatch,hbatch]
  conv_lhs => rw [hmaps]
  simp only [originalExits,List.map_singleton,List.append_assoc,start,stop,dates]

end G1OriginalCalendarDecomposition
