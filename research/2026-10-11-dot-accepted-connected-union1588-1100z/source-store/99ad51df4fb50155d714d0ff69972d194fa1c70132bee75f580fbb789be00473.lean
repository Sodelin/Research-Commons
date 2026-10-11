import G2CompleteCalendarAttachment
import G2CompleteAncestralPath

/-!
Literal chronological joining of the actual calendar and ancestral records.
Contributor: dot (OpenAI), 6 October 2026. This deterministic measurable
reader retains boundary order and skips zero-duration intervals. Distribution
transport between carriers is a separate subsequent theorem.
-/
namespace GProgram.G2.CompleteEpochPath
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.EpochHistoryReadout
open scoped Classical NNReal
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

noncomputable def completePath (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (s : Code N sample)
    (z : Bool × ClockTrace N sample (Fintype.card Copy)) : ℝ≥0 → Q :=
  fun t => f (cutEndpoint N (Fintype.card Copy) (t : ℝ) s z.2)

lemma complete_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (s : Code N sample) : Measurable (completePath N f s) := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_of_countable f).comp
    ((cut_endpoint_joint_measurable N _ (t : ℝ)).comp
      (measurable_const.prodMk measurable_snd))
end GProgram.G2.CompleteEpochPath

namespace GProgram.G2.CalendarPathProjection
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteEpochPath
open scoped Classical NNReal
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

noncomputable def segmentPath (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (op : ProgramStep N) (s : Code N sample)
    (z : SegmentRecord N sample) : ℝ≥0 → Q :=
  match op with
  | .interval _ => completePath N f s z.1
  | .boundary _ => fun _ => f z.2

lemma segment_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (op : ProgramStep N) (s : Code N sample) :
    Measurable (segmentPath N f op s) := by
  cases op with
  | interval h => exact (complete_path_measurable N f s).comp measurable_fst
  | boundary b =>
      apply measurable_pi_lambda
      intro t
      exact (measurable_of_countable f).comp measurable_snd

noncomputable def observeCalendar (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) : (ops : List (ProgramStep N)) → Code N sample →
      (Fin ops.length → SegmentRecord N sample) → (Fin ops.length → ℝ≥0 → Q)
  | [],_,_ => fun i => Fin.elim0 i
  | op::ops,s,z => Fin.cons (segmentPath N f op s (z 0))
      (observeCalendar N f ops (z 0).2 (Fin.tail z))

lemma observe_calendar_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (observeCalendar N f ops s) := by
  induction ops generalizing s with
  | nil =>
      apply measurable_pi_lambda
      intro i
      exact Fin.elim0 i
  | cons op ops ih =>
      have hm : Measurable (fun z : Code N sample × (Fin ops.length → SegmentRecord N sample) =>
          observeCalendar N f ops z.1 z.2) := measurable_from_prod_countable_right ih
      have ht : Measurable (Fin.tail : (Fin (op::ops).length → SegmentRecord N sample) →
          (Fin ops.length → SegmentRecord N sample)) :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply i.succ)
      apply measurable_pi_lambda
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (segment_path_measurable N f op s).comp (measurable_pi_apply 0)
      · exact (measurable_pi_apply j).comp
          (hm.comp (((measurable_pi_apply 0).snd).prodMk ht))
end GProgram.G2.CalendarPathProjection

namespace GProgram.G2.CompletedPathProjection
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteEpochPath
open GProgram.G2.CalendarPathProjection
open scoped Classical NNReal
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

abbrev CompletedObservation (Q : Type*) (n : Nat) :=
  (Fin n → ℝ≥0 → Q) × (ℝ≥0 → Q)

noncomputable def observeCompleted (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample)
    (z : CompleteCalendarRecord N sample ops) : CompletedObservation Q ops.length :=
  (observeCalendar N f ops s z.2.1,completePath N f z.1 z.2.2)

lemma observe_completed_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (observeCompleted N f ops s) := by
  have hm : Measurable (fun z : Code N sample ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => completePath N f z.1 z.2) :=
    measurable_from_prod_countable_right (fun d => complete_path_measurable N f d)
  exact ((observe_calendar_measurable N f ops s).comp measurable_snd.fst).prodMk
    (hm.comp (measurable_fst.prodMk measurable_snd.snd))
end GProgram.G2.CompletedPathProjection

namespace GProgram.G2.ChronologicalPathReadout
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteEpochPath GProgram.G2.CalendarPathProjection
open GProgram.G2.CompletedPathProjection GProgram.G2.EpochHistoryReadout
open scoped Classical NNReal
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [MeasurableSpace Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

noncomputable def programDuration (N : RootedBinary V E X) : List (ProgramStep N) → ℝ≥0
  | [] => 0
  | .interval h::ops => h+programDuration N ops
  | .boundary _::ops => programDuration N ops

noncomputable def chronologicalPath (N : RootedBinary V E X) :
    (ops : List (ProgramStep N)) → CompletedObservation Q ops.length → ℝ≥0 → Q
  | [],z => z.2
  | .interval h::ops,z => fun t =>
      if t < h then z.1 0 t else chronologicalPath N ops (Fin.tail z.1,z.2) (t-h)
  | .boundary _::ops,z => chronologicalPath N ops (Fin.tail z.1,z.2)

lemma chronological_path_measurable (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) : Measurable (chronologicalPath N (Q := Q) ops) := by
  induction ops with
  | nil => exact measurable_snd
  | cons op ops ih =>
      have ht : Measurable (fun z : CompletedObservation Q (ops.length+1) =>
          (Fin.tail z.1,z.2)) :=
        (measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp measurable_fst)).prodMk
          measurable_snd
      cases op with
      | boundary b => exact ih.comp ht
      | interval h =>
          apply measurable_pi_lambda
          intro t
          by_cases hth : t < h
          · simpa only [List.length_cons,chronologicalPath,if_pos hth,Function.comp_def] using
              ((measurable_pi_apply t).comp ((measurable_pi_apply 0).comp
                (measurable_fst : Measurable (Prod.fst : CompletedObservation Q (ops.length+1) → _))))
          · simpa only [List.length_cons,chronologicalPath,if_neg hth,Function.comp_def] using
              ((measurable_pi_apply (t-h)).comp (ih.comp ht))

noncomputable def recordPath (N : RootedBinary V E X) {sample : Copy → X} :
    (ops : List (ProgramStep N)) → Code N sample →
      (Fin ops.length → SegmentRecord N sample) →
      (Bool × ClockTrace N sample (Fintype.card Copy)) → ℝ≥0 → Code N sample
  | [],s,_,tail => fun t => cutEndpoint N (Fintype.card Copy) (t : ℝ) s tail.2
  | .interval h::ops,s,past,tail => fun t =>
      if t < h then cutEndpoint N (Fintype.card Copy) (t : ℝ) s (past 0).1.2
      else recordPath N ops (past 0).2 (Fin.tail past) tail (t-h)
  | .boundary _::ops,_,past,tail => recordPath N ops (past 0).2 (Fin.tail past) tail

theorem record_path_is_chronological (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : Bool × ClockTrace N sample (Fintype.card Copy)) (t : ℝ≥0) :
    chronologicalPath N ops (observeCalendar N f ops s past,
      completePath N f (calendarEnd N ops s past) tail) t =
      f (recordPath N ops s past tail t) := by
  induction ops generalizing s t with
  | nil => rfl
  | cons op ops ih =>
      cases op with
      | boundary b => exact ih (past 0).2 (Fin.tail past) t
      | interval h =>
          by_cases hth : t < h
          · simp only [chronologicalPath,observeCalendar,Fin.cons_zero,if_pos hth,
              segmentPath,completePath,recordPath]
          · simpa only [chronologicalPath,observeCalendar,Fin.tail_cons,if_neg hth,
              calendarEnd,recordPath] using ih (past 0).2 (Fin.tail past) (t-h)

lemma record_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => recordPath N ops s z.1 z.2) := by
  have hp : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => observeCalendar N id ops s z.1) :=
    (observe_calendar_measurable N (id : Code N sample → Code N sample) ops s).comp measurable_fst
  have hm : Measurable (fun z : Code N sample ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => completePath N id z.1 z.2) :=
    measurable_from_prod_countable_right (fun d => complete_path_measurable N id d)
  have ht : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) =>
      completePath N id (calendarEnd N ops s z.1) z.2) :=
    hm.comp (((calendar_end_measurable N ops s).comp measurable_fst).prodMk measurable_snd)
  convert (chronological_path_measurable N ops).comp (hp.prodMk ht) using 1
  funext z t
  exact (record_path_is_chronological N id ops s z.1 z.2 t).symm

#print axioms GProgram.G2.CompleteEpochPath.complete_path_measurable
#print axioms GProgram.G2.CalendarPathProjection.segment_path_measurable
#print axioms GProgram.G2.CalendarPathProjection.observe_calendar_measurable
#print axioms GProgram.G2.CompletedPathProjection.observe_completed_measurable
#print axioms chronological_path_measurable
#print axioms record_path_is_chronological
#print axioms record_path_measurable
end GProgram.G2.ChronologicalPathReadout
