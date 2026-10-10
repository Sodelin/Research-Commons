import G2ChronologicalPathReadout

/-!
Literal compatibility between a marked tail record and its trace component.
Contributor: dot (OpenAI), 7 October 2026. The chronological reader ignores
the completion Bool; this is proved by its recursion, not an implicit coercion.
The accepted reader and all historical consumer bodies remain unchanged.
-/
namespace GProgram.G2.ChronologicalTraceCompatibility
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarPathProjection GProgram.G2.ChronologicalPathReadout
open scoped Classical NNReal
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- The entire path is independent of the tail's success flag, on arbitrary
records. Active-event flags inside the marked trace are not discarded. -/
theorem record_path_tail_flag_irrelevant (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) (b b' : Bool) :
    recordPath N ops s past (b,tail) = recordPath N ops s past (b',tail) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      cases op with
      | boundary a => exact ih (past 0).2 (Fin.tail past)
      | interval h =>
          funext t
          by_cases ht : t < h
          · simp only [recordPath,if_pos ht]
          · simpa only [recordPath,if_neg ht] using
              congrFun (ih (past 0).2 (Fin.tail past)) (t-h)

noncomputable def bareRecordPath (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) : ℝ≥0 → Code N sample :=
  recordPath N ops s past (false,tail)

lemma marked_record_path_eq_bare (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : Bool × ClockTrace N sample (Fintype.card Copy)) :
    recordPath N ops s past tail = bareRecordPath N ops s past tail.2 := by
  cases tail with
  | mk b trace => exact record_path_tail_flag_irrelevant N ops s past trace b false

lemma bare_record_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) :
    Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      ClockTrace N sample (Fintype.card Copy) => bareRecordPath N ops s z.1 z.2) :=
  (record_path_measurable N ops s).comp
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

/-- A bare-tail caller reads exactly the same original chronological path.
No probability, regularity or success premise is used. -/
lemma bare_record_path_is_chronological [MeasurableSpace Q]
    (N : RootedBinary V E X) {sample : Copy → X} (f : Code N sample → Q)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) (t : ℝ≥0) :
    chronologicalPath N ops (observeCalendar N f ops s past,
      CompleteEpochPath.completePath N f (calendarEnd N ops s past) (false,tail)) t =
      f (bareRecordPath N ops s past tail t) :=
  record_path_is_chronological N f ops s past (false,tail) t

#print axioms record_path_tail_flag_irrelevant
#print axioms marked_record_path_eq_bare
#print axioms bare_record_path_measurable
#print axioms bare_record_path_is_chronological
end GProgram.G2.ChronologicalTraceCompatibility
