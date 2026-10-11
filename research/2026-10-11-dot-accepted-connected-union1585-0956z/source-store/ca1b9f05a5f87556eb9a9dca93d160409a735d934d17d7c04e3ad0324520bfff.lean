import G2CalendarPathProjection

/-!
Product-measurable chronological gluing of annotated segment observations.
Contributor: dot (OpenAI), 7 October 2026.

Forgetting stored terminal annotations and applying the original fixed-calendar
reader preserves its strict interval interiors, boundary order and zero-length
steps. Pointwise statements use arbitrary records. Replacing the computed
calendar terminal state by an independently stored state requires an explicit
coherence equality. Probability-law assembly and event-age decoding are separate.
-/
namespace GProgram.G2.ChronologicalGluing
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.ActualSegmentPathLaw GProgram.G2.CalendarPathProjection
open GProgram.G2.CompletedPathProjection GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.ChronologicalPathReadout
open scoped Classical NNReal

abbrev AnnotatedCompletedObservation (Q : Type*) (n : Nat) :=
  (Fin n → SegmentObservation Q) × (ℝ≥0 → Q)

def forgetSegmentTerminals {Q : Type*} (n : Nat)
    (z : Fin n → SegmentObservation Q) : Fin n → ℝ≥0 → Q :=
  fun i => (z i).1

lemma forget_segment_terminals_measurable {Q : Type*} [MeasurableSpace Q] (n : Nat) :
    Measurable (forgetSegmentTerminals (Q := Q) n) :=
  measurable_pi_lambda _ (fun i => (measurable_pi_apply i).fst)

def forgetCompletedTerminals {Q : Type*} (n : Nat)
    (z : AnnotatedCompletedObservation Q n) : CompletedObservation Q n :=
  (forgetSegmentTerminals n z.1,z.2)

lemma forget_completed_terminals_measurable {Q : Type*} [MeasurableSpace Q] (n : Nat) :
    Measurable (forgetCompletedTerminals (Q := Q) n) :=
  ((forget_segment_terminals_measurable n).comp measurable_fst).prodMk measurable_snd

variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [MeasurableSpace Q]

noncomputable def joinedChronologicalPath (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) (z : AnnotatedCompletedObservation Q ops.length) : ℝ≥0 → Q :=
  chronologicalPath N ops (forgetCompletedTerminals ops.length z)

lemma joined_chronological_path_measurable (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) : Measurable (joinedChronologicalPath N (Q := Q) ops) :=
  (chronological_path_measurable N ops).comp (forget_completed_terminals_measurable ops.length)

lemma joined_chronological_nil (N : RootedBinary V E X)
    (z : AnnotatedCompletedObservation Q 0) (t : ℝ≥0) :
    joinedChronologicalPath N [] z t = z.2 t := rfl

/-- The original strict-interior convention is retained. At the endpoint the
reader advances into the suffix, including all intervening boundary steps. -/
lemma joined_chronological_interval (N : RootedBinary V E X)
    (h : ℝ≥0) (ops : List (ProgramStep N))
    (z : AnnotatedCompletedObservation Q (.interval h::ops).length) (t : ℝ≥0) :
    joinedChronologicalPath N (.interval h::ops) z t =
      if t < h then (z.1 0).1 t else
        joinedChronologicalPath N ops (Fin.tail z.1,z.2) (t-h) := rfl

lemma joined_chronological_boundary (N : RootedBinary V E X)
    (b : BoundaryOperation N) (ops : List (ProgramStep N))
    (z : AnnotatedCompletedObservation Q (.boundary b::ops).length) (t : ℝ≥0) :
    joinedChronologicalPath N (.boundary b::ops) z t =
      joinedChronologicalPath N ops (Fin.tail z.1,z.2) t := rfl

/-- Clamping changes no interval interior used by the original chronological
reader. This holds on arbitrary records and for an arbitrary all-time tail;
no relation between a segment's path and stored endpoint is presumed. -/
theorem clamped_chronological_agrees (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample) (p : ℝ≥0 → Q) :
    joinedChronologicalPath N ops (observeCalendarSegments N f ops s past,p) =
      chronologicalPath N ops (observeCalendar N f ops s past,p) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      funext t
      cases op with
      | boundary b =>
          simpa only [joined_chronological_boundary,chronologicalPath,
            observeCalendarSegments,observeCalendar,Fin.tail_cons] using
            congrFun (ih (past 0).2 (Fin.tail past)) t
      | interval h =>
          by_cases ht : t < h
          · simpa only [joined_chronological_interval,chronologicalPath,
              observeCalendarSegments,observeCalendar,Fin.cons_zero,if_pos ht] using
              observed_segment_interior N f h s (past 0) t ht
          · simpa only [joined_chronological_interval,chronologicalPath,
              observeCalendarSegments,observeCalendar,Fin.tail_cons,if_neg ht] using
              congrFun (ih (past 0).2 (Fin.tail past)) (t-h)

/-- The annotated reader joins to exactly the original chronological record
path when its tail starts at the computed calendar endpoint. -/
theorem joined_record_path_agrees (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : Bool × ClockTrace N sample (Fintype.card Copy)) :
    joinedChronologicalPath N ops (observeCalendarSegments N f ops s past,
      GProgram.G2.CompleteEpochPath.completePath N f (calendarEnd N ops s past) tail) =
      fun t => f (recordPath N ops s past tail t) := by
  rw [clamped_chronological_agrees]
  funext t
  exact record_path_is_chronological N f ops s past tail t

/-- The separately stored terminal state can replace the computed endpoint
only under this explicit deterministic coherence hypothesis. It is not
assumed for arbitrary completed records and is not a probability-law premise. -/
theorem coherent_completed_record_agrees (N : RootedBinary V E X) {sample : Copy → X}
    (f : Code N sample → Q) (ops : List (ProgramStep N)) (s : Code N sample)
    (z : CompleteCalendarRecord N sample ops)
    (hterminal : z.1 = calendarEnd N ops s z.2.1) :
    joinedChronologicalPath N ops (observeCalendarSegments N f ops s z.2.1,
      GProgram.G2.CompleteEpochPath.completePath N f z.1 z.2.2) =
      fun t => f (recordPath N ops s z.2.1 z.2.2 t) := by
  rw [hterminal]
  exact joined_record_path_agrees N f ops s z.2.1 z.2.2

#print axioms forget_segment_terminals_measurable
#print axioms forget_completed_terminals_measurable
#print axioms joined_chronological_path_measurable
#print axioms joined_chronological_nil
#print axioms joined_chronological_interval
#print axioms joined_chronological_boundary
#print axioms clamped_chronological_agrees
#print axioms joined_record_path_agrees
#print axioms coherent_completed_record_agrees
end GProgram.G2.ChronologicalGluing
