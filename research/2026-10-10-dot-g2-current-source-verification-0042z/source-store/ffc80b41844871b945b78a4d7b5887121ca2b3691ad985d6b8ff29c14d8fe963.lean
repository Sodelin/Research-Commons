import G2CalendarDecoration

/-!
Complete original source graft-decoration fold with its actual ancestral tail.
Contributor: dot (OpenAI), 6 October 2026.
The same marked records supply the finite calendar and tail. No timed matrix
is fitted to a separately sampled topology.
-/
namespace GProgram.G2.CompleteDecoration
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.SourceGraftDecoration
open GProgram.G2.ActualDecorationFold GProgram.G2.DecorationMeasurability
open GProgram.G2.CalendarDecoration GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.FiniteAncestralTrace
open GProgram.G2.ChronologicalPathReadout
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.LiteralMarkedClockTrace.choiceOptionMeasurable

lemma trace_end_joint_measurable (N : RootedBinary V E X) {sample : Copy → X} (n : Nat) :
    Measurable (fun z : Code N sample × ClockTrace N sample n => traceEndpoint N n z.1 z.2) := by
  cases n with
  | zero => exact measurable_fst
  | succ n => exact ((measurable_pi_apply (Fin.last n)).comp measurable_snd).snd.snd

theorem actual_tail_matrix_decorates (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (offset : ℝ) (leafAge : Copy → ℝ)
    (M : Copy → Copy → ℝ) (hM : ForestDecorates leafAge M (state s)) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s,
      ForestDecorates leafAge (foldMatrix N (Fintype.card Copy) s offset M z.2)
        (state (traceEndpoint N (Fintype.card Copy) s z.2)) := by
  have hf : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      foldMatrix N (Fintype.card Copy) s offset M z.2) :=
    (fold_matrix_joint_measurable N _).comp (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_snd)))
  have he : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      traceEndpoint N (Fintype.card Copy) s z.2) :=
    (trace_end_joint_measurable N _).comp (measurable_const.prodMk measurable_snd)
  have hm := ((forest_decorates_joint_measurable N leafAge).comp (he.prodMk hf)).setOf
  rw [completeAncestralTraceLaw]
  apply (ae_map_iff (complete_ancestral_trace_measurable N s).aemeasurable hm).mpr
  exact Filter.Eventually.of_forall (fun c => actual_literal_fold_decorates N _ s (clockCover N s c : ℝ) offset c leafAge M hM)

noncomputable def completeMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (z : CompleteCalendarRecord N sample ops) : Copy → Copy → ℝ :=
  foldMatrix N (Fintype.card Copy) z.1 (offset+(programDuration N ops : ℝ))
    (calendarMatrix N ops s offset M z.2.1) z.2.2.2

noncomputable def completeEnd (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (z : CompleteCalendarRecord N sample ops) : Code N sample :=
  traceEndpoint N (Fintype.card Copy) z.1 z.2.2.2

lemma complete_end_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) : Measurable (completeEnd N (sample := sample) ops) :=
  (trace_end_joint_measurable N _).comp (measurable_fst.prodMk measurable_snd.snd.snd)

lemma complete_matrix_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    Measurable (completeMatrix N ops s offset M) := by
  have hm : Measurable (fun z : CompleteCalendarRecord N sample ops => calendarMatrix N ops s offset M z.2.1) :=
    (calendar_matrix_measurable N ops s offset M).comp measurable_snd.fst
  have ha : Measurable (fun z : CompleteCalendarRecord N sample ops =>
      (z.1,(offset+(programDuration N ops : ℝ),(calendarMatrix N ops s offset M z.2.1,z.2.2.2)))) :=
    measurable_fst.prodMk (measurable_const.prodMk (hm.prodMk measurable_snd.snd.snd))
  exact (fold_matrix_joint_measurable N _).comp ha

lemma complete_decoration_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) :
    MeasurableSet {z | ForestDecorates leafAge (completeMatrix N ops s offset M z) (state (completeEnd N ops z))} :=
  ((forest_decorates_joint_measurable N leafAge).comp
    ((complete_end_measurable N ops).prodMk (complete_matrix_measurable N ops s offset M))).setOf

/-- Complete output matrix genuinely decorates the SAME source terminal
forest, with every calendar and tail graft retained. -/
theorem actual_complete_matrix_decorates (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (leafAge : Copy → ℝ) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hM : ForestDecorates leafAge M (state s)) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      ForestDecorates leafAge (completeMatrix N ops s offset M z) (state (completeEnd N ops z)) := by
  rw [completeCalendarTraceLaw,ae_finsetSum_measure_iff]
  intro d _
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hmap : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d,z)) := measurable_const.prodMk measurable_id
  have hm := complete_decoration_measurable N leafAge ops s offset M
  apply (ae_map_iff hmap.aemeasurable hm).mpr
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage hmap)).mpr
  filter_upwards [ae_restrict_of_ae (actual_calendar_matrix_decorates N r leafAge ops s offset M hM),
    ae_restrict_mem (measurableSet_eq_fun (calendar_end_measurable N ops s) measurable_const)] with past hp he
  have hd : ForestDecorates leafAge (calendarMatrix N ops s offset M past) (state d) := by
    simpa only [show calendarEnd N ops s past = d from he] using hp
  exact actual_tail_matrix_decorates N r d (offset+(programDuration N ops : ℝ)) leafAge
    (calendarMatrix N ops s offset M past) hd

#print axioms actual_complete_matrix_decorates
#print axioms complete_matrix_measurable
end GProgram.G2.CompleteDecoration
