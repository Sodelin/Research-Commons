import FiniteTagDecoder
import UnifiedLean.G6.BinFold
import G2CompleteDecoration

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED author draft. No compiler has run on this source.
The unchanged actual calendar/complete-record law, source Code, original
real-age fold and SAME record's live genealogy trees are used throughout.
The finite joint calendar/tail kernel formula is a separate hand theorem.
No desired source law, decoder correctness, chronology or successful path
is supplied as a premise. Initial old real decoration is stated explicitly.
-/

namespace CloudG3.CompleteCalendarBinReadout

universe u v w x y

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.ActualDecorationFold GProgram.G2.CalendarDecoration
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open GProgram.G2.SourceGraftDecoration GProgram.G2.FaithfulPairAgeDecoration
open UnifiedLean.G6.BinFold CloudG3.FiniteTagDecoder
open scoped Classical NNReal

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Boundaries carry old tags; intervals fold their own literal marked record. -/
noncomputable def segmentTags (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (op : ProgramStep N) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) (z : SegmentRecord N sample) : Copy → Copy → Tag :=
  match op with
  | .interval _ => foldTags N bin (Fintype.card Copy) s offset B z.1.2
  | .boundary _ => B

/-- Retain the actual record order, stored destination and carried past tags. -/
noncomputable def calendarTags (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) : (ops : List (ProgramStep N)) → Code N sample → ℝ →
      (Copy → Copy → Tag) → (Fin ops.length → SegmentRecord N sample) →
      (Copy → Copy → Tag)
  | [], _, _, B, _ => B
  | op :: ops, s, offset, B, past =>
      calendarTags N bin ops (past 0).2 (segmentOffset N op offset)
        (segmentTags N bin op s offset B (past 0)) (Fin.tail past)

/-- The SAME complete record supplies its conditional tail and full endpoint. -/
noncomputable def completeTags (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (B : Copy → Copy → Tag)
    (z : CompleteCalendarRecord N sample ops) : Copy → Copy → Tag :=
  foldTags N bin (Fintype.card Copy) z.1 (offset + (programDuration N ops : ℝ))
    (calendarTags N bin ops s offset B z.2.1) z.2.2.2

theorem map_segment_matrix (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (op : ProgramStep N) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) (z : SegmentRecord N sample) :
    (fun a b => bin (segmentMatrix N op s offset M z a b)) =
      segmentTags N bin op s offset (fun a b => bin (M a b)) z := by
  cases op with
  | interval h => exact map_actual_age_fold N bin (Fintype.card Copy) s offset M z.1.2
  | boundary b => rfl

theorem map_calendar_matrix (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ)
    (past : Fin ops.length → SegmentRecord N sample) :
    (fun a b => bin (calendarMatrix N ops s offset M past a b)) =
      calendarTags N bin ops s offset (fun a b => bin (M a b)) past := by
  induction ops generalizing s offset M with
  | nil => rfl
  | cons op ops ih =>
      change (fun a b => bin (calendarMatrix N ops (past 0).2
        (segmentOffset N op offset) (segmentMatrix N op s offset M (past 0))
        (Fin.tail past) a b)) = _
      rw [ih, map_segment_matrix]
      rfl

theorem map_complete_matrix (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ)
    (z : CompleteCalendarRecord N sample ops) :
    (fun a b => bin (completeMatrix N ops s offset M z a b)) =
      completeTags N bin ops s offset (fun a b => bin (M a b)) z := by
  unfold completeMatrix completeTags
  rw [map_actual_age_fold, map_calendar_matrix]

/-- The exact complete record's tags decode the ACTUAL live genealogy's
physical decoration, derived under the unchanged actual source measure. -/
theorem actual_complete_tag_decoder (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (bin : ℝ → Tag) (leafAge : Copy → ℝ) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hM : ForestDecorates leafAge M (state s)) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops s,
      ∀ l ∈ (state (completeEnd N ops z)).live,
        ∃ d : Decoration ((state (completeEnd N ops z)).genealogy l),
          (∀ a ∈ ((state (completeEnd N ops z)).genealogy l).leaves,
            ∀ b ∈ ((state (completeEnd N ops z)).genealogy l).leaves,
              completeMatrix N ops s offset M z a b =
                pairAge leafAge ((state (completeEnd N ops z)).genealogy l) d a b) ∧
          decodeTags (completeTags N bin ops s offset (fun a b => bin (M a b)) z)
              ((state (completeEnd N ops z)).genealogy l) =
            mapBinDecoration bin ((state (completeEnd N ops z)).genealogy l) d := by
  filter_upwards [actual_complete_matrix_decorates N r leafAge ops s offset M hM] with z hz
  intro l hl
  obtain ⟨d, hd⟩ := hz l hl
  refine ⟨d, hd, ?_⟩
  rw [← map_complete_matrix N bin ops s offset M z]
  exact decodeTags_bin_of_pair_agreement bin leafAge
    ((state (completeEnd N ops z)).genealogy l)
    ((completeEnd N ops z).property.forest.wellLabelled l hl) d
    (completeMatrix N ops s offset M z) hd

/-- Repeated tags never remove a graft or change any leaf label. -/
theorem complete_tag_decode_underlying (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (B : Copy → Copy → Tag)
    (z : CompleteCalendarRecord N sample ops) (l : Copy) :
    underlying (decodedTaggedTree (completeTags N bin ops s offset B z)
      ((state (completeEnd N ops z)).genealogy l)) =
        ((state (completeEnd N ops z)).genealogy l) := by
  unfold decodedTaggedTree
  exact underlying_toTaggedTree _ _

variable [MeasurableSpace Tag]

/-- The actual past matrix, rather than independent marginal tags, is binned. -/
theorem calendar_binned_matrix_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) :
    Measurable (fun past : Fin ops.length → SegmentRecord N sample =>
      fun a b => bin (calendarMatrix N ops s offset M past a b)) := by
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro b
  exact hbin.comp ((measurable_pi_apply b).comp
    ((measurable_pi_apply a).comp (calendar_matrix_measurable N ops s offset M)))

theorem calendar_joint_bin_readout_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) :
    Measurable (fun past : Fin ops.length → SegmentRecord N sample =>
      (calendarEnd N ops s past, calendarTags N bin ops s offset
        (fun a b => bin (M a b)) past)) := by
  have he : (fun past : Fin ops.length → SegmentRecord N sample =>
      calendarTags N bin ops s offset (fun a b => bin (M a b)) past) =
      (fun past => fun a b => bin (calendarMatrix N ops s offset M past a b)) := by
    funext past
    exact (map_calendar_matrix N bin ops s offset M past).symm
  rw [he]
  exact (calendar_end_measurable N ops s).prodMk
    (calendar_binned_matrix_measurable N bin hbin ops s offset M)

/-- Actual source pushforward. This is explicitly a Measure, before finite
singleton normalization is used to construct a PMF in the hand theorem. -/
noncomputable def calendarJointLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (bin : ℝ → Tag) (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) :
    Measure (Code N sample × (Copy → Copy → Tag)) :=
  (actualCalendarTraceLaw N r ops s).map (fun past =>
    (calendarEnd N ops s past,
      calendarTags N bin ops s offset (fun a b => bin (M a b)) past))

theorem calendar_joint_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    IsProbabilityMeasure (calendarJointLaw N r bin ops s offset M) := by
  letI := actual_calendar_trace_probability N r ops s
  exact Measure.isProbabilityMeasure_map
    (calendar_joint_bin_readout_measurable N bin hbin ops s offset M).aemeasurable

/-- Genuine finite-coordinate binning of the original real matrix is measurable. -/
theorem complete_binned_matrix_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) :
    Measurable (fun z : CompleteCalendarRecord N sample ops =>
      fun a b => bin (completeMatrix N ops s offset M z a b)) := by
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro b
  exact hbin.comp ((measurable_pi_apply b).comp
    ((measurable_pi_apply a).comp (complete_matrix_measurable N ops s offset M)))

/-- The finite joint carrier retains endpoint Code jointly with old/new tags. -/
theorem complete_joint_bin_readout_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) :
    Measurable (fun z : CompleteCalendarRecord N sample ops =>
      (completeEnd N ops z, completeTags N bin ops s offset
        (fun a b => bin (M a b)) z)) := by
  have he : (fun z : CompleteCalendarRecord N sample ops =>
      completeTags N bin ops s offset (fun a b => bin (M a b)) z) =
      (fun z => fun a b => bin (completeMatrix N ops s offset M z a b)) := by
    funext z
    exact (map_complete_matrix N bin ops s offset M z).symm
  rw [he]
  exact (complete_end_measurable N ops).prodMk
    (complete_binned_matrix_measurable N bin hbin ops s offset M)

#print axioms map_segment_matrix
#print axioms map_calendar_matrix
#print axioms map_complete_matrix
#print axioms actual_complete_tag_decoder
#print axioms complete_tag_decode_underlying
#print axioms calendar_binned_matrix_measurable
#print axioms calendar_joint_bin_readout_measurable
#print axioms calendar_joint_probability
#print axioms complete_binned_matrix_measurable
#print axioms complete_joint_bin_readout_measurable

end CloudG3.CompleteCalendarBinReadout
