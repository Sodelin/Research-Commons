import UnifiedLean.G6.BinClock
import G2ActualCalendarTrace
import LiteralSameBinTrace
import CompleteCalendarBinReadout
import FiniteTagDecoder

/-!
Contributor: Cloud Sol /root/source_backend_review_sol, 2026-10-08.
UNCHECKED source draft. No compiler, runtime, or new source-law verification.
The carried kernel is defined ONLY by mapping/binding the unchanged actual
original source kernels. No desired row equality is an input field.
The Python/wire quotient iteration and chronological law are separate HAND
arguments in the adjacent note, pending independent and formal review.
-/
namespace CloudG6.TaggedSourceIteration

open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.BinHistory UnifiedLean.G6.BinFold
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open CloudG3.FiniteTagDecoder CloudG3.LiteralSameBinTrace
open CloudG3.CompleteCalendarBinReadout
open scoped Classical NNReal
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev TaggedCode (N : RootedBinary V E X) (sample : Copy → X) (Tag : Type*) :=
  Code N sample × (Copy → Copy → Tag)

/-- Same original Code row; tags use the existing actual ancestry update. -/
noncomputable def taggedStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (z : TaggedCode N sample Tag) :
    PMF (TaggedCode N sample Tag) :=
  (sourceStep N r z.1).map (fun d => (d,tagUpdate N z.1 d tag z.2))

noncomputable def taggedIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) :
    Nat → TaggedCode N sample Tag → PMF (TaggedCode N sample Tag)
  | 0,z => PMF.pure z
  | k+1,z => (taggedStep N r tag z).bind (taggedIteration N r tag k)

/-- Constructed fixed-tag Poisson mixture. The elapsed-clock interpretation
requires the actual marked-record/constant-bin argument in the HAND note. -/
noncomputable def taggedTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (t : ℝ≥0)
    (z : TaggedCode N sample Tag) : PMF (TaggedCode N sample Tag) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind
    (fun k => taggedIteration N r tag k z)

theorem tagged_step_code (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (z : TaggedCode N sample Tag) :
    (taggedStep N r tag z).map Prod.fst = sourceStep N r z.1 := by
  rw [taggedStep,PMF.map_comp]
  change (sourceStep N r z.1).map id = sourceStep N r z.1
  exact PMF.map_id _

theorem tagged_iteration_code (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (k : Nat) (z : TaggedCode N sample Tag) :
    (taggedIteration N r tag k z).map Prod.fst = sourceIteration N r k z.1 := by
  induction k generalizing z with
  | zero => simp only [taggedIteration,sourceIteration,PMF.pure_map]
  | succ k ih =>
      rw [taggedIteration,PMF.map_bind]
      simp_rw [ih]
      change (taggedStep N r tag z).bind (sourceIteration N r k ∘ Prod.fst) = _
      rw [← PMF.bind_map,tagged_step_code]
      rfl

theorem tagged_time_code (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (t : ℝ≥0)
    (z : TaggedCode N sample Tag) :
    (taggedTimeKernel N r tag t z).map Prod.fst = sourceTimeKernel N r t z.1 := by
  rw [taggedTimeKernel,PMF.map_bind]
  simp_rw [tagged_iteration_code]
  rfl

/-- A finite actual holding-or-merger word, with the current Choice type at
each destination. These are uniformization choices, not physical ages. -/
noncomputable def ChoiceWord (N : RootedBinary V E X) {sample : Copy → X} :
    Nat → Code N sample → Type _
  | 0,_ => PUnit
  | k+1,s => Σ p : Option (Choice N s), ChoiceWord N k (stepDestination N s p)

noncomputable def wordEnd (N : RootedBinary V E X) {sample : Copy → X} :
    (k : Nat) → (s : Code N sample) → ChoiceWord N k s → Code N sample
  | 0,s,_ => s
  | k+1,s,w => wordEnd N k (stepDestination N s w.1) w.2

noncomputable def wordTags (N : RootedBinary V E X) {sample : Copy → X} (tag : Tag) :
    (k : Nat) → (s : Code N sample) → (Copy → Copy → Tag) →
      ChoiceWord N k s → (Copy → Copy → Tag)
  | 0,_,M,_ => M
  | k+1,s,M,w => wordTags N tag k (stepDestination N s w.1)
      (tagUpdate N s (stepDestination N s w.1) tag M) w.2

theorem actual_choice_relation_monotone (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Option (Choice N s)) :
    RelationMonotone N s (stepDestination N s p) := by
  cases p with
  | none => intro x y h; exact h
  | some p => exact actual_destination_relation_monotone N s p

theorem word_relation_monotone (N : RootedBinary V E X) {sample : Copy → X}
    (k : Nat) (s : Code N sample) (w : ChoiceWord N k s) :
    RelationMonotone N s (wordEnd N k s w) := by
  induction k generalizing s with
  | zero => intro x y h; exact h
  | succ k ih =>
      rcases w with ⟨p,w⟩
      intro x y h
      exact ih (stepDestination N s p) w x y
        (actual_choice_relation_monotone N s p x y h)

/-- Complete same-tag words retain old tags and have an endpoint-only update.
No monotonicity or desired endpoint relation is supplied as a premise. -/
theorem word_tags_endpoint (N : RootedBinary V E X) {sample : Copy → X}
    (tag : Tag) (k : Nat) (s : Code N sample) (M : Copy → Copy → Tag)
    (w : ChoiceWord N k s) :
    wordTags N tag k s M w = tagUpdate N s (wordEnd N k s w) tag M := by
  induction k generalizing s M with
  | zero => exact (tag_update_self N s tag M).symm
  | succ k ih =>
      rcases w with ⟨p,w⟩
      change wordTags N tag k (stepDestination N s p)
          (tagUpdate N s (stepDestination N s p) tag M) w = _
      rw [ih]
      exact same_bin_update_comp N s (stepDestination N s p)
        (wordEnd N k (stepDestination N s p) w) tag M
        (actual_choice_relation_monotone N s p)
        (word_relation_monotone N k (stepDestination N s p) w)

/-- Exactly recursive child swaps with tags and original Copy leaves retained. -/
def taggedTreeSetoid (Copy Tag : Type*) : Setoid (TaggedTree Copy Tag) where
  r := TaggedEquiv
  iseqv := ⟨TaggedEquiv.refl,TaggedEquiv.symm,TaggedEquiv.trans⟩

theorem tagged_graft_swap (tag : Tag) (a b : TaggedTree Copy Tag) :
    Quotient.mk (taggedTreeSetoid Copy Tag) (.graft tag a b) =
      Quotient.mk (taggedTreeSetoid Copy Tag) (.graft tag b a) :=
  Quotient.sound (TaggedEquiv.swap tag a b)

/-- Every original Location is retained, including node/outside forests.
Current representative IDs and child order are forgotten; original leaf IDs
and the SAME total original V register are retained. -/
noncomputable def forestReadout (N : RootedBinary V E X) {sample : Copy → X}
    (z : TaggedCode N sample Tag) :
    (Location V E → Finset (Quotient (taggedTreeSetoid Copy Tag))) × (V → Bool) :=
  ((fun loc => ((state z.1).live.filter (fun l => (state z.1).location l = loc)).image
    (fun l => Quotient.mk (taggedTreeSetoid Copy Tag)
      (decodedTaggedTree z.2 ((state z.1).genealogy l)))),(state z.1).register)

noncomputable def quotientIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (k : Nat) (z : TaggedCode N sample Tag) :=
  (taggedIteration N r tag k z).map (forestReadout N)

/-- Boundary operations keep the matrix; their actual current-owner/register
routing is left to the unchanged original boundary kernel. -/
noncomputable def taggedProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N × Tag)
    (z : TaggedCode N sample Tag) : PMF (TaggedCode N sample Tag) :=
  match op.1 with
  | .interval t => taggedTimeKernel N r op.2 t z
  | .boundary b => (boundaryKernel N b z.1).map (fun d => (d,z.2))

noncomputable def taggedProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) :
    List (ProgramStep N × Tag) → TaggedCode N sample Tag → PMF (TaggedCode N sample Tag)
  | [],z => PMF.pure z
  | op::ops,z => (taggedProgramStep N r op z).bind (taggedProgram N r ops)

theorem tagged_program_step_code (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N × Tag) (z : TaggedCode N sample Tag) :
    (taggedProgramStep N r op z).map Prod.fst = sourceProgramStep N r op.1 z.1 := by
  rcases op with ⟨op,tag⟩
  cases op with
  | interval t => exact tagged_time_code N r tag t z
  | boundary b =>
      rw [taggedProgramStep,PMF.map_comp]
      change (boundaryKernel N b z.1).map id = boundaryKernel N b z.1
      exact PMF.map_id _

theorem tagged_program_code (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N × Tag))
    (z : TaggedCode N sample Tag) :
    (taggedProgram N r ops z).map Prod.fst = sourceProgram N r (ops.map Prod.fst) z.1 := by
  induction ops generalizing z with
  | nil => simp only [taggedProgram,List.map_nil,sourceProgram,PMF.pure_map]
  | cons op ops ih =>
      rw [taggedProgram,PMF.map_bind]
      simp_rw [ih]
      change (taggedProgramStep N r op z).bind
        (sourceProgram N r (ops.map Prod.fst) ∘ Prod.fst) = _
      rw [← PMF.bind_map,tagged_program_step_code]
      rfl

/-- Only a deterministic date/bin check, never a desired law field. Zero
duration has an empty interior. The original operation order is unchanged. -/
def BinPlan (N : RootedBinary V E X) (bin : ℝ → Tag) :
    List (ProgramStep N × Tag) → ℝ → Prop
  | [],_ => True
  | (.interval t,tag)::ops,offset =>
      (∀ age, offset < age → age < offset+(t : ℝ) → bin age = tag) ∧
        BinPlan N bin ops (offset+(t : ℝ))
  | (.boundary _,_)::ops,offset => BinPlan N bin ops offset

/-- Read the unchanged physical marked program through its existing joint
old/new bin matrix. This is a code marginal of that actual joint measure;
it does not assume a desired marked law and does not identify Python. -/
theorem actual_calendar_joint_code [MeasurableSpace Tag]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N))
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    (calendarJointLaw N r bin ops s offset M).map Prod.fst =
      (sourceProgram N r ops s).toMeasure := by
  rw [calendarJointLaw,Measure.map_map measurable_fst
    (calendar_joint_bin_readout_measurable N bin hbin ops s offset M)]
  change (actualCalendarTraceLaw N r ops s).map (calendarEnd N ops s) = _
  exact actual_calendar_endpoint_law N r ops s

end CloudG6.TaggedSourceIteration
