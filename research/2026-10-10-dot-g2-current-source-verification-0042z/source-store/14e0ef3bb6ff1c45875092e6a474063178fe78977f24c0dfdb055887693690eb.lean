import G2CompleteDecoration
import G2ActualChronologicalPathLaw

/-!
Countable-coordinate terminal readout of the actual chronological source path.
Contributor: dot (OpenAI), 7 October 2026.

The reader returns the unique value eventually constant on natural-time
coordinates, or none if there is no such value. It is measurable in the
original product path sigma-algebra. Actual eventual constancy follows from
the original finite calendar duration and the same-clock random-cover bound;
no fixed cutoff, root-ancestry or arbitrary event-age decoding claim is made.
-/
namespace GProgram.G2.EventualPathReadout
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.FiniteAncestralTrace
open GProgram.G2.CompletedPathProjection GProgram.G2.CalendarPathProjection
open GProgram.G2.ChronologicalPathReadout GProgram.G2.EpochHistoryReadout
open scoped Classical NNReal

/-- The finite option-valued coordinate is discrete. The full function space
of nonnegative-time paths retains its ordinary product measurable space. -/
local instance terminalOptionMeasurable (Q : Type*) : MeasurableSpace (Option Q) := ⊤

def NatEventuallyConstant {Q : Type*} (path : ℝ≥0 → Q) (q : Q) : Prop :=
  ∃ K : ℕ, ∀ n : ℕ, K ≤ n → path (n : ℝ≥0) = q

lemma nat_eventually_constant_unique {Q : Type*} (path : ℝ≥0 → Q) {q r : Q}
    (hq : NatEventuallyConstant path q) (hr : NatEventuallyConstant path r) : q = r := by
  obtain ⟨K,hK⟩ := hq
  obtain ⟨L,hL⟩ := hr
  exact (hK (max K L) (le_max_left K L)).symm.trans (hL (max K L) (le_max_right K L))

noncomputable def terminalPath {Q : Type*} (path : ℝ≥0 → Q) : Option Q :=
  if h : ∃ q, NatEventuallyConstant path q then some (Classical.choose h) else none

lemma terminal_path_of_nat_eventually_constant {Q : Type*} (path : ℝ≥0 → Q) (q : Q)
    (hq : NatEventuallyConstant path q) : terminalPath path = some q := by
  have h : ∃ r, NatEventuallyConstant path r := ⟨q,hq⟩
  rw [terminalPath,dif_pos h]
  congr 1
  exact nat_eventually_constant_unique path (Classical.choose_spec h) hq

lemma terminal_path_eq_some_iff {Q : Type*} (path : ℝ≥0 → Q) (q : Q) :
    terminalPath path = some q ↔ NatEventuallyConstant path q := by
  constructor
  · intro he
    by_cases h : ∃ r, NatEventuallyConstant path r
    · rw [terminalPath,dif_pos h] at he
      have hq := Option.some.inj he
      exact hq ▸ Classical.choose_spec h
    · rw [terminalPath,dif_neg h] at he
      cases he
  · exact terminal_path_of_nat_eventually_constant path q

lemma terminal_path_eq_none_iff {Q : Type*} (path : ℝ≥0 → Q) :
    terminalPath path = none ↔ ¬ ∃ q, NatEventuallyConstant path q := by
  by_cases h : ∃ q, NatEventuallyConstant path q <;> simp [terminalPath,h]

lemma nat_eventually_constant_measurable {Q : Type*} [MeasurableSpace Q]
    [MeasurableSingletonClass Q] (q : Q) :
    Measurable (fun path : ℝ≥0 → Q => NatEventuallyConstant path q) := by
  apply Measurable.exists
  intro K
  apply Measurable.forall
  intro n
  have heval : Measurable (fun path : ℝ≥0 → Q => path (n : ℝ≥0)) :=
    measurable_pi_apply (n : ℝ≥0)
  have hq : MeasurableSet {path : ℝ≥0 → Q | path (n : ℝ≥0) = q} :=
    heval (MeasurableSet.singleton q)
  exact Measurable.imp measurable_const hq.mem

/-- Only countably many fixed-time evaluation events are used. Arbitrary
product-space paths need not stabilize, and Q may be empty. -/
lemma terminal_path_measurable {Q : Type*} [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [Fintype Q] :
    Measurable (terminalPath (Q := Q)) := by
  have hE : Measurable (fun path : ℝ≥0 → Q => ∃ q, NatEventuallyConstant path q) := by
    apply Measurable.exists
    intro q
    exact nat_eventually_constant_measurable q
  apply measurable_to_countable'
  intro z
  cases z with
  | none =>
      change MeasurableSet {path : ℝ≥0 → Q | terminalPath path = none}
      simp only [terminal_path_eq_none_iff]
      exact hE.setOf.compl
  | some q =>
      change MeasurableSet {path : ℝ≥0 → Q | terminalPath path = some q}
      simp only [terminal_path_eq_some_iff]
      exact (nat_eventually_constant_measurable q).setOf

/-- A finite real-time horizon implies the countable eventual-value predicate,
using cofinality of natural numbers rather than an uncountable intersection. -/
theorem terminal_path_of_constant_after {Q : Type*} (path : ℝ≥0 → Q) (q : Q)
    (H : ℝ≥0) (hH : ∀ t, H ≤ t → path t = q) : terminalPath path = some q := by
  obtain ⟨K,hK⟩ := exists_nat_ge H
  apply terminal_path_of_nat_eventually_constant
  refine ⟨K,?_⟩
  intro n hn
  apply hH
  exact hK.trans (by exact_mod_cast hn)

variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [MeasurableSpace Q] [MeasurableSingletonClass Q] [Fintype Q]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Every finite original calendar has finished at its total duration. This
identity holds for arbitrary segment observations and the arbitrary tail. -/
lemma chronological_path_add_duration (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) (z : CompletedObservation Q ops.length) (u : ℝ≥0) :
    chronologicalPath N ops z (programDuration N ops + u) = z.2 u := by
  induction ops generalizing u with
  | nil => simp only [programDuration,chronologicalPath,zero_add]
  | cons op ops ih =>
      cases op with
      | boundary b =>
          simpa only [programDuration,chronologicalPath] using ih (Fin.tail z.1,z.2) u
      | interval h =>
          have hn : ¬ h + (programDuration N ops + u) < h :=
            not_lt_of_ge (le_add_of_nonneg_right
              (show (0 : ℝ≥0) ≤ programDuration N ops + u from bot_le))
          simpa only [programDuration,chronologicalPath,add_assoc,if_neg hn,
            add_tsub_cancel_left] using ih (Fin.tail z.1,z.2) u

lemma chronological_path_after_duration (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) (z : CompletedObservation Q ops.length)
    (t : ℝ≥0) (ht : programDuration N ops ≤ t) :
    chronologicalPath N ops z t = z.2 (t-programDuration N ops) := by
  simpa only [add_tsub_cancel_of_le ht] using
    chronological_path_add_duration N ops z (t-programDuration N ops)

/-- The same-source cover controls the complete tail without regularity or
root ancestry; mere stabilization is not a one-root assertion. -/
lemma actual_complete_tail_constant (N : RootedBinary V E X) {sample : Copy → X}
    (d : Code N sample) (c : Choice N d → ℝ) (f : Code N sample → Q)
    (u : ℝ≥0) (hu : clockCover N d c ≤ u) :
    GProgram.G2.CompleteEpochPath.completePath N f d (completeAncestralTrace N d c) u =
      f (traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c).2) := by
  change f (cutEndpoint N (Fintype.card Copy) (u : ℝ) d (completeAncestralTrace N d c).2) =
    f (traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c).2)
  have he := actual_history_cut_readout N (Fintype.card Copy) (u : ℝ) (u : ℝ) d c le_rfl
  have hs := complete_ancestral_trace_stable N d c (u : ℝ) (by exact_mod_cast hu)
  simpa only [hs] using congrArg f he

/-- Stronger pointwise statement: the existing regular-clock hypothesis is
not needed for this eventual-value identity. Past and stored d are independent. -/
theorem actual_completed_chronological_terminal_unconditional (N : RootedBinary V E X)
    {sample : Copy → X} (s d : Code N sample) (ops : List (ProgramStep N))
    (past : Fin ops.length → SegmentRecord N sample) (c : Choice N d → ℝ)
    (f : Code N sample → Q) :
    terminalPath (chronologicalPath N ops (observeCalendar N f ops s past,
      GProgram.G2.CompleteEpochPath.completePath N f d (completeAncestralTrace N d c))) =
      some (f (traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c).2)) := by
  apply terminal_path_of_constant_after _ _ (programDuration N ops + clockCover N d c)
  intro t ht
  have hD : programDuration N ops ≤ t :=
    (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ clockCover N d c from bot_le)).trans ht
  rw [chronological_path_after_duration N ops _ t hD]
  have hC : clockCover N d c ≤ t-programDuration N ops := (le_tsub_iff_left hD).mpr ht
  exact actual_complete_tail_constant N d c f _ hC

/-- Exact legacy argument order. The supplied original clock regularity is
retained for the consumer, without adding coherence or ancestral hypotheses. -/
theorem actual_completed_chronological_terminal (N : RootedBinary V E X)
    {sample : Copy → X} (s d : Code N sample) (ops : List (ProgramStep N))
    (past : Fin ops.length → SegmentRecord N sample) (c : Choice N d → ℝ)
    (_hc : ClockRegular c) (f : Code N sample → Q) :
    terminalPath (chronologicalPath N ops (observeCalendar N f ops s past,
      GProgram.G2.CompleteEpochPath.completePath N f d (completeAncestralTrace N d c))) =
      some (f (traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c).2)) :=
  actual_completed_chronological_terminal_unconditional N s d ops past c f

#print axioms nat_eventually_constant_unique
#print axioms terminal_path_of_nat_eventually_constant
#print axioms terminal_path_eq_some_iff
#print axioms terminal_path_eq_none_iff
#print axioms nat_eventually_constant_measurable
#print axioms terminal_path_measurable
#print axioms terminal_path_of_constant_after
#print axioms chronological_path_add_duration
#print axioms chronological_path_after_duration
#print axioms actual_complete_tail_constant
#print axioms actual_completed_chronological_terminal_unconditional
#print axioms actual_completed_chronological_terminal
end GProgram.G2.EventualPathReadout
