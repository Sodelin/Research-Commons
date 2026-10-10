import G2LiteralMarkedClockTrace
import UnifiedLean.Source.SourceAncestralCompletion

/-!
# Finite completion of the actual ancestral marked trace

Contributor: dot (OpenAI), 2026-10-06. Newly reconstructed source satisfying
preserved consumer interfaces, not recovery of the missing historical file.
The finite random cover is a measurable function of the SAME original clock
vector. Its trajectory bound is derived through actual retained-coordinate
subtraction. No fixed truncation or completion-kernel identity is assumed.
-/

namespace GProgram.G2.FiniteAncestralTrace
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.LiteralMarkedClockTrace
open scoped Classical NNReal BigOperators

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.LiteralMarkedClockTrace.choiceOptionMeasurable

/-- A finite measurable cover from the original finite coordinate vector.
The sum is only used to dominate each initial coordinate; the actual
trajectory-cover property is proved below by a remaining-horizon invariant. -/
noncomputable def clockCover (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) : ℝ≥0 :=
  ⟨∑ p : Choice N s, |c p|,Finset.sum_nonneg (fun p _ => abs_nonneg (c p))⟩

lemma clock_le_cover (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) (p : Choice N s) :
    c p ≤ (clockCover N s c : ℝ) := by
  change c p ≤ ∑ q : Choice N s, |c q|
  exact le_trans (le_abs_self (c p))
    (Finset.single_le_sum (fun q _ => abs_nonneg (c q)) (Finset.mem_univ p))

lemma clock_cover_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Measurable (clockCover N s) := by
  unfold clockCover
  apply Measurable.subtype_mk
  fun_prop

/-- This is the trajectory invariant: subtracting the SAME selected age
from the retained original coordinate and the horizon preserves domination.
No bound on a sum of freshly sampled waiting times is substituted. -/
lemma destination_clock_bound (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) (p : Choice N s) (t : ℝ)
    (hb : ∀ q : Choice N s, c q ≤ t) :
    ∀ q : Choice N (stepDestination N s (some p)),
      c (destinationClockEmbedding N s p q).val-c p ≤ t-c p := by
  intro q
  exact sub_le_sub_right (hb (destinationClockEmbedding N s p q).val) (c p)

/-- Once the horizon dominates every original coordinate, further horizon
extension changes no branch of the actual trace recursion. This includes
its success flag and padding because the same event sequence is followed;
it is not a padded-vector translation statement. -/
theorem literal_trace_stable_above_coordinates (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (u t : ℝ) (s : Code N sample)
    (c : Choice N s → ℝ) (hb : ∀ p, c p ≤ u) (hut : u ≤ t) :
    literalMarkedTrace N n u s c = literalMarkedTrace N n t s c := by
  induction n generalizing s u t with
  | zero =>
      by_cases hstop : ∀ p : Choice N s, u < c p
      · have hstop' : ∀ p : Choice N s, t < c p := by
          intro p
          exact False.elim ((not_lt_of_ge (hb p)) (hstop p))
        simp [literalMarkedTrace,hstop,hstop']
      · have hstop' : ¬ ∀ p : Choice N s, t < c p := by
          obtain ⟨p,_⟩ := not_forall.mp hstop
          intro h
          exact (not_lt_of_ge (le_trans (hb p) hut)) (h p)
        simp [literalMarkedTrace,hstop,hstop']
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, u < c p
      · have hstop' : ∀ p : Choice N s, t < c p := by
          intro p
          exact False.elim ((not_lt_of_ge (hb p)) (hstop p))
        simp [literalMarkedTrace,hstop,hstop']
      · have hstop' : ¬ ∀ p : Choice N s, t < c p := by
          obtain ⟨p,_⟩ := not_forall.mp hstop
          intro h
          exact (not_lt_of_ge (le_trans (hb p) hut)) (h p)
        simp only [literalMarkedTrace,if_neg hstop,if_neg hstop']
        cases hp : selectedWinner c with
        | none => rfl
        | some p =>
            simp only [if_pos (hb p),if_pos (le_trans (hb p) hut)]
            have he := ih (u-c p) (t-c p) (stepDestination N s (some p))
              (fun q => c (destinationClockEmbedding N s p q).val-c p)
              (destination_clock_bound N s c p u hb) (sub_le_sub_right hut (c p))
            rw [he]

/-- On ancestral states, a dominating horizon cannot stop while two live
roots remain. Actual winner selection, ancestral preservation and strict
live-card descent therefore complete the source within the supplied budget. -/
theorem literal_ancestral_terminal_above_coordinates (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (t : ℝ) (s : Code N sample)
    (c : Choice N s → ℝ) (hs : AncestralRoot N s) (hc : ClockRegular c)
    (hn : liveCard s ≤ n) (hb : ∀ p, c p ≤ t) :
    ∃ e, literalClockEndpoint N n t s c = some e ∧ AncestralRoot N e ∧ liveCard e ≤ 1 := by
  induction n generalizing s t with
  | zero =>
      have hcard : liveCard s ≤ 1 := by omega
      letI := choice_empty_of_terminal_card N s hcard
      have hstop : ∀ p : Choice N s, t < c p := fun p => isEmptyElim p
      exact ⟨s,by simp [literalClockEndpoint,hstop],hs,hcard⟩
  | succ n ih =>
      by_cases hcard : liveCard s ≤ 1
      · letI := choice_empty_of_terminal_card N s hcard
        have hstop : ∀ p : Choice N s, t < c p := fun p => isEmptyElim p
        exact ⟨s,by simp [literalClockEndpoint,hstop],hs,hcard⟩
      · letI := ancestral_choice_exists N s hs (lt_of_not_ge hcard)
        obtain ⟨p,hp⟩ := regular_winner_exists c hc
        have hpt : c p ≤ t := hb p
        have hstop : ¬ ∀ q : Choice N s, t < c q := by
          intro h
          exact (not_lt_of_ge hpt) (h p)
        have hdestcard := merger_destination_card N s p
        have hn' : liveCard (stepDestination N s (some p)) ≤ n := by omega
        obtain ⟨e,he,her,hec⟩ := ih (t-c p) (stepDestination N s (some p))
          (fun q => c (destinationClockEmbedding N s p q).val-c p)
          (ancestral_merger_preserved N s hs p)
          (destination_residual_regular N s c p hc hp) hn'
          (destination_clock_bound N s c p t hb)
        refine ⟨e,?_,her,hec⟩
        simpa only [literalClockEndpoint,if_neg hstop,hp,if_pos hpt] using he

noncomputable def completeAncestralTrace (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (c : Choice N s → ℝ) :
    Bool × ClockTrace N sample (Fintype.card Copy) :=
  literalMarkedTrace N (Fintype.card Copy) (clockCover N s c : ℝ) s c

noncomputable def completeAncestralTraceLaw (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    Measure (Bool × ClockTrace N sample (Fintype.card Copy)) :=
  (currentPairClockMeasure N r s).map (completeAncestralTrace N s)

/-- Variable-horizon measurability uses the proved JOINT original compiler
measurability and the cover of that same clock vector. -/
theorem complete_ancestral_trace_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) : Measurable (completeAncestralTrace N s) := by
  exact (marked_trace_joint_measurable N (Fintype.card Copy) s).comp
    ((clock_cover_measurable N s).subtype_coe.prodMk measurable_id)

/-- The law is the actual unconditional pushforward of the original finite
clock product; no success conditioning or terminal-law replacement occurs. -/
theorem complete_ancestral_trace_probability (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    IsProbabilityMeasure (completeAncestralTraceLaw N r s) := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  change IsProbabilityMeasure ((Measure.pi (fun p => expMeasure (choiceRate N r s p))).map
    (completeAncestralTrace N s))
  exact Measure.isProbabilityMeasure_map (complete_ancestral_trace_measurable N s).aemeasurable

/-- Exact unchanged-consumer terminal interface, including empty and
singleton carriers. Only regularity of the original clocks is required. -/
theorem complete_ancestral_trace_terminal (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (c : Choice N s → ℝ)
    (hs : AncestralRoot N s) (hc : ClockRegular c) :
    ∃ e, decodedEndpoint N (Fintype.card Copy) s (completeAncestralTrace N s c) = some e ∧
      AncestralRoot N e ∧ liveCard e ≤ 1 := by
  obtain ⟨e,he,hr,hcard⟩ := literal_ancestral_terminal_above_coordinates N
    (Fintype.card Copy) (clockCover N s c : ℝ) s c hs hc
    (Finset.card_le_univ s.val.live) (clock_le_cover N s c)
  refine ⟨e,?_,hr,hcard⟩
  simpa only [completeAncestralTrace,marked_trace_endpoint_eq] using he

/-- Large-horizon stability is derived on the same original clock vector,
for the whole actual Bool/padded trace, even outside the regular event. -/
theorem complete_ancestral_trace_stable (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (c : Choice N s → ℝ) (t : ℝ)
    (ht : (clockCover N s c : ℝ) ≤ t) :
    literalMarkedTrace N (Fintype.card Copy) t s c = completeAncestralTrace N s c := by
  exact (literal_trace_stable_above_coordinates N (Fintype.card Copy)
    (clockCover N s c : ℝ) t s c (clock_le_cover N s c) ht).symm

#print axioms clock_le_cover
#print axioms clock_cover_measurable
#print axioms destination_clock_bound
#print axioms literal_trace_stable_above_coordinates
#print axioms literal_ancestral_terminal_above_coordinates
#print axioms complete_ancestral_trace_measurable
#print axioms complete_ancestral_trace_probability
#print axioms complete_ancestral_trace_terminal
#print axioms complete_ancestral_trace_stable

end GProgram.G2.FiniteAncestralTrace
