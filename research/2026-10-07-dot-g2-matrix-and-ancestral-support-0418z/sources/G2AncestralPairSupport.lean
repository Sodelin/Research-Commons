import G2CompleteCalendarAttachment
import G2PairBirthFold

/-!
Actual ancestral endpoint pair support.
Contributor: dot (OpenAI), 7 October 2026.
AncestralRoot is retained explicitly; stabilization alone is insufficient.
-/
namespace GProgram.G2.AncestralPairSupport
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.FiniteAncestralTrace
open GProgram.G2.ActualCalendarTrace GProgram.G2.PairBirthFold
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

def AllPairsJoined (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Prop :=
  ∀ x y : Copy, (state s).ancestor x = (state s).ancestor y

lemma all_pairs_joined_of_live_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : liveCard s ≤ 1) : AllPairsJoined N s := by
  intro x y
  exact (Finset.card_le_one.mp hs) _ (s.property.forest.ancestor_live x)
    _ (s.property.forest.ancestor_live y)

/-- The original terminal-card theorem supplies the pair support witness.
The original root premise is essential for this conclusion. -/
theorem actual_ancestral_pairs_joined (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) (hs : AncestralRoot N s)
    (hc : ClockRegular c) :
    AllPairsJoined N (traceEndpoint N (Fintype.card Copy) s
      (completeAncestralTrace N s c).2) := by
  obtain ⟨e,he,_,hcard⟩ := complete_ancestral_trace_terminal N s c hs hc
  cases hz : (completeAncestralTrace N s c).1 with
  | false => simp [decodedEndpoint,hz] at he
  | true =>
      have hend : traceEndpoint N (Fintype.card Copy) s
          (completeAncestralTrace N s c).2 = e := by
        simpa [decodedEndpoint,hz] using he
      rw [hend]
      exact all_pairs_joined_of_live_card N e hcard

lemma ancestral_pairs_event_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) :
    MeasurableSet {z : Bool × ClockTrace N sample (Fintype.card Copy) |
      AllPairsJoined N (traceEndpoint N (Fintype.card Copy) s z.2)} :=
  ((measurable_of_countable (AllPairsJoined N)).comp
    ((trace_endpoint_measurable N _ s).comp measurable_snd)).setOf

theorem actual_ancestral_pairs_joined_ae (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s,
      AllPairsJoined N (traceEndpoint N (Fintype.card Copy) s z.2) := by
  rw [completeAncestralTraceLaw]
  apply (ae_map_iff (complete_ancestral_trace_measurable N s).aemeasurable
    (ancestral_pairs_event_measurable N s)).mpr
  filter_upwards [actual_current_clock_regular_ae N r s] with c hc
  exact actual_ancestral_pairs_joined N s c hs hc

/-- Every initially separated pair has an actual finite birth record on the
regular ancestral trace; no first-age equality is inserted as a premise. -/
theorem actual_ancestral_first_pair_birth_exists (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (c : Choice N s → ℝ)
    (hs : AncestralRoot N s) (hc : ClockRegular c) (x y : Copy)
    (hxy : (state s).ancestor x ≠ (state s).ancestor y) :
    ∃ a : ℝ, firstPairBirth N (Fintype.card Copy) s 0
      (completeAncestralTrace N s c).2 x y = some a := by
  exact (actual_first_pair_birth_iff_endpoint N (Fintype.card Copy)
    (clockCover N s c : ℝ) s c 0 x y hxy).mpr
      (actual_ancestral_pairs_joined N s c hs hc x y)

#print axioms all_pairs_joined_of_live_card
#print axioms actual_ancestral_pairs_joined
#print axioms ancestral_pairs_event_measurable
#print axioms actual_ancestral_pairs_joined_ae
#print axioms actual_ancestral_first_pair_birth_exists
end GProgram.G2.AncestralPairSupport
