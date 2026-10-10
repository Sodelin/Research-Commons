import G2ChronologicalDecoration

/-!
Chronologically valid decorations along the actual literal clock recursion.
Contributor: dot (OpenAI), 6 October 2026.
Strict positivity and genuine winner resets are derived from the original
exponential clocks. Invalid clock outcomes are not used to certify time order.
-/
namespace GProgram.G2.StrictClockDecoration
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source MeasureTheory
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ClockBoundaryNull
open GProgram.G2.ActualDecorationFold GProgram.G2.ChronologicalDecoration
open GProgram.G2.FiniteAncestralTrace
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma strict_residual_clocks (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) (p : Choice N s) (hp : selectedWinner c = some p) :
    ∀ q : Choice N (stepDestination N s (some p)), 0 < c (destinationClockEmbedding N s p q).val-c p := by
  have hw := (selectedWinner_eq_some_iff c p).mp hp
  intro q
  exact sub_pos.mpr (hw.2 (destinationClockEmbedding N s p q))

/-- Every actual graft is strictly older than its two children. Future dormant
leaf dates are admitted only when source/calendar legality makes them active. -/
theorem literal_fold_timed_bound (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (a b H offset : ℝ)
    (c : Choice N s → ℝ) (hc : ClockRegular c) (hcpos : ∀ p, 0 < c p)
    (he : EpochCompatible N C a b (state s)) (ha : a ≤ offset) (hH : 0 ≤ H)
    (M : Copy → Copy → ℝ) (hM : TimedBound (fun x => C.age (N.leaf (sample x))) M (state s) offset) :
    TimedBound (fun x => C.age (N.leaf (sample x)))
      (foldMatrix N n s offset M (literalMarkedTrace N n H s c).2)
      (state (traceEndpoint N n s (literalMarkedTrace N n H s c).2)) (offset+H) := by
  induction n generalizing s H offset M with
  | zero => exact timed_bound_mono _ M (state s) (by linarith) hM
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, H < c p
      · simpa only [literalMarkedTrace,if_pos hstop,fold_empty,empty_trace_endpoint] using
          timed_bound_mono _ M (state s) (show offset ≤ offset+H by linarith) hM
      · simp only [literalMarkedTrace,if_neg hstop]
        cases hw : selectedWinner c with
        | none =>
            simpa only [fold_empty,empty_trace_endpoint] using
              timed_bound_mono _ M (state s) (show offset ≤ offset+H by linarith) hM
        | some p =>
            by_cases hp : c p ≤ H
            · simp only [if_pos hp,fold_prepend,prepend_trace_endpoint]
              have hd := actual_coded_timed_graft N C s p he ha
                (show offset < offset+c p by linarith [hcpos p]) M hM
              have hrec := ih (stepDestination N s (some p)) (H-c p) (offset+c p) _
                (destination_residual_regular N s c p hc hw) (strict_residual_clocks N s c p hw)
                (actual_step_destination_epoch N C s he (some p)) (by linarith [hcpos p])
                (sub_nonneg.mpr hp) _ hd
              have hbnd : offset+c p+(H-c p) = offset+H := by ring
              simpa only [hbnd] using hrec
            · simpa only [if_neg hp,fold_empty,empty_trace_endpoint] using
                timed_bound_mono _ M (state s) (show offset ≤ offset+H by linarith) hM

/-- Original exponential clocks supply the entire strict-clock event at full
mass, including an empty current catalogue, without conditional repair. -/
theorem actual_clock_fold_chronological_ae (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (n : Nat) (s : Code N sample)
    (a b H offset : ℝ) (he : EpochCompatible N C a b (state s)) (ha : a ≤ offset) (hH : 0 ≤ H)
    (M : Copy → Copy → ℝ) (hM : TimedBound (fun x => C.age (N.leaf (sample x))) M (state s) offset) :
    ∀ᵐ c ∂currentPairClockMeasure N r s,
      TimedBound (fun x => C.age (N.leaf (sample x)))
        (foldMatrix N n s offset M (literalMarkedTrace N n H s c).2)
        (state (traceEndpoint N n s (literalMarkedTrace N n H s c).2)) (offset+H) := by
  filter_upwards [actual_current_clock_regular_ae N r s,actual_clock_strictly_positive N r s] with c hc hp
  exact literal_fold_timed_bound N C n s a b H offset c hc hp he ha hH M hM

#print axioms literal_fold_timed_bound
#print axioms actual_clock_fold_chronological_ae
end GProgram.G2.StrictClockDecoration
