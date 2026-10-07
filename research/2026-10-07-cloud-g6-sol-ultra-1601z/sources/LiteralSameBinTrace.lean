import UnifiedLean.G6.BinClock

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED standalone derivative. No compiler has run on this source.
The SAME actual literal marked record is retained, including failed prefixes
and inactive padding. Only its constant-bin pair-tag fold is reduced.
No completion flag, regularity, sufficient budget or law equality is a premise.
-/

namespace CloudG3.LiteralSameBinTrace

open MeasureTheory ProbabilityTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.NativePairClockLaw
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualDecorationFold
open UnifiedLean.G6.BinHistory UnifiedLean.G6.BinFold UnifiedLean.G6.BinClock
open scoped Classical

variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem relation_monotone_refl (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : RelationMonotone N s s := by
  intro x y hxy
  exact hxy

theorem relation_monotone_trans (N : RootedBinary V E X) {sample : Copy → X}
    (s d e : Code N sample) (hsd : RelationMonotone N s d)
    (hde : RelationMonotone N d e) : RelationMonotone N s e := by
  intro x y hxy
  exact hde x y (hsd x y hxy)

/-- Actual legal-merger persistence across every literal recorded prefix.
This includes every clock vector and budget, not just successful paths. -/
theorem literal_trace_endpoint_relation_monotone (N : RootedBinary V E X)
    {sample : Copy → X} (n : ℕ) (s : Code N sample) (H : ℝ)
    (c : Choice N s → ℝ) :
    RelationMonotone N s
      (traceEndpoint N n s (literalMarkedTrace N n H s c).2) := by
  induction n generalizing s H with
  | zero => exact relation_monotone_refl N s
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, H < c p
      · simpa only [literalMarkedTrace,if_pos hstop,empty_trace_endpoint] using
          relation_monotone_refl N s
      · simp only [literalMarkedTrace,if_neg hstop]
        cases hw : selectedWinner c with
        | none =>
            simpa only [empty_trace_endpoint] using relation_monotone_refl N s
        | some p =>
            by_cases hp : c p ≤ H
            · simp only [if_pos hp,prepend_trace_endpoint]
              exact relation_monotone_trans N s (stepDestination N s (some p)) _
                (actual_destination_relation_monotone N s p)
                (ih (stepDestination N s (some p)) (H-c p)
                  (fun q => c (destinationClockEmbedding N s p q).val-c p))
            · simpa only [if_neg hp,empty_trace_endpoint] using
                relation_monotone_refl N s

set_option backward.isDefEq.respectTransparency false in
/-- The inherited age shift changes no flag or destination. Constant-bin tags
ignore those shifted ages even on inactive padding. -/
theorem foldTags_const_shift_ages (N : RootedBinary V E X) {sample : Copy → X}
    (tag : Tag) (n : ℕ) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → Tag) (age : ℝ) (z : ClockTrace N sample n) :
    foldTags N (fun _ => tag) n s offset M (shiftTraceAges N age z) =
      foldTags N (fun _ => tag) n s offset M z := by
  induction n generalizing s M with
  | zero => rfl
  | succ n ih =>
      by_cases h : (z 0).1 = true
      · simp only [foldTags,shiftTraceAges,if_pos h]
        change foldTags N (fun _ => tag) n (z 0).2.2 offset
            (tagUpdate N s (z 0).2.2 tag M)
            (shiftTraceAges N age (fun i => z i.succ)) =
          foldTags N (fun _ => tag) n (z 0).2.2 offset
            (tagUpdate N s (z 0).2.2 tag M) (fun i => z i.succ)
        exact ih (z 0).2.2 _ (fun i => z i.succ)
      · simp only [foldTags,shiftTraceAges,if_neg h]
        change foldTags N (fun _ => tag) n s offset M
            (shiftTraceAges N age (fun i => z i.succ)) =
          foldTags N (fun _ => tag) n s offset M (fun i => z i.succ)
        exact ih s M (fun i => z i.succ)

theorem foldTags_const_empty (N : RootedBinary V E X) {sample : Copy → X}
    (tag : Tag) (n : ℕ) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → Tag) :
    foldTags N (fun _ => tag) n s offset M (emptyTrace N n s) = M := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change foldTags N (fun _ => tag) n s offset M (emptyTrace N n s) = M
      exact ih

theorem foldTags_const_prepend (N : RootedBinary V E X) {sample : Copy → X}
    (tag : Tag) (n : ℕ) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → Tag) (age : ℝ) (d : Code N sample)
    (z : ClockTrace N sample n) :
    foldTags N (fun _ => tag) (n+1) s offset M (prependTrace N age d z) =
      foldTags N (fun _ => tag) n d offset (tagUpdate N s d tag M) z := by
  change foldTags N (fun _ => tag) n d offset (tagUpdate N s d tag M)
    (shiftTraceAges N age z) = _
  exact foldTags_const_shift_ages N tag n d offset (tagUpdate N s d tag M) age z

/-- Entire SAME literal record, arbitrary finite budget and failed/incomplete
prefix. The actual endpoint Code retains the genealogy; no tree is rebuilt
from the pair partition or from bin values. -/
theorem literal_same_bin_endpoint_fold (N : RootedBinary V E X)
    {sample : Copy → X} (tag : Tag) (n : ℕ) (s : Code N sample)
    (H offset : ℝ) (c : Choice N s → ℝ) (M : Copy → Copy → Tag) :
    foldTags N (fun _ => tag) n s offset M (literalMarkedTrace N n H s c).2 =
      tagUpdate N s (traceEndpoint N n s (literalMarkedTrace N n H s c).2) tag M := by
  induction n generalizing s H M with
  | zero => exact (tag_update_self N s tag M).symm
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, H < c p
      · simp only [literalMarkedTrace,if_pos hstop,foldTags_const_empty,
          empty_trace_endpoint,tag_update_self]
      · simp only [literalMarkedTrace,if_neg hstop]
        cases hw : selectedWinner c with
        | none => simp only [foldTags_const_empty,empty_trace_endpoint,tag_update_self]
        | some p =>
            by_cases hp : c p ≤ H
            · simp only [if_pos hp,foldTags_const_prepend,prepend_trace_endpoint]
              rw [ih (stepDestination N s (some p)) (H-c p)
                (fun q => c (destinationClockEmbedding N s p q).val-c p)
                (tagUpdate N s (stepDestination N s (some p)) tag M)]
              exact same_bin_update_comp N s (stepDestination N s (some p)) _ tag M
                (actual_destination_relation_monotone N s p)
                (literal_trace_endpoint_relation_monotone N n
                  (stepDestination N s (some p)) (H-c p)
                  (fun q => c (destinationClockEmbedding N s p q).val-c p))
            · simp only [if_neg hp,foldTags_const_empty,empty_trace_endpoint,tag_update_self]

/-- The original current-pair clock measure supplies one event for every
budget and old matrix. This is derived from actual clock support, without
conditioning on completion or postulating a law equality. -/
theorem actual_same_bin_endpoint_fold (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (offset H : ℝ)
    (bin : ℝ → Tag) (tag : Tag)
    (hbin : ∀ a : ℝ, offset < a → a < offset+H → bin a = tag) :
    ∀ᵐ c ∂currentPairClockMeasure N r s, ∀ (n : ℕ) (M : Copy → Copy → Tag),
      foldTags N bin n s offset M (literalMarkedTrace N n H s c).2 =
        tagUpdate N s (traceEndpoint N n s (literalMarkedTrace N n H s c).2) tag M := by
  filter_upwards [actual_bin_constant_fold N r s offset H bin tag hbin] with c hc
  intro n M
  exact (hc n M).trans (literal_same_bin_endpoint_fold N tag n s H offset c M)

#print axioms relation_monotone_refl
#print axioms relation_monotone_trans
#print axioms literal_trace_endpoint_relation_monotone
#print axioms foldTags_const_shift_ages
#print axioms foldTags_const_empty
#print axioms foldTags_const_prepend
#print axioms literal_same_bin_endpoint_fold
#print axioms actual_same_bin_endpoint_fold

end CloudG3.LiteralSameBinTrace
