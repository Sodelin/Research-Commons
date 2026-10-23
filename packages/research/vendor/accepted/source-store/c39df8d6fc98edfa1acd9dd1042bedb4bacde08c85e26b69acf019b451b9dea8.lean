import UnifiedLean.G6.BinFold
import G2SameClockContinuation
import G2FiniteAncestralTrace

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED author derivative; no compiler has run on this file.
The attributed original active-record continuation and complete-trace
stability are consumed without altering clocks, physical source or padding.
List fold algebra alone does not admit arbitrary lists as physical histories.
The joint probabilistic attachment is a separate hand proposition.
-/

namespace CloudG3.ActualCutTagRefinement
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.LiteralCutResidual GProgram.G2.SameClockContinuation
open GProgram.G2.FiniteAncestralTrace
open UnifiedLean.G6.BinHistory UnifiedLean.G6.BinFold
open scoped Classical

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- A total fold of the active list. A source claim additionally requires
the list to be the proved original compiler's active records. -/
noncomputable def foldTagRecords (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (offset : ℝ) : Code N sample → (Copy → Copy → Tag) →
      List (Bool × ℝ × Code N sample) → (Copy → Copy → Tag)
  | _, B, [] => B
  | s, B, r :: rs => foldTagRecords N bin offset r.2.2
      (tagUpdate N s r.2.2 (bin (offset + r.2.1)) B) rs

/-- Inactive padding writes nothing. This is fold algebra, not a legality
claim for an arbitrary padded vector. -/
theorem fold_tags_eq_active_records (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (n : ℕ) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) (z : ClockTrace N sample n) :
    foldTags N bin n s offset B z =
      foldTagRecords N bin offset s B (activeRecords z) := by
  induction n generalizing s B with
  | zero => simp [foldTags, foldTagRecords, activeRecords]
  | succ n ih =>
      cases h : (z 0).1 with
      | false =>
          simp only [foldTags, h, Bool.false_eq_true, if_false]
          simpa [activeRecords, List.ofFn_succ, h] using
            ih s B (fun i => z i.succ)
      | true =>
          simp only [foldTags, h, if_true]
          simpa [activeRecords, List.ofFn_succ, h, foldTagRecords] using
            ih (z 0).2.2 (tagUpdate N s (z 0).2.2 (bin (offset + (z 0).2.1)) B)
              (fun i => z i.succ)

/-- Concatenation carries the exact last destination and all old tags. -/
theorem fold_tag_records_append (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (offset : ℝ) (s : Code N sample) (B : Copy → Copy → Tag)
    (l q : List (Bool × ℝ × Code N sample)) :
    foldTagRecords N bin offset s B (l ++ q) =
      foldTagRecords N bin offset (recordEndpoint s l)
        (foldTagRecords N bin offset s B l) q := by
  induction l generalizing s B with
  | nil => rfl
  | cons r l ih =>
      simpa only [List.cons_append, foldTagRecords, recordEndpoint_cons] using
        ih r.2.2 (tagUpdate N s r.2.2 (bin (offset + r.2.1)) B)

/-- The original shiftRecord changes the age offset only. -/
theorem fold_tag_records_shift (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (offset age : ℝ) (s : Code N sample)
    (B : Copy → Copy → Tag) (l : List (Bool × ℝ × Code N sample)) :
    foldTagRecords N bin offset s B (l.map (shiftRecord age)) =
      foldTagRecords N bin (offset + age) s B l := by
  induction l generalizing s B with
  | nil => rfl
  | cons r l ih =>
      simp only [List.map_cons, foldTagRecords, shiftRecord, add_assoc]
      simpa only [add_assoc] using
        ih r.2.2 (tagUpdate N s r.2.2 (bin ((offset + age) + r.2.1)) B)

/-- The prefix's last active destination is the ACTUAL retained residual
Code. Regularity and budget suffice; a desired endpoint is not supplied. -/
theorem retained_cut_prefix_record_endpoint (N : RootedBinary V E X)
    {sample : Copy → X} (n : ℕ) (t : ℝ) (s d : Code N sample)
    (c : Choice N s → ℝ) (k : Choice N d → ℝ) (hc : ClockRegular c)
    (hn : liveCard s ≤ n)
    (hcut : literalCutResidual N n t s c = encodeResidual N d k) :
    recordEndpoint s (activeTrace N n t s c) = d := by
  have hd : literalClockEndpoint N n t s c = some d := by
    rw [← cut_endpoint_eq_literal N n s t c, hcut]
    rfl
  rw [literal_endpoint_of_success N n t s c
    (marked_trace_success_on_regular N n s t c hn hc)] at hd
  exact Option.some.inj hd

/-- Finite-interval refinement of the SAME actual clock record. The prefix
and residual are linked by the original compiler, not independently fitted. -/
theorem same_clock_tag_cut_refinement (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (n : ℕ) (t v offset : ℝ)
    (s d : Code N sample) (c : Choice N s → ℝ) (k : Choice N d → ℝ)
    (B : Copy → Copy → Tag) (hc : ClockRegular c) (hn : liveCard s ≤ n)
    (ht : 0 ≤ t) (hv : 0 ≤ v)
    (hcut : literalCutResidual N n t s c = encodeResidual N d k) :
    foldTags N bin n s offset B (literalMarkedTrace N n (t + v) s c).2 =
      foldTags N bin n d (offset + t)
        (foldTags N bin n s offset B (literalMarkedTrace N n t s c).2)
        (literalMarkedTrace N n v d k).2 := by
  simp_rw [fold_tags_eq_active_records]
  change foldTagRecords N bin offset s B (activeTrace N n (t + v) s c) =
    foldTagRecords N bin (offset + t) d
      (foldTagRecords N bin offset s B (activeTrace N n t s c))
      (activeTrace N n v d k)
  rw [same_clock_active_continuation N n t v s d c k hc hn ht hv hcut,
    fold_tag_records_append,
    retained_cut_prefix_record_endpoint N n t s d c k hc hn hcut,
    fold_tag_records_shift]

/-- At a cut, completed active records concatenate pathwise at the SAME
random covers. The enlarged horizon is only a proof device. -/
theorem same_clock_complete_active_cut_refinement (N : RootedBinary V E X)
    {sample : Copy → X} (t : ℝ) (s d : Code N sample)
    (c : Choice N s → ℝ) (k : Choice N d → ℝ) (hc : ClockRegular c)
    (ht : 0 ≤ t)
    (hcut : literalCutResidual N (Fintype.card Copy) t s c = encodeResidual N d k) :
    activeRecords (completeAncestralTrace N s c).2 =
      activeTrace N (Fintype.card Copy) t s c ++
        (activeRecords (completeAncestralTrace N d k).2).map (shiftRecord t) := by
  let H : ℝ := max (clockCover N s c : ℝ) (t + (clockCover N d k : ℝ))
  let v : ℝ := H - t
  have hH : (clockCover N s c : ℝ) ≤ H := le_max_left _ _
  have hk : (clockCover N d k : ℝ) ≤ v := by
    have h := le_max_right (clockCover N s c : ℝ) (t + (clockCover N d k : ℝ))
    dsimp only [v, H]
    linarith
  have hv : 0 ≤ v := le_trans (clockCover N d k).property hk
  have he : t + v = H := by dsimp [v]; ring
  have h := same_clock_active_continuation N (Fintype.card Copy) t v s d c k
    hc (Finset.card_le_univ s.val.live) ht hv hcut
  have hleft := complete_ancestral_trace_stable N s c H hH
  have hright := complete_ancestral_trace_stable N d k v hk
  rw [he] at h
  simpa only [activeTrace, hleft, hright] using h

/-- The raw endpoint of the SAME complete record is its active destination
fold, including empty carriers. -/
theorem complete_raw_endpoint_eq_records (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (c : Choice N s → ℝ) :
    traceEndpoint N (Fintype.card Copy) s (completeAncestralTrace N s c).2 =
      recordEndpoint s (activeRecords (completeAncestralTrace N s c).2) := by
  simpa only [completeAncestralTrace, activeTrace] using
    actual_trace_endpoint_fold N (Fintype.card Copy) (clockCover N s c : ℝ) s c

/-- Completion keeps the exact endpoint genealogy after inserting the cut. -/
theorem same_clock_complete_endpoint_cut_refinement (N : RootedBinary V E X)
    {sample : Copy → X} (t : ℝ) (s d : Code N sample)
    (c : Choice N s → ℝ) (k : Choice N d → ℝ) (hc : ClockRegular c)
    (ht : 0 ≤ t)
    (hcut : literalCutResidual N (Fintype.card Copy) t s c = encodeResidual N d k) :
    traceEndpoint N (Fintype.card Copy) s (completeAncestralTrace N s c).2 =
      traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d k).2 := by
  rw [complete_raw_endpoint_eq_records, complete_raw_endpoint_eq_records,
    same_clock_complete_active_cut_refinement N t s d c k hc ht hcut,
    recordEndpoint_append, recordEndpoint_shift,
    retained_cut_prefix_record_endpoint N (Fintype.card Copy) t s d c k hc
      (Finset.card_le_univ s.val.live) hcut]

/-- The complete joint Code/tag readout is identical. Equality of partitions
or an endpoint harmonicity result is not substituted for this statement. -/
theorem same_clock_complete_joint_readout_cut_refinement (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (t offset : ℝ) (s d : Code N sample)
    (c : Choice N s → ℝ) (k : Choice N d → ℝ) (B : Copy → Copy → Tag)
    (hc : ClockRegular c) (ht : 0 ≤ t)
    (hcut : literalCutResidual N (Fintype.card Copy) t s c = encodeResidual N d k) :
    (traceEndpoint N (Fintype.card Copy) s (completeAncestralTrace N s c).2,
      foldTags N bin (Fintype.card Copy) s offset B (completeAncestralTrace N s c).2) =
    (traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d k).2,
      foldTags N bin (Fintype.card Copy) d (offset + t)
        (foldTags N bin (Fintype.card Copy) s offset B
          (literalMarkedTrace N (Fintype.card Copy) t s c).2)
        (completeAncestralTrace N d k).2) := by
  apply Prod.ext
  · exact same_clock_complete_endpoint_cut_refinement N t s d c k hc ht hcut
  · simp_rw [fold_tags_eq_active_records]
    rw [same_clock_complete_active_cut_refinement N t s d c k hc ht hcut,
      fold_tag_records_append,
      retained_cut_prefix_record_endpoint N (Fintype.card Copy) t s d c k hc
        (Finset.card_le_univ s.val.live) hcut,
      fold_tag_records_shift]
    rfl

#print axioms fold_tags_eq_active_records
#print axioms fold_tag_records_append
#print axioms fold_tag_records_shift
#print axioms retained_cut_prefix_record_endpoint
#print axioms same_clock_tag_cut_refinement
#print axioms same_clock_complete_active_cut_refinement
#print axioms complete_raw_endpoint_eq_records
#print axioms same_clock_complete_endpoint_cut_refinement
#print axioms same_clock_complete_joint_readout_cut_refinement

end CloudG3.ActualCutTagRefinement
