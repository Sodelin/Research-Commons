/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual three-header plus nested-rows spine, with two PROVIDED physical
caps and failure-absorbing stages. Original external framing is retained.
This is a PREFIX routine, not cap creation or complete-input validation.
-/
import PolytomyGuardedRowsSection

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

structure PrefixPorts (K : Type) where
  r : K
  c : K
  d : K
  b : K
  t : K
  hrc : r ≠ c
  hrd : r ≠ d
  hrb : r ≠ b
  hrt : r ≠ t
  hcd : c ≠ d
  hcb : c ≠ b
  hct : c ≠ t
  hdb : d ≠ b
  hdt : d ≠ t
  hbt : b ≠ t

def PrefixReady (p : PrefixPorts K) (C D L : ℕ) (s : CountdownStore (NumericStack K) F) : Prop :=
  RowsReady p.c p.d C L s ∧ s.stk (.inr p.b) = List.replicate D true ∧ s.stk (.inr p.t) = []

def PrefixReturned (p : PrefixPorts K) (C D L : ℕ) (s : CountdownStore (NumericStack K) F) : Prop :=
  RowsReturned p.c p.d C L s ∧ s.stk (.inr p.b) = List.replicate D true ∧ s.stk (.inr p.t) = []

theorem smallHeader_ready (p : PrefixPorts K) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : PrefixReady p C D L s) :
    PrefixReady p C D L (guardedNumericEval p.r C s) := by
  obtain ⟨n, hn, he, hi⟩ := guardedNumeric_executes p.r p.c p.hrc C L s hs.1.1
  refine ⟨⟨hi, ?_, ?_⟩, ?_, ?_⟩
  · exact (guardedNumeric_extra p.r p.c (Ne.symm p.hrc) C s).trans hs.1.2.1
  · exact (guardedNumeric_extra p.r p.d (Ne.symm p.hrd) C s).trans hs.1.2.2
  · exact (guardedNumeric_extra p.r p.b (Ne.symm p.hrb) C s).trans hs.2.1
  · exact (guardedNumeric_extra p.r p.t (Ne.symm p.hrt) C s).trans hs.2.2

theorem largeHeader_ready (p : PrefixPorts K) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : PrefixReady p C D L s) :
    PrefixReady p C D L (capSwitchedHeaderEval p.r p.b p.t D s) := by
  obtain ⟨n, hn, he, hi, hb, ht⟩ := capSwitchedHeader_executes p.r p.c p.b p.t
    p.hrc p.hrb p.hrt p.hbt C D L s hs.1.1 hs.2.1 hs.2.2
  refine ⟨⟨hi, ?_, ?_⟩, hb, ht⟩
  · exact (capSwitchedHeader_extra p.r p.b p.t p.c (Ne.symm p.hrc) p.hcb p.hct D s).trans hs.1.2.1
  · exact (capSwitchedHeader_extra p.r p.b p.t p.d (Ne.symm p.hrd) p.hdb p.hdt D s).trans hs.1.2.2

def providedCapPrefixRoutine (p : PrefixPorts K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (guardedNumericRoutine p.r p.c)
    (RoutineComposition.seq (guardedNumericRoutine p.r p.c)
      (RoutineComposition.seq (capSwitchedHeaderRoutine p.r p.c p.b p.t)
        (guardedRowsRoutine p.r p.c p.d)))

def providedCapPrefixEval (p : PrefixPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  guardedRowsEval p.r p.c p.d C
    (capSwitchedHeaderEval p.r p.b p.t D
      (guardedNumericEval p.r C (guardedNumericEval p.r C s)))

def providedCapPrefixStepBound (L C D : ℕ) : ℕ :=
  2 * numericRecordStepBound L C + numericRecordStepBound L D +
    framedRowsStepBound L C + 3 * C + 3 * D + 10

theorem providedCapPrefix_executes (p : PrefixPorts K) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : PrefixReady p C D L s) :
    ∃ n ≤ providedCapPrefixStepBound L C D,
      (providedCapPrefixRoutine p).Executes s (providedCapPrefixEval p C D s) n ∧
      PrefixReturned p C D L (providedCapPrefixEval p C D s) := by
  let s1 := guardedNumericEval p.r C s
  let s2 := guardedNumericEval p.r C s1
  let s3 := capSwitchedHeaderEval p.r p.b p.t D s2
  have hi1 := smallHeader_ready p C D L s hs
  have hi2 := smallHeader_ready p C D L s1 hi1
  have hi3 := largeHeader_ready p C D L s2 hi2
  obtain ⟨n1, hn1, h1, _⟩ := guardedNumeric_executes p.r p.c p.hrc C L s hs.1.1
  obtain ⟨n2, hn2, h2, _⟩ := guardedNumeric_executes p.r p.c p.hrc C L s1 hi1.1.1
  obtain ⟨n3, hn3, h3, _, _, _⟩ := capSwitchedHeader_executes p.r p.c p.b p.t
    p.hrc p.hrb p.hrt p.hbt C D L s2 hi2.1.1 hi2.2.1 hi2.2.2
  obtain ⟨n4, hn4, h4, hi4⟩ := guardedRows_executes p.r p.c p.d p.hrc p.hrd p.hcd C L s3 hi3.1
  have h34 := RoutineComposition.seq_executes (capSwitchedHeaderRoutine p.r p.c p.b p.t)
    (guardedRowsRoutine p.r p.c p.d) h3 h4
  have h234 := RoutineComposition.seq_executes (guardedNumericRoutine p.r p.c)
    (RoutineComposition.seq (capSwitchedHeaderRoutine p.r p.c p.b p.t)
      (guardedRowsRoutine p.r p.c p.d)) h2 h34
  have hall := RoutineComposition.seq_executes (guardedNumericRoutine p.r p.c)
    (RoutineComposition.seq (guardedNumericRoutine p.r p.c)
      (RoutineComposition.seq (capSwitchedHeaderRoutine p.r p.c p.b p.t)
        (guardedRowsRoutine p.r p.c p.d))) h1 h234
  refine ⟨n1 + (n2 + (n3 + n4)), ?_, hall, hi4, ?_, ?_⟩
  · unfold providedCapPrefixStepBound capSwitchedHeaderStepBound at *
    omega
  · exact (guardedRows_extra p.r p.c p.d p.b (Ne.symm p.hrb)
      (Ne.symm p.hcb) (Ne.symm p.hdb) C s3).trans hi3.2.1
  · exact (guardedRows_extra p.r p.c p.d p.t (Ne.symm p.hrt)
      (Ne.symm p.hct) (Ne.symm p.hdt) C s3).trans hi3.2.2

theorem providedCapPrefix_extra (p : PrefixPorts K) (k : K)
    (hkr : k ≠ p.r) (hkc : k ≠ p.c) (hkd : k ≠ p.d) (hkb : k ≠ p.b) (hkt : k ≠ p.t)
    (C D : ℕ) (s : CountdownStore (NumericStack K) F) :
    (providedCapPrefixEval p C D s).stk (.inr k) = s.stk (.inr k) := by
  unfold providedCapPrefixEval
  rw [guardedRows_extra p.r p.c p.d k hkr hkc hkd,
    capSwitchedHeader_extra p.r p.b p.t k hkr hkb hkt,
    guardedNumeric_extra p.r k hkr, guardedNumeric_extra p.r k hkr]

theorem capSwitchedHeader_frame (r b t : K) (D : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    (capSwitchedHeaderEval r b t D s).state.1.1 = s.state.1.1 := by
  unfold capSwitchedHeaderEval
  change (guardedNumericEval r D (numericCapSwapEval b t s)).state.1.1 = s.state.1.1
  rw [guardedNumeric_frame]
  rfl

theorem providedCapPrefix_frame (p : PrefixPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    (providedCapPrefixEval p C D s).state.1.1 = s.state.1.1 := by
  unfold providedCapPrefixEval
  rw [guardedRows_frame, capSwitchedHeader_frame, guardedNumeric_frame, guardedNumeric_frame]

theorem providedCapPrefix_record_bound (p : PrefixPorts K) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : PrefixReady p C D L s) :
    ((providedCapPrefixEval p C D s).stk (.inr p.r)).length ≤
      (s.stk (.inr p.r)).length + L ^ 2 * (C + 2) + 2 * L + 2 * C + D + 4 := by
  let s1 := guardedNumericEval p.r C s
  let s2 := guardedNumericEval p.r C s1
  let s3 := capSwitchedHeaderEval p.r p.b p.t D s2
  have hi1 := smallHeader_ready p C D L s hs
  have hi2 := smallHeader_ready p C D L s1 hi1
  have hi3 := largeHeader_ready p C D L s2 hi2
  have h1 := guardedNumeric_record_bound p.r C s
  have h2 := guardedNumeric_record_bound p.r C s1
  have h3 := capSwitchedHeader_record_bound p.r p.b p.t p.hrb p.hrt D s2
  have h4 := guardedRows_record_bound p.r p.c p.d p.hrc p.hrd p.hcd C L s3 hi3.1
  change ((guardedRowsEval p.r p.c p.d C s3).stk (.inr p.r)).length ≤ _
  omega

/- This operational spine contains no numeric cap/size parameter in its
routine code. C,D,L occur in data assumptions, pure semantics and bounds.
Cap construction, full-input finish/tag/reversal/cleanup, downstream
constructor and independent checker, encoded hardness and kernel closure
remain open. Exact original-prefix observation is supplied separately.
-/

end PolytomyReductionModel
