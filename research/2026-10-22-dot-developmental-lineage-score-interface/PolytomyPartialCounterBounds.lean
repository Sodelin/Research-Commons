/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

All-path bounds on BOTH physical rows counters, including failed inner
rows with leftover tallies. These support unconditional final cleanup;
success-only counter exhaustion would not justify its polynomial cost.
-/
import PolytomyCompleteInputFinish

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem countdownLoop_counter_le (counter : K) (f : CountdownStore K F → CountdownStore K F)
    (hf : ∀ s, (f s).stk counter = s.stk counter) (n : ℕ) (s : CountdownStore K F) :
    ((countdownLoopEval counter f n s).stk counter).length ≤ (s.stk counter).length := by
  induction n generalizing s with
  | zero => exact le_refl _
  | succ n ih =>
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          let u := countdownPeek counter (f (countdownPop counter s))
          have hi := ih u
          have hu : u.stk counter = (s.stk counter).tail := by
            change (f (countdownPop counter s)).stk counter = _
            rw [hf, countdownPop_counter]
          have htail : (s.stk counter).tail.length ≤ (s.stk counter).length := by
            cases s.stk counter <;> simp
          simp only [countdownLoopEval, hg, ↓reduceIte]
          exact hi.trans (by rw [hu]; exact htail)

theorem countdown_counter_le (counter : K) (f : CountdownStore K F → CountdownStore K F)
    (hf : ∀ s, (f s).stk counter = s.stk counter) (s : CountdownStore K F) :
    ((countdownEval counter f s).stk counter).length ≤ (s.stk counter).length :=
  countdownLoop_counter_le counter f hf (s.stk counter).length (countdownPeek counter s)

theorem framedNumericRow_counter_bound (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (hc : base c = []) (frame : F) (C L : ℕ)
    (bits : List Bool) (hL : bits.length ≤ L) :
    ((framedNumericRowResult r c base frame C bits).stk (.inr c)).length ≤ L := by
  let s := listCountPrefixResult r c base frame (List.replicate C true) (readUnaryFrame bits)
  have hloop := countdown_counter_le (.inr c : NumericStack K) (numericRecordEval r C)
    (numericRecordEval_extra r c (Ne.symm hrc) C) s
  have hp := listCountPrefix_counter_bound r c base hc frame (List.replicate C true) bits
  exact hloop.trans (hp.trans hL)

def BoundedRowOuterInv (c : K) (C L : ℕ) (s : CountdownStore (NumericStack K) F) : Prop :=
  RowOuterInv c C L s ∧ (s.stk (.inr c)).length ≤ L

theorem guardedRow_counter_bound (r c : K) (hrc : r ≠ c) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : BoundedRowOuterInv c C L s) :
    ((guardedRowEval r c C s).stk (.inr c)).length ≤ L := by
  cases hf : s.state.2 with
  | false => simpa [guardedRowEval, hf, countdownReset, countdownResetOp, Op.apply] using hs.2
  | true =>
      simpa only [guardedRowEval, hf, ↓reduceIte] using framedNumericRow_counter_bound r c hrc
        (fun k => s.stk (.inr k)) (hs.1.2 hf) s.state.1.1 C L (s.stk (.inl .source)) hs.1.1.2.2.2.2

def boundedRowOuterContract (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L : ℕ) :
    CountdownContract (.inr d : NumericStack K) (guardedRowRoutine r c)
      (guardedRowEval r c C) (BoundedRowOuterInv c C L) (framedNumericRowStepBound L C + 1) where
  peek_closed s hs := ⟨(rowOuterContract r c d hrc hrd hcd C L).peek_closed s hs.1, hs.2⟩
  pop_closed s hs hg := by
    refine ⟨(rowOuterContract r c d hrc hrd hcd C L).pop_closed s hs.1 hg, ?_⟩
    simpa [countdownPop, countdownPopOp, Op.apply, hcd] using hs.2
  body_closed s hs := ⟨guardedRow_invariant r c hrc C L s hs.1, guardedRow_counter_bound r c hrc C L s hs⟩
  reset_closed s hs := ⟨(rowOuterContract r c d hrc hrd hcd C L).reset_closed s hs.1, hs.2⟩
  counter_preserved s hs := (rowOuterContract r c d hrc hrd hcd C L).counter_preserved s hs.1
  body_executes s hs := (rowOuterContract r c d hrc hrd hcd C L).body_executes s hs.1

theorem framedRows_counter_bounds (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (base : K → List Bool) (hc : base c = []) (hd : base d = []) (frame : F)
    (C L : ℕ) (bits : List Bool) (hL : bits.length ≤ L) :
    ((framedRowsResult r c d base frame C bits).stk (.inr c)).length ≤ L ∧
    ((framedRowsResult r c d base frame C bits).stk (.inr d)).length ≤ L := by
  let s := listCountPrefixResult r d base frame (List.replicate C true) (readUnaryFrame bits)
  have hi : BoundedRowOuterInv c C L s := by
    refine ⟨framedRowsPrefix_invariant r c d hrc hcd base hc frame C L bits hL, ?_⟩
    rw [listCountPrefix_extra r d c (Ne.symm hrc) hcd, hc]
    simp
  obtain ⟨n, hn, he, hfinal, hg, hclear⟩ := countdownRoutine_executes (.inr d) (guardedRowRoutine r c)
    (guardedRowEval r c C) (BoundedRowOuterInv c C L) (framedNumericRowStepBound L C + 1)
    (boundedRowOuterContract r c d hrc hrd hcd C L) s hi
  have houter := countdown_counter_le (.inr d : NumericStack K) (guardedRowEval r c C)
    (guardedRow_extra r c d (Ne.symm hrd) (Ne.symm hcd) C) s
  have hprefix := listCountPrefix_counter_bound r d base hd frame (List.replicate C true) bits
  exact ⟨hfinal.2, houter.trans (hprefix.trans hL)⟩

theorem guardedRows_counter_bounds (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : RowsReady c d C L s) :
    ((guardedRowsEval r c d C s).stk (.inr c)).length ≤ L ∧
    ((guardedRowsEval r c d C s).stk (.inr d)).length ≤ L := by
  cases hf : s.state.2 with
  | false => simp [guardedRowsEval, hf, countdownReset, countdownResetOp, Op.apply, hs.2.1, hs.2.2]
  | true => simpa only [guardedRowsEval, hf, ↓reduceIte] using framedRows_counter_bounds r c d hrc hrd hcd
      (fun k => s.stk (.inr k)) hs.2.1 hs.2.2 s.state.1.1 C L (s.stk (.inl .source)) hs.1.2.2.2.2

theorem providedCapPrefix_counter_bounds (p : PrefixPorts K) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : PrefixReady p C D L s) :
    ((providedCapPrefixEval p C D s).stk (.inr p.c)).length ≤ L ∧
    ((providedCapPrefixEval p C D s).stk (.inr p.d)).length ≤ L := by
  have h1 := smallHeader_ready p C D L s hs
  have h2 := smallHeader_ready p C D L (guardedNumericEval p.r C s) h1
  have h3 := largeHeader_ready p C D L (guardedNumericEval p.r C (guardedNumericEval p.r C s)) h2
  exact guardedRows_counter_bounds p.r p.c p.d p.hrc p.hrd p.hcd C L _ h3.1

theorem prefixReturned_mass_bound (p : PrefixPorts K) (C D L R : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : PrefixReturned p C D L s)
    (hc : (s.stk (.inr p.c)).length ≤ L) (hd : (s.stk (.inr p.d)).length ≤ L)
    (hr : (s.stk (.inr p.r)).length ≤ R) :
    cleanupMass (prefixOwned p) s ≤ R + 3 * L + C + D := by
  rcases hs with ⟨⟨⟨hp, hw, hv, hcap, hsrc⟩, hclear⟩, hcache, htemp⟩
  simp only [cleanupMass, prefixOwned, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hp, hw, hv, hcap, hcache, htemp, List.length_nil, List.length_replicate]
  omega

/- Both failed-state counters now have bounds independent of successful
completion. Original all-path cleanup mass is at most record+3L+C+D;
using only success-implies-empty would have left a genuine gap.
-/

end PolytomyReductionModel
