/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual failure-absorbing row wrapper and outer physical countdown. Its
invariant requires inner-count emptiness ONLY while success is true.
Distinct outer-counter preservation and partial-record storage are proved.
The outer loop's original grammar observation remains a separate step.
-/
import PolytomyFramedNumericRow

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem countdownLoop_preserves {A : Type} (counter : K)
    (f : CountdownStore K F → CountdownStore K F) (obs : CountdownStore K F → A)
    (hpeek : ∀ s, obs (countdownPeek counter s) = obs s)
    (hpop : ∀ s, obs (countdownPop counter s) = obs s)
    (hf : ∀ s, obs (f s) = obs s) (n : ℕ) (s : CountdownStore K F) :
    obs (countdownLoopEval counter f n s) = obs s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      cases hg : countdownGuard s.state <;>
        simp only [countdownLoopEval, hg, Bool.false_eq_true, Bool.true_eq_true, ↓reduceIte,
          ih, hpeek, hf, hpop]

theorem numericRecordEval_extra (r k : K) (hkr : k ≠ r) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    (numericRecordEval r C s).stk (.inr k) = s.stk (.inr k) := by
  cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
  | none => simp [numericRecordEval, hp, numericRecordResult, numericStore, numericStacks]
  | some p =>
      rcases p with ⟨a, rest⟩
      simp [numericRecordEval, hp, numericRecordResult, numericStore, numericStacks, hkr]

theorem numericRecordEval_frame (r : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (numericRecordEval r C s).state.1.1 = s.state.1.1 := by
  cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) <;>
    simp [numericRecordEval, hp, numericRecordResult, numericStore]

theorem numericList_extra (r c k : K) (hkr : k ≠ r) (hkc : k ≠ c) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    (numericListEval r c C s).stk (.inr k) = s.stk (.inr k) := by
  exact countdownLoop_preserves (.inr c) (numericRecordEval r C) (fun t => t.stk (.inr k))
    (fun _ => rfl)
    (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hkc])
    (numericRecordEval_extra r k hkr C) (s.stk (.inr c)).length (countdownPeek (.inr c) s)

theorem numericList_frame (r c : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (numericListEval r c C s).state.1.1 = s.state.1.1 := by
  exact countdownLoop_preserves (.inr c) (numericRecordEval r C) (fun t => t.state.1.1)
    (fun _ => rfl) (fun _ => rfl) (numericRecordEval_frame r C)
    (s.stk (.inr c)).length (countdownPeek (.inr c) s)

theorem framedNumericRow_extra (r c k : K) (hkr : k ≠ r) (hkc : k ≠ c)
    (base : K → List Bool) (frame : F) (C : ℕ) (bits : List Bool) :
    (framedNumericRowResult r c base frame C bits).stk (.inr k) = base k := by
  unfold framedNumericRowResult
  rw [numericList_extra r c k hkr hkc]
  cases hp : readUnaryFrame bits with
  | none => rfl
  | some p =>
      rcases p with ⟨n, rest⟩
      simp [listCountPrefixResult, hp, numericStore, numericStacks, hkr, hkc]

theorem framedNumericRow_frame (r c : K) (base : K → List Bool) (frame : F)
    (C : ℕ) (bits : List Bool) :
    (framedNumericRowResult r c base frame C bits).state.1.1 = frame := by
  unfold framedNumericRowResult
  rw [numericList_frame]
  cases hp : readUnaryFrame bits <;> simp [listCountPrefixResult, hp, numericStore]

def RowOuterInv (c : K) (C L : ℕ) (s : CountdownStore (NumericStack K) F) : Prop :=
  NumericLoopInv C L s ∧ (s.state.2 = true → s.stk (.inr c) = [])

def guardedRowRoutine (r c : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd (framedNumericRowRoutine r c) (Atom.routine countdownResetOp)

def guardedRowEval (r c : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  if s.state.2 then framedNumericRowResult r c (fun k => s.stk (.inr k)) s.state.1.1 C
    (s.stk (.inl .source))
  else countdownReset s

theorem guardedRow_executes (r c : K) (hrc : r ≠ c) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : RowOuterInv c C L s) :
    ∃ n ≤ framedNumericRowStepBound L C + 1,
      (guardedRowRoutine r c).Executes s (guardedRowEval r c C s) n ∧
      RowOuterInv c C L (guardedRowEval r c C s) := by
  cases hflag : s.state.2 with
  | false =>
      refine ⟨2, ?_, ?_, ?_⟩
      · unfold framedNumericRowStepBound; omega
      · have he := RoutineControl.branch_false Prod.snd (framedNumericRowRoutine r c)
          (Atom.routine countdownResetOp) hflag (Atom.executes countdownResetOp s)
        simpa only [guardedRowRoutine, guardedRowEval, hflag, Bool.false_eq_true, ↓reduceIte] using he
      · simpa [guardedRowEval, hflag, RowOuterInv, NumericLoopInv,
          countdownReset, countdownResetOp, Op.apply] using hs
  | true =>
      have hc := hs.2 hflag
      obtain ⟨n, hn, he, hi, hg, hclear⟩ := framedNumericRow_executes r c hrc
        (fun k => s.stk (.inr k)) hc s.state.1.1 s.state.1.2 s.state.2 C L
        (s.stk (.inl .source)) hs.1.2.2.2.2
      rw [← numericLoop_reconstruct C L s hs.1] at he
      have hall := RoutineControl.branch_true Prod.snd (framedNumericRowRoutine r c)
        (Atom.routine countdownResetOp) hflag he
      refine ⟨n + 1, by omega, ?_, ?_⟩
      · simpa only [guardedRowRoutine, guardedRowEval, hflag, ↓reduceIte] using hall
      · simpa only [guardedRowEval, hflag, ↓reduceIte, RowOuterInv] using And.intro hi hclear

theorem guardedRow_invariant (r c : K) (hrc : r ≠ c) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : RowOuterInv c C L s) :
    RowOuterInv c C L (guardedRowEval r c C s) := by
  obtain ⟨n, hn, he, hi⟩ := guardedRow_executes r c hrc C L s hs
  exact hi

theorem guardedRow_extra (r c k : K) (hkr : k ≠ r) (hkc : k ≠ c) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    (guardedRowEval r c C s).stk (.inr k) = s.stk (.inr k) := by
  cases hflag : s.state.2 with
  | false => simp [guardedRowEval, hflag, countdownReset, countdownResetOp, Op.apply]
  | true =>
      simpa only [guardedRowEval, hflag, ↓reduceIte] using
        framedNumericRow_extra r c k hkr hkc (fun j => s.stk (.inr j)) s.state.1.1 C
          (s.stk (.inl .source))

theorem guardedRow_record_bound (r c : K) (hrc : r ≠ c) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : RowOuterInv c C L s) :
    ((guardedRowEval r c C s).stk (.inr r)).length ≤
      (s.stk (.inr r)).length + (L * (C + 2) + 1) := by
  cases hflag : s.state.2 with
  | false => simp [guardedRowEval, hflag, countdownReset, countdownResetOp, Op.apply]
  | true =>
      simpa only [guardedRowEval, hflag, ↓reduceIte, Nat.add_assoc] using
        framedNumericRow_record_bound r c hrc (fun k => s.stk (.inr k)) (hs.2 hflag)
          s.state.1.1 C L (s.stk (.inl .source)) hs.1.2.2.2.2

theorem guardedRow_frame (r c : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (guardedRowEval r c C s).state.1.1 = s.state.1.1 := by
  cases hflag : s.state.2 with
  | false => simp [guardedRowEval, hflag, countdownReset, countdownResetOp, Op.apply]
  | true =>
      simpa only [guardedRowEval, hflag, ↓reduceIte] using
        framedNumericRow_frame r c (fun k => s.stk (.inr k)) s.state.1.1 C
          (s.stk (.inl .source))

def rowOuterContract (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L : ℕ) :
    CountdownContract (.inr d : NumericStack K) (guardedRowRoutine r c)
      (guardedRowEval r c C) (RowOuterInv c C L) (framedNumericRowStepBound L C + 1) where
  peek_closed s hs := by
    simpa only [RowOuterInv, NumericLoopInv, countdownPeek, countdownPeekOp, Op.apply] using hs
  pop_closed s hs hg := by
    simpa [RowOuterInv, NumericLoopInv, countdownPop, countdownPopOp, Op.apply, hcd] using hs
  body_closed s hs := guardedRow_invariant r c hrc C L s hs
  reset_closed s hs := by
    simpa only [RowOuterInv, NumericLoopInv, countdownReset, countdownResetOp, Op.apply] using hs
  counter_preserved s hs := guardedRow_extra r c d (Ne.symm hrd) (Ne.symm hcd) C s
  body_executes s hs := by
    obtain ⟨n, hn, he, hi⟩ := guardedRow_executes r c hrc C L s hs
    exact ⟨n, hn, he⟩

def rowOuterRoutine (r c d : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  countdownRoutine (.inr d) (guardedRowRoutine r c)

def rowOuterEval (r c d : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  countdownEval (.inr d) (guardedRowEval r c C) s

theorem rowOuter_extra (r c d k : K) (hkr : k ≠ r) (hkc : k ≠ c) (hkd : k ≠ d)
    (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (rowOuterEval r c d C s).stk (.inr k) = s.stk (.inr k) := by
  exact countdownLoop_preserves (.inr d) (guardedRowEval r c C) (fun t => t.stk (.inr k))
    (fun _ => rfl) (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hkd])
    (guardedRow_extra r c k hkr hkc C) (s.stk (.inr d)).length (countdownPeek (.inr d) s)

theorem rowOuter_frame (r c d : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (rowOuterEval r c d C s).state.1.1 = s.state.1.1 := by
  exact countdownLoop_preserves (.inr d) (guardedRowEval r c C) (fun t => t.state.1.1)
    (fun _ => rfl) (fun _ => rfl) (guardedRow_frame r c C)
    (s.stk (.inr d)).length (countdownPeek (.inr d) s)

theorem rowOuter_executes (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : RowOuterInv c C L s) :
    ∃ n ≤ (s.stk (.inr d)).length * (framedNumericRowStepBound L C + 4) + 3,
      (rowOuterRoutine r c d).Executes s (rowOuterEval r c d C s) n ∧
      RowOuterInv c C L (rowOuterEval r c d C s) ∧
      (rowOuterEval r c d C s).state.1.2 = false ∧
      ((rowOuterEval r c d C s).state.2 = true →
        (rowOuterEval r c d C s).stk (.inr d) = []) := by
  simpa only [Nat.add_assoc] using countdownRoutine_executes (.inr d) (guardedRowRoutine r c)
    (guardedRowEval r c C) (RowOuterInv c C L) (framedNumericRowStepBound L C + 1)
    (rowOuterContract r c d hrc hrd hcd C L) s hs

theorem rowOuterLoop_record_bound (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L fuel : ℕ) : ∀ s : CountdownStore (NumericStack K) F, RowOuterInv c C L s →
    ((countdownLoopEval (.inr d) (guardedRowEval r c C) fuel s).stk (.inr r)).length ≤
      (s.stk (.inr r)).length + fuel * (L * (C + 2) + 1) := by
  induction fuel with
  | zero => intro s hs; simp [countdownLoopEval]
  | succ fuel ih =>
      intro s hs
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          let hc := rowOuterContract r c d hrc hrd hcd C L
          let p := countdownPop (.inr d) s
          have hp : RowOuterInv c C L p := hc.pop_closed s hs hg
          let u := countdownPeek (.inr d) (guardedRowEval r c C p)
          have hu : RowOuterInv c C L u := hc.peek_closed _ (hc.body_closed p hp)
          have hi := ih u hu
          have hb := guardedRow_record_bound r c hrc C L p hp
          have hpop : p.stk (.inr r) = s.stk (.inr r) := by
            simp [p, countdownPop, countdownPopOp, Op.apply, hrd]
          have hpeek : (u.stk (.inr r)).length = ((guardedRowEval r c C p).stk (.inr r)).length := rfl
          rw [hpop] at hb
          rw [hpeek] at hi
          simp only [countdownLoopEval, hg, ↓reduceIte]
          change ((countdownLoopEval (.inr d) (guardedRowEval r c C) fuel u).stk (.inr r)).length ≤ _
          nlinarith

theorem rowOuter_record_bound (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : RowOuterInv c C L s) :
    ((rowOuterEval r c d C s).stk (.inr r)).length ≤
      (s.stk (.inr r)).length + (s.stk (.inr d)).length * (L * (C + 2) + 1) := by
  exact rowOuterLoop_record_bound r c d hrc hrd hcd C L (s.stk (.inr d)).length
    (countdownPeek (.inr d) s) ((rowOuterContract r c d hrc hrd hcd C L).peek_closed s hs)

/- The outer invariant now includes every failed partial state without
pretending the inner counter was cleared. The guarded row wrapper prevents
new attempts after failure. Both loops may share their cached guard because
the actual outer body is followed by re-peeking; no guard-preservation
premise is used. Exact observation of repeated original rows, outer count
reading/copy, headers/caps, suffix rejection, reversal/tagging and whole
cleanup still remain. Full constructor/checker, closed encoded hardness
and every kernel check remain open. No runtime or broader closure claim.
-/

end PolytomyReductionModel
