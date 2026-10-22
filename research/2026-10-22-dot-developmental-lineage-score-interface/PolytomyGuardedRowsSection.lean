/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Failure-absorbing wrapper for the COMPLETE original nested rows section.
Both physical counters start empty; both need only be empty on success
after return. This prevents a later rows attempt from reviving failure.
-/
import PolytomyCapSwitchedHeader

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def RowsReady (c d : K) (C L : ℕ) (s : CountdownStore (NumericStack K) F) : Prop :=
  NumericLoopInv C L s ∧ s.stk (.inr c) = [] ∧ s.stk (.inr d) = []

def RowsReturned (c d : K) (C L : ℕ) (s : CountdownStore (NumericStack K) F) : Prop :=
  NumericLoopInv C L s ∧ (s.state.2 = true → s.stk (.inr c) = [] ∧ s.stk (.inr d) = [])

def guardedRowsRoutine (r c d : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd (framedRowsRoutine r c d) (Atom.routine countdownResetOp)

def guardedRowsEval (r c d : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  if s.state.2 then framedRowsResult r c d (fun k => s.stk (.inr k)) s.state.1.1 C
    (s.stk (.inl .source)) else countdownReset s

theorem guardedRows_executes (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : RowsReady c d C L s) :
    ∃ n ≤ framedRowsStepBound L C + 1,
      (guardedRowsRoutine r c d).Executes s (guardedRowsEval r c d C s) n ∧
      RowsReturned c d C L (guardedRowsEval r c d C s) := by
  cases hf : s.state.2 with
  | false =>
      refine ⟨2, ?_, ?_, ?_⟩
      · unfold framedRowsStepBound; omega
      · have he := RoutineControl.branch_false Prod.snd (framedRowsRoutine r c d)
          (Atom.routine countdownResetOp) hf (Atom.executes countdownResetOp s)
        simpa only [guardedRowsRoutine, guardedRowsEval, hf, Bool.false_eq_true, ↓reduceIte] using he
      · simpa [guardedRowsEval, hf, RowsReturned, NumericLoopInv,
          countdownReset, countdownResetOp, Op.apply] using hs.1
  | true =>
      obtain ⟨n, hn, he, hi, hg, hd⟩ := framedRows_executes r c d hrc hrd hcd
        (fun k => s.stk (.inr k)) hs.2.1 hs.2.2 s.state.1.1 s.state.1.2 s.state.2 C L
        (s.stk (.inl .source)) hs.1.2.2.2.2
      rw [← numericLoop_reconstruct C L s hs.1] at he
      have hall := RoutineControl.branch_true Prod.snd (framedRowsRoutine r c d)
        (Atom.routine countdownResetOp) hf he
      refine ⟨n + 1, by omega, ?_, ?_⟩
      · simpa only [guardedRowsRoutine, guardedRowsEval, hf, ↓reduceIte] using hall
      · simp only [guardedRowsEval, hf, ↓reduceIte, RowsReturned]
        exact ⟨hi.1, fun hok => ⟨hi.2 hok, hd hok⟩⟩

theorem guardedRows_extra (r c d k : K) (hkr : k ≠ r) (hkc : k ≠ c) (hkd : k ≠ d)
    (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (guardedRowsEval r c d C s).stk (.inr k) = s.stk (.inr k) := by
  cases hf : s.state.2 with
  | false => simp [guardedRowsEval, hf, countdownReset, countdownResetOp, Op.apply]
  | true => simpa only [guardedRowsEval, hf, ↓reduceIte] using
      framedRows_extra r c d k hkr hkc hkd (fun j => s.stk (.inr j)) s.state.1.1 C
        (s.stk (.inl .source))

theorem guardedRows_frame (r c d : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (guardedRowsEval r c d C s).state.1.1 = s.state.1.1 := by
  cases hf : s.state.2 with
  | false => simp [guardedRowsEval, hf, countdownReset, countdownResetOp, Op.apply]
  | true => simpa only [guardedRowsEval, hf, ↓reduceIte] using
      framedRows_frame r c d (fun j => s.stk (.inr j)) s.state.1.1 C (s.stk (.inl .source))

theorem guardedRows_observation (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (guardedRowsEval r c d C s) =
      if s.state.2 then
        (readFramedList (readFramedList (readSaturatedBinaryNatFrame C)) (s.stk (.inl .source))).map
          (fun p => (p.2, (encodeFramedList (encodeFramedList unaryFrame) p.1).reverse ++ s.stk (.inr r)))
      else none := by
  cases hf : s.state.2 with
  | false => simp [guardedRowsEval, hf, numericObservation_reset, numericListObservation]
  | true => simpa only [guardedRowsEval, hf, ↓reduceIte] using
      framedRows_observation r c d hrc hrd hcd (fun j => s.stk (.inr j)) s.state.1.1 C
        (s.stk (.inl .source))

theorem guardedRows_record_bound (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : RowsReady c d C L s) :
    ((guardedRowsEval r c d C s).stk (.inr r)).length ≤
      (s.stk (.inr r)).length + L ^ 2 * (C + 2) + 2 * L + 1 := by
  cases hf : s.state.2 with
  | false => simp [guardedRowsEval, hf, countdownReset, countdownResetOp, Op.apply]
  | true => simpa only [guardedRowsEval, hf, ↓reduceIte] using
      framedRows_record_bound r c d hrc hrd hcd (fun j => s.stk (.inr j)) hs.2.1 hs.2.2
        s.state.1.1 C L (s.stk (.inl .source)) hs.1.2.2.2.2

end PolytomyReductionModel
