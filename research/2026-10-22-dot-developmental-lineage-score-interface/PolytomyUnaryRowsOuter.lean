/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual second countdown for original internal unary rows. Failed inner
counters may remain nonempty; the invariant requires emptiness only at
successful row boundaries. The outer guard is explicitly re-peeked.
-/
import PolytomyUnaryFramedRow

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def UnaryRowsInv (p : UnaryVisitPorts K) (c : K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) : Prop :=
  UnaryVisitInv p C L s ∧ (s.state.2 = true → s.stk (.inr c) = [])

def guardedUnaryRowRoutine (p : UnaryVisitPorts K) (c : K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd (unaryFramedRowRoutine p c mode bump) (Atom.routine countdownResetOp)

def guardedUnaryRowEval (p : UnaryVisitPorts K) (c : K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C : ℕ) (s : CountdownStore (NumericStack K) F) :=
  if s.state.2 then unaryFramedRowEval p c mode bump C s else countdownReset s

theorem guardedUnaryRow_executes (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryRowsInv p c C L s) :
    ∃ n ≤ unaryFramedRowBound C L + 1,
      (guardedUnaryRowRoutine p c mode bump).Executes s (guardedUnaryRowEval p c mode bump C s) n ∧
      UnaryRowsInv p c C L (guardedUnaryRowEval p c mode bump C s) := by
  cases hf : s.state.2 with
  | false =>
      refine ⟨2, by unfold unaryFramedRowBound; omega, ?_, ?_⟩
      · simpa only [guardedUnaryRowRoutine, guardedUnaryRowEval, hf, Bool.false_eq_true, ↓reduceIte] using
          RoutineControl.branch_false Prod.snd (unaryFramedRowRoutine p c mode bump)
            (Atom.routine countdownResetOp) hf (Atom.executes countdownResetOp s)
      · simpa [guardedUnaryRowEval, hf, UnaryRowsInv, UnaryVisitInv, NumericLoopInv,
          countdownReset, countdownResetOp, Op.apply] using hs.1
  | true =>
      obtain ⟨n, hn, he, hi, hg, hz⟩ := unaryFramedRow_executes p c hc mode bump C L s hs.1 (hs.2 hf)
      have hb := RoutineControl.branch_true Prod.snd (unaryFramedRowRoutine p c mode bump)
        (Atom.routine countdownResetOp) hf he
      exact ⟨n + 1, by omega, by simpa [guardedUnaryRowRoutine, guardedUnaryRowEval, hf] using hb,
        by simpa [guardedUnaryRowEval, hf, UnaryRowsInv] using And.intro hi hz⟩

theorem guardedUnaryRow_extra (p : UnaryVisitPorts K) (c k : K) (hc : UnaryVisitOutside p c)
    (hkc : k ≠ c) (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryRowsInv p c C L s) :
    (guardedUnaryRowEval p c mode bump C s).stk (.inr k) = s.stk (.inr k) := by
  cases hf : s.state.2 with
  | false => simp [guardedUnaryRowEval, hf, countdownReset, countdownResetOp, Op.apply]
  | true => simpa only [guardedUnaryRowEval, hf, ↓reduceIte] using
      unaryFramedRow_extra p c k hc hkc mode bump C L s hs.1

theorem guardedUnaryRow_observation (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryRowsInv p c C L s) :
    unaryVisitObservation (guardedUnaryRowEval p c mode bump C s) =
      if s.state.2 then (readFramedList readUnaryFrame (s.stk (.inl .source))).map
        (fun q => (q.2, q.1.foldl (unaryVisitStep mode bump C) s.state.1.1)) else none := by
  cases hf : s.state.2 with
  | false => simp [guardedUnaryRowEval, hf, unaryVisitObservation, countdownReset, countdownResetOp, Op.apply]
  | true => simpa only [guardedUnaryRowEval, hf, ↓reduceIte] using
      unaryFramedRow_observation p c hc mode bump C L s hs.1

def unaryRowsOuterContract (p : UnaryVisitPorts K) (c d : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hcd : c ≠ d)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ) :
    CountdownContract (.inr d) (guardedUnaryRowRoutine p c mode bump)
      (guardedUnaryRowEval p c mode bump C) (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 1) where
  peek_closed s hs := by
    simpa only [UnaryRowsInv, UnaryVisitInv, NumericLoopInv, countdownPeek, countdownPeekOp, Op.apply] using hs
  pop_closed s hs hg := by
    rcases hd with ⟨hdm, hdt, hdl, hdr⟩
    simpa [UnaryRowsInv, UnaryVisitInv, NumericLoopInv, countdownPop, countdownPopOp, Op.apply,
      Ne.symm hdm, Ne.symm hdt, Ne.symm hdl, Ne.symm hdr, hcd] using hs
  body_closed s hs := by
    obtain ⟨n, hn, he, hi⟩ := guardedUnaryRow_executes p c hc mode bump C L s hs
    exact hi
  reset_closed s hs := by
    simpa only [UnaryRowsInv, UnaryVisitInv, NumericLoopInv, countdownReset, countdownResetOp, Op.apply] using hs
  counter_preserved s hs := guardedUnaryRow_extra p c d hc (Ne.symm hcd) mode bump C L s hs
  body_executes s hs := by
    obtain ⟨n, hn, he, hi⟩ := guardedUnaryRow_executes p c hc mode bump C L s hs
    exact ⟨n, hn, he⟩

def unaryRowsOuterRoutine (p : UnaryVisitPorts K) (c d : K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  countdownRoutine (.inr d) (guardedUnaryRowRoutine p c mode bump)

def unaryRowsOuterEval (p : UnaryVisitPorts K) (c d : K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C : ℕ) (s : CountdownStore (NumericStack K) F) :=
  countdownEval (.inr d) (guardedUnaryRowEval p c mode bump C) s

theorem unaryRowsOuter_executes (p : UnaryVisitPorts K) (c d : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hcd : c ≠ d)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryRowsInv p c C L s) :
    ∃ n ≤ (s.stk (.inr d)).length * (unaryFramedRowBound C L + 4) + 3,
      (unaryRowsOuterRoutine p c d mode bump).Executes s (unaryRowsOuterEval p c d mode bump C s) n ∧
      UnaryRowsInv p c C L (unaryRowsOuterEval p c d mode bump C s) ∧
      (unaryRowsOuterEval p c d mode bump C s).state.1.2 = false ∧
      ((unaryRowsOuterEval p c d mode bump C s).state.2 = true →
        (unaryRowsOuterEval p c d mode bump C s).stk (.inr d) = []) := by
  simpa only [Nat.add_assoc] using countdownRoutine_executes (.inr d)
    (guardedUnaryRowRoutine p c mode bump) (guardedUnaryRowEval p c mode bump C)
    (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 1)
    (unaryRowsOuterContract p c d hc hd hcd mode bump C L) s hs

theorem unaryRowsOuter_observation (p : UnaryVisitPorts K) (c d : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hcd : c ≠ d)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryRowsInv p c C L s) :
    unaryVisitObservation (unaryRowsOuterEval p c d mode bump C s) =
      if s.state.2 then
        (readMany (readFramedList readUnaryFrame) (s.stk (.inr d)).length (s.stk (.inl .source))).map
          (fun q => (q.2, q.1.foldl (fun acc row => row.foldl (unaryVisitStep mode bump C) acc) s.state.1.1))
      else none := by
  exact observedCountdown d (guardedUnaryRowRoutine p c mode bump)
    (guardedUnaryRowEval p c mode bump C) (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 1)
    (unaryRowsOuterContract p c d hc hd hcd mode bump C L) (readFramedList readUnaryFrame)
    (fun acc row => row.foldl (unaryVisitStep mode bump C) acc)
    (guardedUnaryRow_observation p c hc mode bump C L) s hs

theorem unaryRowsOuter_extra (p : UnaryVisitPorts K) (c d k : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hcd : c ≠ d)
    (hkc : k ≠ c) (hkd : k ≠ d) (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryRowsInv p c C L s) :
    (unaryRowsOuterEval p c d mode bump C s).stk (.inr k) = s.stk (.inr k) := by
  exact countdownLoop_preserves_on (.inr d) (guardedUnaryRowRoutine p c mode bump)
    (guardedUnaryRowEval p c mode bump C) (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 1)
    (unaryRowsOuterContract p c d hc hd hcd mode bump C L) (fun t => t.stk (.inr k))
    (fun _ => rfl) (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hkd])
    (fun t ht => guardedUnaryRow_extra p c k hc hkc mode bump C L t ht)
    (s.stk (.inr d)).length (countdownPeek (.inr d) s)
    ((unaryRowsOuterContract p c d hc hd hcd mode bump C L).peek_closed s hs)

end PolytomyReductionModel
