/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual counted identifier visits, with the previous actual body contract
discharged and exact original readMany/fold observation. This is not an
oracle for either the row-count prefix or a whole record.
-/
import PolytomyObservedCountdownFold

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def UnaryVisitOutside (p : UnaryVisitPorts K) (k : K) : Prop :=
  k ≠ p.m ∧ k ≠ p.t ∧ k ≠ p.l ∧ k ≠ p.r

def unaryVisitStep (mode : UnaryVisitMode) (bump : F → Bool → F) (C : ℕ) : F → ℕ → F :=
  fun acc a => bump acc (unaryVisitTest mode C a)

def unaryIdentifierContract (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ) :
    CountdownContract (.inr c) (unaryIdentifierRoutine p mode bump)
      (unaryIdentifierEval p mode bump C) (UnaryVisitInv p C L) (7 * C + 10 * L + 22) where
  peek_closed s hs := by
    simpa only [UnaryVisitInv, NumericLoopInv, countdownPeek, countdownPeekOp, Op.apply] using hs
  pop_closed s hs hg := by
    rcases hc with ⟨hcm, hct, hcl, hcr⟩
    simpa [UnaryVisitInv, NumericLoopInv, countdownPop, countdownPopOp, Op.apply,
      Ne.symm hcm, Ne.symm hct, Ne.symm hcl, Ne.symm hcr] using hs
  body_closed s hs := unaryIdentifier_invariant p mode bump C L s hs
  reset_closed s hs := by
    simpa only [UnaryVisitInv, NumericLoopInv, countdownReset, countdownResetOp, Op.apply] using hs
  counter_preserved s hs := unaryIdentifier_extra p mode bump C L s hs c
  body_executes s hs := unaryIdentifier_executes p mode bump C L s hs

def unaryIdentifierListRoutine (p : UnaryVisitPorts K) (c : K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  countdownRoutine (.inr c) (unaryIdentifierRoutine p mode bump)

def unaryIdentifierListEval (p : UnaryVisitPorts K) (c : K) (mode : UnaryVisitMode)
    (bump : F → Bool → F) (C : ℕ) (s : CountdownStore (NumericStack K) F) :=
  countdownEval (.inr c) (unaryIdentifierEval p mode bump C) s

theorem unaryIdentifierList_executes (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv p C L s) :
    ∃ n ≤ (s.stk (.inr c)).length * (7 * C + 10 * L + 25) + 3,
      (unaryIdentifierListRoutine p c mode bump).Executes s (unaryIdentifierListEval p c mode bump C s) n ∧
      UnaryVisitInv p C L (unaryIdentifierListEval p c mode bump C s) ∧
      (unaryIdentifierListEval p c mode bump C s).state.1.2 = false ∧
      ((unaryIdentifierListEval p c mode bump C s).state.2 = true →
        (unaryIdentifierListEval p c mode bump C s).stk (.inr c) = []) := by
  simpa only [Nat.add_assoc] using countdownRoutine_executes (.inr c)
    (unaryIdentifierRoutine p mode bump) (unaryIdentifierEval p mode bump C) (UnaryVisitInv p C L)
    (7 * C + 10 * L + 22) (unaryIdentifierContract p c hc mode bump C L) s hs

theorem unaryIdentifierList_observation (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv p C L s) :
    unaryVisitObservation (unaryIdentifierListEval p c mode bump C s) =
      if s.state.2 then (readMany readUnaryFrame (s.stk (.inr c)).length (s.stk (.inl .source))).map
        (fun q => (q.2, q.1.foldl (unaryVisitStep mode bump C) s.state.1.1)) else none := by
  exact observedCountdown c (unaryIdentifierRoutine p mode bump) (unaryIdentifierEval p mode bump C)
    (UnaryVisitInv p C L) (7 * C + 10 * L + 22) (unaryIdentifierContract p c hc mode bump C L)
    readUnaryFrame (unaryVisitStep mode bump C) (unaryIdentifier_observation p mode bump C L) s hs

theorem unaryIdentifierList_extra (p : UnaryVisitPorts K) (c k : K) (hc : UnaryVisitOutside p c)
    (hkc : k ≠ c) (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv p C L s) :
    (unaryIdentifierListEval p c mode bump C s).stk (.inr k) = s.stk (.inr k) := by
  exact countdownLoop_preserves_on (.inr c) (unaryIdentifierRoutine p mode bump)
    (unaryIdentifierEval p mode bump C) (UnaryVisitInv p C L) (7 * C + 10 * L + 22)
    (unaryIdentifierContract p c hc mode bump C L) (fun t => t.stk (.inr k))
    (fun _ => rfl) (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hkc])
    (fun t ht => unaryIdentifier_extra p mode bump C L t ht k) (s.stk (.inr c)).length
    (countdownPeek (.inr c) s) ((unaryIdentifierContract p c hc mode bump C L).peek_closed s hs)

theorem unaryField_visit_invariant (p : UnaryVisitPorts K) (c : K) (hc : UnaryVisitOutside p c)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv p C L s) :
    UnaryVisitInv p C L (guardedUnaryFieldEval (.inl .source) (.inr c) s) := by
  refine ⟨unaryField_numeric_invariant c C L s hs.1, ?_, ?_, ?_, ?_⟩
  · rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using Ne.symm hc.1)]; exact hs.2.1
  · rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using Ne.symm hc.2.1)]; exact hs.2.2.1
  · rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using Ne.symm hc.2.2.1)]; exact hs.2.2.2.1
  · rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using Ne.symm hc.2.2.2)]; exact hs.2.2.2.2

end PolytomyReductionModel
