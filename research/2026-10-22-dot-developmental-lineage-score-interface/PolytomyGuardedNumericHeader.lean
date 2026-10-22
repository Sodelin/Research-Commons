/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Failure-absorbing wrapper for one ORIGINAL capped numeric header attempt.
It uses the existing actual numeric reader/emitter, preserves outside
stacks and physically stored cap, and does not restart a failed prefix.
-/
import PolytomyPhysicalCapExchange

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def guardedNumericRoutine (r c : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd (numericRecordRoutine r c) (Atom.routine countdownResetOp)

def guardedNumericEval (r : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  if s.state.2 then numericRecordEval r C s else countdownReset s

theorem guardedNumeric_executes (r c : K) (hrc : r ≠ c) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s) :
    ∃ n ≤ numericRecordStepBound L C + 1,
      (guardedNumericRoutine r c).Executes s (guardedNumericEval r C s) n ∧
      NumericLoopInv C L (guardedNumericEval r C s) := by
  cases hflag : s.state.2 with
  | false =>
      refine ⟨2, ?_, ?_, ?_⟩
      · unfold numericRecordStepBound; omega
      · have he := RoutineControl.branch_false Prod.snd (numericRecordRoutine r c)
          (Atom.routine countdownResetOp) hflag (Atom.executes countdownResetOp s)
        simpa only [guardedNumericRoutine, guardedNumericEval, hflag, Bool.false_eq_true, ↓reduceIte] using he
      · simpa only [guardedNumericEval, hflag, Bool.false_eq_true, ↓reduceIte,
          NumericLoopInv, countdownReset, countdownResetOp, Op.apply] using hs
  | true =>
      obtain ⟨n, hn, he⟩ := numericRecord_executes r c hrc C (s.stk (.inl .source))
        (fun k => s.stk (.inr k)) s.state.1.1 s.state.1.2 s.state.2
      have hm := numericRecordStepBound_mono (s.stk (.inl .source)).length L C hs.2.2.2.2
      rw [← numericLoop_reconstruct C L s hs] at he
      have hall := RoutineControl.branch_true Prod.snd (numericRecordRoutine r c)
        (Atom.routine countdownResetOp) hflag he
      refine ⟨n + 1, by omega, ?_, ?_⟩
      · simpa only [guardedNumericRoutine, guardedNumericEval, hflag, ↓reduceIte,
          numericRecordEval] using hall
      · simpa only [guardedNumericEval, hflag, ↓reduceIte] using
          numericRecordEval_invariant r C L s hs

theorem guardedNumeric_extra (r k : K) (hkr : k ≠ r) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    (guardedNumericEval r C s).stk (.inr k) = s.stk (.inr k) := by
  cases hflag : s.state.2 with
  | false => simp [guardedNumericEval, hflag, countdownReset, countdownResetOp, Op.apply]
  | true => simpa only [guardedNumericEval, hflag, ↓reduceIte] using numericRecordEval_extra r k hkr C s

theorem guardedNumeric_frame (r : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (guardedNumericEval r C s).state.1.1 = s.state.1.1 := by
  cases hflag : s.state.2 with
  | false => simp [guardedNumericEval, hflag, countdownReset, countdownResetOp, Op.apply]
  | true => simpa only [guardedNumericEval, hflag, ↓reduceIte] using numericRecordEval_frame r C s

theorem guardedNumeric_failed (r : K) (C : ℕ) (s : CountdownStore (NumericStack K) F)
    (hf : s.state.2 = false) : guardedNumericEval r C s = countdownReset s := by
  simp [guardedNumericEval, hf]

theorem guardedNumeric_observation (r : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (guardedNumericEval r C s) =
      if s.state.2 then
        (readSaturatedBinaryNatFrame C (s.stk (.inl .source))).map
          (fun p => (p.2, (unaryFrame p.1).reverse ++ s.stk (.inr r)))
      else none := by
  cases hflag : s.state.2 with
  | false => simp [guardedNumericEval, hflag, numericObservation_reset, numericListObservation]
  | true =>
      cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
      | none => simp [guardedNumericEval, hflag, numericRecordEval, hp, numericRecordResult,
          numericListObservation, numericStore, numericStacks]
      | some p =>
          rcases p with ⟨a, rest⟩
          simp [guardedNumericEval, hflag, numericRecordEval, hp, numericRecordResult,
            numericListObservation, numericStore, numericStacks]

theorem guardedNumeric_record_bound (r : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    ((guardedNumericEval r C s).stk (.inr r)).length ≤ (s.stk (.inr r)).length + C + 1 := by
  cases hflag : s.state.2 with
  | false => simp [guardedNumericEval, hflag, countdownReset, countdownResetOp, Op.apply]
  | true =>
      simpa only [guardedNumericEval, hflag, ↓reduceIte, Nat.add_assoc] using
        numericRecordEval_record_length r C s

/- Each header wrapper now absorbs a failed prefix instead of silently
starting a new attempt. The supplied cap remains a physical operand, with
all outside extra stacks available for a large-cap cache and swap scratch.
Actual cap-switched third-header composition, all three headers plus rows,
cap creation, complete-input finish/cleanup and whole end-to-end machine/
hardness/kernel obligations remain open. No runtime or new model.
-/

end PolytomyReductionModel
