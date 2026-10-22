/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual destructive declared-count equality check for the original first
validation pass. Earlier syntax failure is absorbed. On successful entry,
the declared and actual row counts are consumed as needed; only their
equality and existing finite range flag are retained. No copy is omitted
under a false claim that these no-longer-needed operands survive.
-/
import PolytomyCoveragePredicateAndCleanup

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K : Type} [DecidableEq K]

def declaredCountVerdictOp (left : K) : Op K Bool (CountdownState Bool) :=
  .peek left (fun st h => (st.1, st.2 && h.isNone && st.1.1))

def declaredCountSubtractEval (left right : K) (s : CountdownStore K Bool) : CountdownStore K Bool :=
  frameCallerStore left right s.stk s.state.1
    (decide ((s.stk right).length ≤ (s.stk left).length))
    (List.replicate ((s.stk left).length - (s.stk right).length) true) []

def guardedDeclaredCountRoutine (left right : K) : Routine (fun _ : K => Bool) (CountdownState Bool) :=
  RoutineControl.branch Prod.snd
    (RoutineComposition.seq (unarySubtractRoutine left right) (Atom.routine (declaredCountVerdictOp left)))
    (Atom.routine cleanupNoop)

def guardedDeclaredCountEval (left right : K) (s : CountdownStore K Bool) :=
  if s.state.2 then (declaredCountVerdictOp left).apply (declaredCountSubtractEval left right s) else s

theorem guardedDeclaredCount_executes (left right : K) (hne : left ≠ right)
    (s : CountdownStore K Bool)
    (hl : s.state.2 = true → IsUnaryWord (s.stk left))
    (hr : s.state.2 = true → IsUnaryWord (s.stk right)) :
    ∃ n ≤ (s.stk right).length + 3,
      (guardedDeclaredCountRoutine left right).Executes s (guardedDeclaredCountEval left right s) n := by
  cases hf : s.state.2 with
  | false =>
      have h := RoutineControl.branch_false Prod.snd
        (RoutineComposition.seq (unarySubtractRoutine left right) (Atom.routine (declaredCountVerdictOp left)))
        (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop s)
      exact ⟨2, by omega, by simpa [guardedDeclaredCountRoutine, guardedDeclaredCountEval, hf, cleanupNoop, Op.apply] using h⟩
  | true =>
      have h1 := unarySubtract_executes left right hne s.stk s.state.1 s.state.2
        (s.stk left).length (s.stk right).length
      have hentry : frameCallerStore left right s.stk s.state.1 s.state.2
          (List.replicate (s.stk left).length true) (List.replicate (s.stk right).length true) = s := by
        rw [← hl hf, ← hr hf, frameCallerStore_self]
      rw [hentry] at h1
      have h2 := Atom.executes (declaredCountVerdictOp left) (declaredCountSubtractEval left right s)
      have hseq := RoutineComposition.seq_executes (unarySubtractRoutine left right)
        (Atom.routine (declaredCountVerdictOp left)) h1 h2
      have hall := RoutineControl.branch_true Prod.snd
        (RoutineComposition.seq (unarySubtractRoutine left right) (Atom.routine (declaredCountVerdictOp left)))
        (Atom.routine cleanupNoop) hf hseq
      exact ⟨((s.stk right).length + 1) + 1 + 1, by omega,
        by simpa [guardedDeclaredCountRoutine, guardedDeclaredCountEval, hf] using hall⟩

theorem guardedDeclaredCount_verdict (left right : K) (hne : left ≠ right) (s : CountdownStore K Bool) :
    (guardedDeclaredCountEval left right s).state.2 =
      s.state.2 && s.state.1.1 && decide ((s.stk left).length = (s.stk right).length) := by
  cases hf : s.state.2 with
  | false => simp [guardedDeclaredCountEval, hf]
  | true =>
      have he := unaryVisit_test_residual .equal (s.stk left).length (s.stk right).length
      simp only [unaryVisitTest] at he
      simp only [guardedDeclaredCountEval, hf, ↓reduceIte, declaredCountVerdictOp,
        declaredCountSubtractEval, Op.apply, frameCallerStore, Function.update_of_ne hne,
        Function.update_same]
      rw [he]
      cases s.state.1.1 <;> by_cases h : (s.stk left).length = (s.stk right).length <;>
        simp_all [eq_comm]

theorem guardedDeclaredCount_extra (left right k : K) (hkl : k ≠ left) (hkr : k ≠ right)
    (s : CountdownStore K Bool) : (guardedDeclaredCountEval left right s).stk k = s.stk k := by
  cases hf : s.state.2 <;>
    simp [guardedDeclaredCountEval, hf, declaredCountVerdictOp, declaredCountSubtractEval,
      Op.apply, frameCallerStore, hkl, hkr]

theorem guardedDeclaredCount_lengths (left right : K) (hne : left ≠ right) (s : CountdownStore K Bool) :
    ((guardedDeclaredCountEval left right s).stk left).length ≤ (s.stk left).length ∧
      ((guardedDeclaredCountEval left right s).stk right).length ≤ (s.stk right).length := by
  cases hf : s.state.2 with
  | false => simp [guardedDeclaredCountEval, hf]
  | true =>
      simp [guardedDeclaredCountEval, hf, declaredCountVerdictOp, declaredCountSubtractEval,
        Op.apply, frameCallerStore, hne, Nat.sub_le]

/- Concrete first-pass operands will be headerM and savedCount. Exact
complete-record syntax supplies their true-only words on the successful
branch. Underflow/equality/overflow and earlier parse failure are all
included. Query-count creation and the full first-pass composition remain
to be joined before claiming the original validator routine.
-/

end PolytomyReductionModel
