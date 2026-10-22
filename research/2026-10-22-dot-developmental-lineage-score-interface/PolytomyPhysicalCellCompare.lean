/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Generic finite-port, operand-preserving unary <=, =, and < comparisons.
Every copy, subtraction, residual observation and cleanup is charged.
The guarded form preserves a previous parse/range failure, on all data.
-/
import PolytomyPhysicalSuffixReplay

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive CellComparePort where
  | left | right | temp | residue | subtrahend
  deriving DecidableEq, Fintype

inductive CellCompareMode where
  | le | eq | lt
  deriving DecidableEq, Fintype

abbrev CellComparePorts (K : Type) := CellComparePort ↪ K

variable {K F : Type} [DecidableEq K]

@[simp] theorem cellComparePorts_eq (p : CellComparePorts K) (a b : CellComparePort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def cellCompareAnswer : CellCompareMode → ℕ → ℕ → Bool
  | .le, C, D => decide (D ≤ C)
  | .eq, C, D => decide (D = C)
  | .lt, C, D => decide (D < C)

def cellCompareHead : CellCompareMode → Bool → Option Bool → Bool
  | .le, flag, _ => flag
  | .eq, flag, head => flag && !head.isSome
  | .lt, _, head => head.isSome

theorem cellCompareHead_residue (mode : CellCompareMode) (C D : ℕ) :
    cellCompareHead mode (decide (D ≤ C)) ((List.replicate (C - D) true).head?) =
      cellCompareAnswer mode C D := by
  cases hz : C - D with
  | zero =>
      have hlt : ¬ D < C := by omega
      have heq : (D ≤ C) ↔ D = C := by omega
      cases mode <;> simp [cellCompareHead, cellCompareAnswer, hz, hlt, heq]
  | succ n =>
      have hlt : D < C := by omega
      have hle : D ≤ C := by omega
      have hne : D ≠ C := by omega
      cases mode <;> simp [cellCompareHead, cellCompareAnswer, hz, List.replicate_succ, hlt, hle, hne]

def cellCompareFlagStore (flag : Bool) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨(s.state.1, flag), s.stk⟩

def cellCompareFirst (p : CellComparePorts K) (s : CountdownStore K F) :=
  wordDuplicateEval (p .left) (p .residue) s

def cellComparePrepared (p : CellComparePorts K) (s : CountdownStore K F) :=
  wordDuplicateEval (p .right) (p .subtrahend) (cellCompareFirst p s)

def cellCompareSubtracted (p : CellComparePorts K) (C D : ℕ) (s : CountdownStore K F) :=
  frameCallerStore (p .residue) (p .subtrahend)
    (cellComparePrepared p s).stk (cellComparePrepared p s).state.1 (decide (D ≤ C))
    (List.replicate (C - D) true) []

def cellCompareTestOp (p : CellComparePorts K) (mode : CellCompareMode) : Op K Bool (CountdownState F) :=
  .peek (p .residue) (fun st head => (st.1, cellCompareHead mode st.2 head))

def cellCompareTested (p : CellComparePorts K) (mode : CellCompareMode) (C D : ℕ)
    (s : CountdownStore K F) :=
  (cellCompareTestOp p mode).apply (cellCompareSubtracted p C D s)

def cellCompareEval (p : CellComparePorts K) (mode : CellCompareMode) (C D : ℕ)
    (s : CountdownStore K F) := clearStackEval (p .residue) (cellCompareTested p mode C D s)

def cellCompareRoutine (p : CellComparePorts K) (mode : CellCompareMode) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (p .left) (p .temp) (p .residue))
    (RoutineComposition.seq (wordDuplicateRoutine (p .right) (p .temp) (p .subtrahend))
      (RoutineComposition.seq (unarySubtractRoutine (p .residue) (p .subtrahend))
        (RoutineComposition.seq (Atom.routine (cellCompareTestOp p mode)) (clearStackRoutine (p .residue)))))

theorem cellCompare_result (p : CellComparePorts K) (mode : CellCompareMode) (C D : ℕ)
    (s : CountdownStore K F) (hl : s.stk (p .residue) = []) (hr : s.stk (p .subtrahend) = []) :
    cellCompareEval p mode C D s = cellCompareFlagStore (cellCompareAnswer mode C D) s := by
  apply countdownStore_ext
  · simpa [cellCompareEval, clearStackEval, cellCompareTested, cellCompareTestOp, Op.apply,
      cellCompareSubtracted, frameCallerStore, cellComparePrepared, cellCompareFirst,
      wordDuplicateEval, cellCompareFlagStore] using
      congrArg (fun flag => (s.state.1, flag)) (cellCompareHead_residue mode C D)
  · funext k
    by_cases hkl : k = p .residue
    · subst k; simp [cellCompareEval, clearStackEval, cellCompareFlagStore, hl]
    by_cases hkr : k = p .subtrahend
    · subst k
      simp [cellCompareEval, clearStackEval, cellCompareTested, cellCompareTestOp, Op.apply,
        cellCompareSubtracted, frameCallerStore, cellCompareFlagStore, hr]
    · simp [cellCompareEval, clearStackEval, cellCompareTested, cellCompareTestOp, Op.apply,
        cellCompareSubtracted, frameCallerStore, cellComparePrepared, cellCompareFirst,
        wordDuplicateEval, cellCompareFlagStore, hkl, hkr]

theorem cellCompare_executes (p : CellComparePorts K) (mode : CellCompareMode) (C D : ℕ)
    (s : CountdownStore K F) (hC : s.stk (p .left) = List.replicate C true)
    (hD : s.stk (p .right) = List.replicate D true) (hl : s.stk (p .residue) = [])
    (hr : s.stk (p .subtrahend) = []) (ht : s.stk (p .temp) = []) :
    ∃ n ≤ 4 * C + 4 * D + 9,
      (cellCompareRoutine p mode).Executes s (cellCompareFlagStore (cellCompareAnswer mode C D) s) n := by
  have h1 := wordDuplicate_executes (p .left) (p .temp) (p .residue)
    (by simp) (by simp) (by simp) s ht
  have ht1 : (cellCompareFirst p s).stk (p .temp) = [] := by
    simp [cellCompareFirst, wordDuplicateEval, ht]
  have h2 := wordDuplicate_executes (p .right) (p .temp) (p .subtrahend)
    (by simp) (by simp) (by simp) (cellCompareFirst p s) ht1
  have hD1 : (cellCompareFirst p s).stk (p .right) = List.replicate D true := by
    simp [cellCompareFirst, wordDuplicateEval, hD]
  rw [hC, List.length_replicate] at h1
  rw [hD1, List.length_replicate] at h2
  have hleft : (cellComparePrepared p s).stk (p .residue) = List.replicate C true := by
    simp [cellComparePrepared, cellCompareFirst, wordDuplicateEval, hC, hl]
  have hright : (cellComparePrepared p s).stk (p .subtrahend) = List.replicate D true := by
    simp [cellComparePrepared, cellCompareFirst, wordDuplicateEval, hD, hr]
  have hsub := unarySubtract_executes (p .residue) (p .subtrahend) (by simp)
    (cellComparePrepared p s).stk (cellComparePrepared p s).state.1
    (cellComparePrepared p s).state.2 C D
  have hin : frameCallerStore (p .residue) (p .subtrahend)
      (cellComparePrepared p s).stk (cellComparePrepared p s).state.1 (cellComparePrepared p s).state.2
      (List.replicate C true) (List.replicate D true) = cellComparePrepared p s := by
    rw [← hleft, ← hright, frameCallerStore_self]
  rw [hin] at hsub
  have hp := Atom.executes (cellCompareTestOp p mode) (cellCompareSubtracted p C D s)
  have hc := clearStack_executes (p .residue) (cellCompareTested p mode C D s)
  have hlen : ((cellCompareTested p mode C D s).stk (p .residue)).length = C - D := by
    simp [cellCompareTested, cellCompareTestOp, Op.apply, cellCompareSubtracted, frameCallerStore]
  rw [hlen] at hc
  have hall := RoutineComposition.seq_executes _ _ h1
    (RoutineComposition.seq_executes _ _ h2 (RoutineComposition.seq_executes _ _ hsub
      (RoutineComposition.seq_executes _ _ hp hc)))
  change (cellCompareRoutine p mode).Executes s (cellCompareEval p mode C D s)
    ((3 * C + 3) + ((3 * D + 3) + ((D + 1) + (1 + (C - D + 1))))) at hall
  rw [cellCompare_result p mode C D s hl hr] at hall
  exact ⟨_, by omega, hall⟩

def guardedCellCompareRoutine (p : CellComparePorts K) (mode : CellCompareMode) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd (cellCompareRoutine p mode) (Atom.routine cleanupNoop)

def guardedCellCompareEval (mode : CellCompareMode) (C D : ℕ)
    (s : CountdownStore K F) : CountdownStore K F :=
  if s.state.2 then cellCompareFlagStore (cellCompareAnswer mode C D) s else s

theorem guardedCellCompare_executes (p : CellComparePorts K) (mode : CellCompareMode) (C D : ℕ)
    (s : CountdownStore K F) (hC : s.stk (p .left) = List.replicate C true)
    (hD : s.stk (p .right) = List.replicate D true) (hl : s.stk (p .residue) = [])
    (hr : s.stk (p .subtrahend) = []) (ht : s.stk (p .temp) = []) :
    ∃ n ≤ 4 * C + 4 * D + 10,
      (guardedCellCompareRoutine p mode).Executes s (guardedCellCompareEval mode C D s) n := by
  cases hf : s.state.2 with
  | false =>
      have h := RoutineControl.branch_false Prod.snd (cellCompareRoutine p mode)
        (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop s)
      refine ⟨2, by omega, ?_⟩
      simpa [guardedCellCompareRoutine, guardedCellCompareEval, hf, cleanupNoop, Op.apply] using h
  | true =>
      obtain ⟨n, hn, he⟩ := cellCompare_executes p mode C D s hC hD hl hr ht
      have h := RoutineControl.branch_true Prod.snd (cellCompareRoutine p mode) (Atom.routine cleanupNoop) hf he
      refine ⟨n + 1, by omega, ?_⟩
      simpa [guardedCellCompareRoutine, guardedCellCompareEval, hf] using h

theorem guardedCellCompare_stacks (mode : CellCompareMode) (C D : ℕ) (s : CountdownStore K F) :
    (guardedCellCompareEval mode C D s).stk = s.stk := by
  cases hf : s.state.2 <;> simp [guardedCellCompareEval, cellCompareFlagStore, hf]

theorem guardedCellCompare_frame (mode : CellCompareMode) (C D : ℕ) (s : CountdownStore K F) :
    (guardedCellCompareEval mode C D s).state.1 = s.state.1 := by
  cases hf : s.state.2 <;> simp [guardedCellCompareEval, cellCompareFlagStore, hf]

theorem guardedCellCompare_flag (mode : CellCompareMode) (C D : ℕ) (s : CountdownStore K F) :
    (guardedCellCompareEval mode C D s).state.2 = s.state.2 && cellCompareAnswer mode C D := by
  cases hf : s.state.2 <;> simp [guardedCellCompareEval, cellCompareFlagStore, hf]

/- Generic F is a preserved caller frame, not a finite-state realization
   claim for arbitrary F. The complete verifier must instantiate finite F
   and K, compose actual scans and cleanup, and retain all malformed cases.
-/

end PolytomyReductionModel
