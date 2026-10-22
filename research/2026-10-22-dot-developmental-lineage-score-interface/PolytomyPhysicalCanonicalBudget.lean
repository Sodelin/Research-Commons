/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual ORIGINAL budget C0+K-N, using physical C0/K/N words, restoring
copies and saturated subtraction. Underflow semantics is exactly Nat.sub;
an actual final instruction resets success, not a logical ignored flag.
-/
import PolytomyBinaryCounterCaller

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def canonicalBudget1 (s : CanonicalGlobalStore) :=
  wordDuplicateEval (globalFilterPort .cost) (globalFilterPort .typeIndex) s

def canonicalBudget2 (s : CanonicalGlobalStore) :=
  wordDuplicateEval (.inr .budget) (globalFilterPort .typeIndex) (canonicalBudget1 s)

def canonicalBudgetPrepared (s : CanonicalGlobalStore) :=
  wordDuplicateEval (.inr .universe) (globalFilterPort .remaining) (canonicalBudget2 s)

def canonicalBudgetSubtracted (C K N : ℕ) (s : CanonicalGlobalStore) :=
  frameCallerStore (globalFilterPort .typeIndex) (globalFilterPort .remaining)
    (canonicalBudgetPrepared s).stk (canonicalBudgetPrepared s).state.1 (decide (N ≤ C + K))
    (List.replicate (C + K - N) true) []

def canonicalBudgetEval (C K N : ℕ) (s : CanonicalGlobalStore) :=
  canonicalContinueOp.apply (canonicalBudgetSubtracted C K N s)

def canonicalBudgetRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (wordDuplicateRoutine (globalFilterPort .cost) (globalFilterPort .temp) (globalFilterPort .typeIndex))
    (RoutineComposition.seq (wordDuplicateRoutine (.inr .budget) (globalFilterPort .temp) (globalFilterPort .typeIndex))
      (RoutineComposition.seq (wordDuplicateRoutine (.inr .universe) (globalFilterPort .temp) (globalFilterPort .remaining))
        (RoutineComposition.seq (unarySubtractRoutine (globalFilterPort .typeIndex) (globalFilterPort .remaining))
          (Atom.routine canonicalContinueOp))))

theorem canonicalBudget_prepared (C K N : ℕ) (s : CanonicalGlobalStore)
    (hC : s.stk (globalFilterPort .cost) = List.replicate C true)
    (hK : s.stk (.inr .budget) = List.replicate K true)
    (hN : s.stk (.inr .universe) = List.replicate N true)
    (htype : s.stk (globalFilterPort .typeIndex) = []) (hrem : s.stk (globalFilterPort .remaining) = []) :
    (canonicalBudgetPrepared s).stk (globalFilterPort .typeIndex) = List.replicate (C + K) true ∧
    (canonicalBudgetPrepared s).stk (globalFilterPort .remaining) = List.replicate N true := by
  simp [canonicalBudgetPrepared, canonicalBudget2, canonicalBudget1, wordDuplicateEval,
    globalFilterPort, hC, hK, hN, htype, hrem, capReplicate_append, Nat.add_comm]

theorem canonicalBudget_executes (C K N : ℕ) (s : CanonicalGlobalStore)
    (hC : s.stk (globalFilterPort .cost) = List.replicate C true)
    (hK : s.stk (.inr .budget) = List.replicate K true)
    (hN : s.stk (.inr .universe) = List.replicate N true)
    (htype : s.stk (globalFilterPort .typeIndex) = []) (hrem : s.stk (globalFilterPort .remaining) = [])
    (ht : s.stk (globalFilterPort .temp) = []) :
    canonicalBudgetRoutine.Executes s (canonicalBudgetEval C K N s) (3 * C + 3 * K + 4 * N + 11) := by
  have he1 := wordDuplicate_executes (globalFilterPort .cost) (globalFilterPort .temp)
    (globalFilterPort .typeIndex) (by decide) (by decide) (by decide) s ht
  have ht1 : (canonicalBudget1 s).stk (globalFilterPort .temp) = [] := by
    simpa [canonicalBudget1, wordDuplicateEval, globalFilterPort] using ht
  have he2 := wordDuplicate_executes (.inr CanonicalGlobalPort.budget : CanonicalGlobalStack) (globalFilterPort .temp)
    (globalFilterPort .typeIndex) (by decide) (by decide) (by decide) (canonicalBudget1 s) ht1
  have ht2 : (canonicalBudget2 s).stk (globalFilterPort .temp) = [] := by
    simpa [canonicalBudget2, wordDuplicateEval, globalFilterPort] using ht1
  have he3 := wordDuplicate_executes (.inr CanonicalGlobalPort.universe : CanonicalGlobalStack) (globalFilterPort .temp)
    (globalFilterPort .remaining) (by decide) (by decide) (by decide) (canonicalBudget2 s) ht2
  have hK1 : (canonicalBudget1 s).stk (.inr .budget) = List.replicate K true := by
    simpa [canonicalBudget1, wordDuplicateEval, globalFilterPort] using hK
  have hN2 : (canonicalBudget2 s).stk (.inr .universe) = List.replicate N true := by
    simpa [canonicalBudget2, canonicalBudget1, wordDuplicateEval, globalFilterPort] using hN
  rw [hC, List.length_replicate] at he1
  rw [hK1, List.length_replicate] at he2
  rw [hN2, List.length_replicate] at he3
  obtain ⟨hleft, hright⟩ := canonicalBudget_prepared C K N s hC hK hN htype hrem
  have hsub := unarySubtract_executes (globalFilterPort .typeIndex) (globalFilterPort .remaining)
    (by decide) (canonicalBudgetPrepared s).stk (canonicalBudgetPrepared s).state.1
    (canonicalBudgetPrepared s).state.2 (C + K) N
  have hentry : frameCallerStore (globalFilterPort .typeIndex) (globalFilterPort .remaining)
      (canonicalBudgetPrepared s).stk (canonicalBudgetPrepared s).state.1 (canonicalBudgetPrepared s).state.2
      (List.replicate (C + K) true) (List.replicate N true) = canonicalBudgetPrepared s := by
    rw [← hleft, ← hright, frameCallerStore_self]
  rw [hentry] at hsub
  have hreset := Atom.executes canonicalContinueOp (canonicalBudgetSubtracted C K N s)
  have hall := RoutineComposition.seq_executes _ _ he1 (RoutineComposition.seq_executes _ _ he2
    (RoutineComposition.seq_executes _ _ he3 (RoutineComposition.seq_executes _ _ hsub hreset)))
  convert hall using 1 <;> omega

theorem canonicalBudget_value (C K N : ℕ) (s : CanonicalGlobalStore) :
    (canonicalBudgetEval C K N s).stk (globalFilterPort .typeIndex) = List.replicate (C + K - N) true := by
  simp [canonicalBudgetEval, canonicalBudgetSubtracted, canonicalContinueOp, Op.apply, frameCallerStore, globalFilterPort]

theorem canonicalBudget_remaining (C K N : ℕ) (s : CanonicalGlobalStore) :
    (canonicalBudgetEval C K N s).stk (globalFilterPort .remaining) = [] := by
  simp [canonicalBudgetEval, canonicalBudgetSubtracted, canonicalContinueOp, Op.apply, frameCallerStore]

theorem canonicalBudget_state (C K N : ℕ) (s : CanonicalGlobalStore) :
    (canonicalBudgetEval C K N s).state = (s.state.1, true) := rfl

theorem canonicalBudget_extra (C K N : ℕ) (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (htype : k ≠ globalFilterPort .typeIndex) (hrem : k ≠ globalFilterPort .remaining) :
    (canonicalBudgetEval C K N s).stk k = s.stk k := by
  simp [canonicalBudgetEval, canonicalBudgetSubtracted, canonicalContinueOp, Op.apply, frameCallerStore,
    canonicalBudgetPrepared, canonicalBudget2, canonicalBudget1, wordDuplicateEval, htype, hrem]

/- Apply with C=rawRowFixedCost R after the COMPLETE original block
generator. K and N come from the actual preserved global header words.
The physical budget output replaces a now-empty type-counter tape; hence
the former block-loop invariant is deliberately not asserted afterward.
Original output/cost/global data and all other work remain preserved.
-/

end PolytomyReductionModel
