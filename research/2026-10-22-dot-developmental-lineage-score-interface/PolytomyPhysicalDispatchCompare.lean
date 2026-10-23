/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual original scalar comparisons through restoring copies and unary
subtraction. All physical data return EXACTLY unchanged; only the public
success Boolean receives right<=left. Operand values are not control.
-/
import PolytomyOriginalDispatchPreparation

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

structure DispatchComparePorts where
  «left» : CanonicalGlobalStack
  «right» : CanonicalGlobalStack
  left_type : «left» ≠ globalFilterPort .typeIndex
  left_remaining : «left» ≠ globalFilterPort .remaining
  left_temp : «left» ≠ globalFilterPort .temp
  right_type : «right» ≠ globalFilterPort .typeIndex
  right_remaining : «right» ≠ globalFilterPort .remaining
  right_temp : «right» ≠ globalFilterPort .temp

def dispatchFlagStore (flag : Bool) (s : CanonicalGlobalStore) : CanonicalGlobalStore := ⟨(s.state.1, flag), s.stk⟩

def dispatchCompareFirst (p : DispatchComparePorts) (s : CanonicalGlobalStore) :=
  wordDuplicateEval p.left (globalFilterPort .typeIndex) s

def dispatchComparePrepared (p : DispatchComparePorts) (s : CanonicalGlobalStore) :=
  wordDuplicateEval p.right (globalFilterPort .remaining) (dispatchCompareFirst p s)

def dispatchCompareSubtracted (p : DispatchComparePorts) (C D : ℕ) (s : CanonicalGlobalStore) :=
  frameCallerStore (globalFilterPort .typeIndex) (globalFilterPort .remaining)
    (dispatchComparePrepared p s).stk (dispatchComparePrepared p s).state.1 (decide (D ≤ C))
    (List.replicate (C - D) true) []

def dispatchCompareEval (p : DispatchComparePorts) (C D : ℕ) (s : CanonicalGlobalStore) :=
  clearStackEval (globalFilterPort .typeIndex) (dispatchCompareSubtracted p C D s)

def dispatchCompareRoutine (p : DispatchComparePorts) :
    Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (wordDuplicateRoutine p.left (globalFilterPort .temp) (globalFilterPort .typeIndex))
    (RoutineComposition.seq (wordDuplicateRoutine p.right (globalFilterPort .temp) (globalFilterPort .remaining))
      (RoutineComposition.seq (unarySubtractRoutine (globalFilterPort .typeIndex) (globalFilterPort .remaining))
        (clearStackRoutine (globalFilterPort .typeIndex))))

theorem dispatchCompare_result (p : DispatchComparePorts) (C D : ℕ) (s : CanonicalGlobalStore)
    (htype : s.stk (globalFilterPort .typeIndex) = []) (hrem : s.stk (globalFilterPort .remaining) = []) :
    dispatchCompareEval p C D s = dispatchFlagStore (decide (D ≤ C)) s := by
  apply countdownStore_ext
  · rfl
  · funext k
    by_cases ht : k = globalFilterPort .typeIndex
    · subst k
      simp [dispatchCompareEval, clearStackEval, dispatchFlagStore, htype]
    by_cases hr : k = globalFilterPort .remaining
    · subst k
      simp [dispatchCompareEval, clearStackEval, dispatchCompareSubtracted, frameCallerStore,
        globalFilterPort, dispatchFlagStore, hrem]
    · simp [dispatchCompareEval, clearStackEval, dispatchCompareSubtracted, frameCallerStore,
        dispatchComparePrepared, dispatchCompareFirst, wordDuplicateEval, dispatchFlagStore, ht, hr]

theorem dispatchCompare_executes (p : DispatchComparePorts) (C D : ℕ) (s : CanonicalGlobalStore)
    (hC : s.stk p.left = List.replicate C true) (hD : s.stk p.right = List.replicate D true)
    (htype : s.stk (globalFilterPort .typeIndex) = []) (hrem : s.stk (globalFilterPort .remaining) = [])
    (htemp : s.stk (globalFilterPort .temp) = []) :
    ∃ n ≤ 4 * C + 4 * D + 8,
      (dispatchCompareRoutine p).Executes s (dispatchFlagStore (decide (D ≤ C)) s) n := by
  have h1 := wordDuplicate_executes p.left (globalFilterPort .temp) (globalFilterPort .typeIndex)
    p.left_temp p.left_type (by decide) s htemp
  have ht1 : (dispatchCompareFirst p s).stk (globalFilterPort .temp) = [] := by
    simpa [dispatchCompareFirst, wordDuplicateEval, globalFilterPort] using htemp
  have h2 := wordDuplicate_executes p.right (globalFilterPort .temp) (globalFilterPort .remaining)
    p.right_temp p.right_remaining (by decide) (dispatchCompareFirst p s) ht1
  have hD1 : (dispatchCompareFirst p s).stk p.right = List.replicate D true := by
    simpa [dispatchCompareFirst, wordDuplicateEval, p.right_type] using hD
  rw [hC, List.length_replicate] at h1
  rw [hD1, List.length_replicate] at h2
  have hl : (dispatchComparePrepared p s).stk (globalFilterPort .typeIndex) = List.replicate C true := by
    simp [dispatchComparePrepared, dispatchCompareFirst, wordDuplicateEval, globalFilterPort, hC, htype]
  have hr : (dispatchComparePrepared p s).stk (globalFilterPort .remaining) = List.replicate D true := by
    simp [dispatchComparePrepared, dispatchCompareFirst, wordDuplicateEval,
      globalFilterPort, p.right_type, hD, hrem]
  have hsub := unarySubtract_executes (globalFilterPort .typeIndex) (globalFilterPort .remaining)
    (by decide) (dispatchComparePrepared p s).stk (dispatchComparePrepared p s).state.1
    (dispatchComparePrepared p s).state.2 C D
  have hin : frameCallerStore (globalFilterPort .typeIndex) (globalFilterPort .remaining)
      (dispatchComparePrepared p s).stk (dispatchComparePrepared p s).state.1 (dispatchComparePrepared p s).state.2
      (List.replicate C true) (List.replicate D true) = dispatchComparePrepared p s := by
    rw [← hl, ← hr, frameCallerStore_self]
  rw [hin] at hsub
  have hc := clearStack_executes (globalFilterPort .typeIndex) (dispatchCompareSubtracted p C D s)
  have hlen : ((dispatchCompareSubtracted p C D s).stk (globalFilterPort .typeIndex)).length = C - D := by
    simp [dispatchCompareSubtracted, frameCallerStore, globalFilterPort]
  rw [hlen] at hc
  have hall := RoutineComposition.seq_executes _ _ h1
    (RoutineComposition.seq_executes _ _ h2 (RoutineComposition.seq_executes _ _ hsub hc))
  change (dispatchCompareRoutine p).Executes s (dispatchCompareEval p C D s)
    ((3 * C + 3) + ((3 * D + 3) + ((D + 1) + (C - D + 1)))) at hall
  rw [dispatchCompare_result p C D s htype hrem] at hall
  exact ⟨_, by omega, hall⟩

def originalBudgetUniversePorts : DispatchComparePorts where
  «left» := .inr .budget
  «right» := .inr .universe
  left_type := by decide
  left_remaining := by decide
  left_temp := by decide
  right_type := by decide
  right_remaining := by decide
  right_temp := by decide

def originalBudgetProductPorts : DispatchComparePorts where
  «left» := .inr .budget
  «right» := globalScanPort (.inr .savedCount)
  left_type := by decide
  left_remaining := by decide
  left_temp := by decide
  right_type := by decide
  right_remaining := by decide
  right_temp := by decide

/- The exact original tests are N<=K and N*m<=K. The former's false
case is K<N. Both comparisons restore even unrelated caller data, with
all borrowed type/remaining/temp tapes fresh. Zero operands are included.
-/

end PolytomyReductionModel
