/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual operand-preserving subtraction/comparison for original constructor
branches. Copies are explicit; both original operands survive. The result
flag is a fresh comparison bit, not an inherited parser-success promise.
-/
import PolytomyPreservingUnaryProduct

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def preservingUnarySubtractRoutine (m t l r : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (copyCapToExtraRoutine l)
    (RoutineComposition.seq (copySavedCapRoutine m t r)
      (unarySubtractRoutine (F := F × Bool) (.inr l) (.inr r)))

theorem preservingUnarySubtract_executes (m t l r : K)
    (hmt : m ≠ t) (hlm : l ≠ m) (hlt : l ≠ t) (hlr : l ≠ r)
    (hrm : r ≠ m) (hrt : r ≠ t) (C D L : ℕ)
    (bits : List Bool) (hL : bits.length ≤ L) (base : K → List Bool)
    (hm : base m = List.replicate D true) (ht : base t = []) (hl : base l = []) (hr : base r = [])
    (frame : F) (guard flag : Bool) :
    (preservingUnarySubtractRoutine m t l r).Executes
      (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] [])
      (numericStore (Function.update base l (List.replicate (C - D) true))
        (frame, guard) (decide (D ≤ C)) bits [] (List.replicate C true) [] [])
      (6 * C + 7 * D + 13) := by
  let s := numericStore base (frame, guard) flag bits [] (List.replicate C true) [] []
  let u := copyCapToExtraEval l C s
  let v := copyCapToExtraEval r D u
  have hi : NumericLoopInv C L s := by simpa [s, NumericLoopInv, numericStore, numericStacks] using hL
  have h1 := copyCapToExtra_executes l C L s hi
  have hiu := copyCapToExtra_invariant l C L s hi
  have hm' : u.stk (.inr m) = List.replicate D true := by
    simp [u, s, copyCapToExtraEval, numericStore, numericStacks, Ne.symm hlm, hm]
  have ht' : u.stk (.inr t) = [] := by
    simp [u, s, copyCapToExtraEval, numericStore, numericStacks, Ne.symm hlt, ht]
  have h2 := copySavedCap_executes m t r hmt hrm hrt C D L u hiu hm' ht'
  have h3 := unarySubtract_executes (.inr l : NumericStack K) (.inr r) (by simpa using hlr)
    (numericStacks base bits [] (List.replicate C true) [] []) (frame, guard) flag C D
  have hentry : frameCallerStore (.inr l) (.inr r)
      (numericStacks base bits [] (List.replicate C true) [] []) (frame, guard) flag
      (List.replicate C true) (List.replicate D true) = v := by
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> rfl
      | inr k => by_cases hkr : k = r <;> by_cases hkl : k = l <;>
          simp_all [frameCallerStore, v, u, s, copyCapToExtraEval, numericStore, numericStacks]
  have hexit : frameCallerStore (.inr l) (.inr r)
      (numericStacks base bits [] (List.replicate C true) [] []) (frame, guard) (decide (D ≤ C))
      (List.replicate (C - D) true) [] =
      numericStore (Function.update base l (List.replicate (C - D) true))
        (frame, guard) (decide (D ≤ C)) bits [] (List.replicate C true) [] [] := by
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> rfl
      | inr k => by_cases hkr : k = r <;> by_cases hkl : k = l <;>
          simp_all [frameCallerStore, numericStore, numericStacks]
  rw [hentry, hexit] at h3
  have h23 := RoutineComposition.seq_executes (copySavedCapRoutine m t r)
    (unarySubtractRoutine (F := F × Bool) (.inr l) (.inr r)) h2 h3
  have hall := RoutineComposition.seq_executes (copyCapToExtraRoutine l)
    (RoutineComposition.seq (copySavedCapRoutine m t r)
      (unarySubtractRoutine (F := F × Bool) (.inr l) (.inr r))) h1 h23
  convert hall using 1 <;> omega

def preservingUnaryCompareRoutine (m t l r : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (preservingUnarySubtractRoutine m t l r) (clearStackRoutine (.inr l))

theorem preservingUnaryCompare_executes (m t l r : K)
    (hmt : m ≠ t) (hlm : l ≠ m) (hlt : l ≠ t) (hlr : l ≠ r)
    (hrm : r ≠ m) (hrt : r ≠ t) (C D L : ℕ)
    (bits : List Bool) (hL : bits.length ≤ L) (base : K → List Bool)
    (hm : base m = List.replicate D true) (ht : base t = []) (hl : base l = []) (hr : base r = [])
    (frame : F) (guard flag : Bool) :
    ∃ n ≤ 7 * C + 7 * D + 14,
      (preservingUnaryCompareRoutine m t l r).Executes
        (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] [])
        (numericStore base (frame, guard) (decide (D ≤ C)) bits [] (List.replicate C true) [] []) n := by
  let u := numericStore (Function.update base l (List.replicate (C - D) true))
    (frame, guard) (decide (D ≤ C)) bits [] (List.replicate C true) [] []
  have h1 := preservingUnarySubtract_executes m t l r hmt hlm hlt hlr hrm hrt C D L bits hL
    base hm ht hl hr frame guard flag
  have h2 := clearStack_executes (.inr l : NumericStack K) u
  have he : clearStackEval (.inr l) u =
      numericStore base (frame, guard) (decide (D ≤ C)) bits [] (List.replicate C true) [] [] := by
    apply countdownStore_ext
    · rfl
    · funext k; cases k with
      | inl p => cases p <;> rfl
      | inr k => by_cases hkl : k = l <;> simp [clearStackEval, u, numericStore, numericStacks, hkl, hl]
  rw [he] at h2
  have hall := RoutineComposition.seq_executes (preservingUnarySubtractRoutine m t l r)
    (clearStackRoutine (.inr l)) h1 h2
  have hlen : (u.stk (.inr l)).length = C - D := by simp [u, numericStore, numericStacks]
  rw [hlen] at hall
  exact ⟨(6 * C + 7 * D + 13) + ((C - D) + 1), by omega, hall⟩

/- Comparator return restores ALL data stacks, including both original
operands and all scratch, and changes only the public comparison bit.
Subtraction preserves originals but deliberately leaves a fresh residual.
Zero difference plus true means equality; zero plus false means underflow.
These original-constructor arithmetic components do not discharge tagged
record validation, row scans, canonical serializer, independent checker,
closed encoded hardness or any compilation/kernel obligation.
-/

end PolytomyReductionModel
