/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual ORIGINAL unary list-count reader followed by reversed-record
emission and physical count copy. The reserved count stack must start
empty; no overwrite of an occupied caller stack is silently assumed.
-/
import PolytomyNumericListObservation

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def numericCopiedCountStore (r c : K) (base : K → List Bool) (frame : F)
    (flag : Bool) (xs cs os : List Bool) : CountdownStore (NumericStack K) F :=
  if flag then numericStore
    (Function.update (Function.update base r ((unaryFrame os.length).reverse ++ base r))
      c (List.replicate os.length true))
    (frame, false) true xs [] cs [] []
  else numericStore base (frame, false) false xs [] cs [] os

theorem emitNumericCopy_executes (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (hc : base c = []) (frame : F) (guard flag : Bool)
    (xs cs os : List Bool) :
    ∃ n ≤ 5 * os.length + 5,
      (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) true).Executes
        (numericStore base (frame, guard) flag xs [] cs [] os)
        (numericCopiedCountStore r c base frame flag xs cs os) n := by
  obtain ⟨n, hn, he⟩ := emitFrame_executes
    (.inl .output : NumericStack K) (.inr r) (.inr c) (by simp) (by simp)
    (by simpa using hrc) true (numericStacks base xs [] cs [] []) frame guard flag os
    (base r) (base c)
  refine ⟨n, hn, ?_⟩
  cases flag <;>
    simpa only [emitFrameResult, numericCopiedCountStore, Bool.false_eq_true, Bool.true_eq_true,
      ↓reduceIte, emitStore_numeric, updates_at_own_values, reverse_unaryFrame_append,
      hc, List.append_nil] using he

theorem countCaller_numeric_store (base : K → List Bool) (frame : F) (guard flag : Bool)
    (xs cs os : List Bool) :
    frameCallerStore (.inl .source : NumericStack K) (.inl .output)
      (numericStacks base [] [] cs [] []) (frame, guard) flag xs os =
    numericStore base (frame, guard) flag xs [] cs [] os := by
  apply countdownStore_ext
  · rfl
  · funext j
    cases j with
    | inl p => cases p <;> simp [frameCallerStore, numericStore, numericStacks]
    | inr k => simp [frameCallerStore, numericStore, numericStacks]

def countNumericReaderResult (base : K → List Bool) (frame : F) (guard : Bool) (cs : List Bool) :
    Option (ℕ × List Bool) → CountdownStore (NumericStack K) F
  | none => numericStore base (frame, guard) false [] [] cs [] []
  | some (n, rest) => numericStore base (frame, guard) true rest [] cs [] (List.replicate n true)

theorem countCaller_numeric_result (base : K → List Bool) (frame : F) (guard : Bool)
    (cs : List Bool) (result : Option (ℕ × List Bool)) :
    unaryCallerResult (.inl .source : NumericStack K) (.inl .output)
      (numericStacks base [] [] cs [] []) (frame, guard) result =
    countNumericReaderResult base frame guard cs result := by
  cases result with
  | none => exact countCaller_numeric_store base frame guard false [] cs []
  | some p => rcases p with ⟨n, rest⟩; exact countCaller_numeric_store base frame guard true rest cs _

def listCountPrefixResult (r c : K) (base : K → List Bool) (frame : F) (cs : List Bool) :
    Option (ℕ × List Bool) → CountdownStore (NumericStack K) F
  | none => numericStore base (frame, false) false [] [] cs [] []
  | some (n, rest) => numericStore
      (Function.update (Function.update base r ((unaryFrame n).reverse ++ base r))
        c (List.replicate n true))
      (frame, false) true rest [] cs [] []

theorem count_result_copy_executes (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (hc : base c = []) (frame : F) (guard : Bool)
    (cs bits : List Bool) :
    ∃ n ≤ 5 * bits.length + 5,
      (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) true).Executes
        (countNumericReaderResult base frame guard cs (readUnaryFrame bits))
        (listCountPrefixResult r c base frame cs (readUnaryFrame bits)) n := by
  cases hp : readUnaryFrame bits with
  | none =>
      obtain ⟨n, hn, he⟩ := emitNumericCopy_executes r c hrc base hc frame guard false [] cs []
      refine ⟨n, by simp only [List.length_nil] at hn; omega, ?_⟩
      exact he
  | some p =>
      rcases p with ⟨a, rest⟩
      obtain ⟨n, hn, he⟩ := emitNumericCopy_executes r c hrc base hc frame guard true rest cs
        (List.replicate a true)
      have ha := readUnaryFrame_consumption bits a rest hp
      simp only [List.length_replicate] at hn
      refine ⟨n, by omega, ?_⟩
      simpa only [countNumericReaderResult, listCountPrefixResult, numericCopiedCountStore,
        ↓reduceIte, List.length_replicate] using he

def listCountPrefixRoutine (r c : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine numericStartOp)
    (RoutineComposition.seq (unaryCountRoutine (.inl .source : NumericStack K) (.inl .output))
      (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) true))

/-- This starts one new count-read attempt. Higher-level failed parses
    must skip it; the later row wrapper provides that absorbing guard. -/
theorem listCountPrefix_executes (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (hc : base c = []) (frame : F) (guard flag : Bool)
    (cs bits : List Bool) :
    ∃ n ≤ 7 * bits.length + 8,
      (listCountPrefixRoutine r c).Executes
        (numericStore base (frame, guard) flag bits [] cs [] [])
        (listCountPrefixResult r c base frame cs (readUnaryFrame bits)) n := by
  have hstart := Atom.executes (numericStartOp (K := K) (F := F))
    (numericStore base (frame, guard) flag bits [] cs [] [])
  obtain ⟨n, hn, hr⟩ := unaryCount_executes (.inl .source : NumericStack K) (.inl .output)
    (by simp) (numericStacks base [] [] cs [] []) (frame, guard) bits
  rw [countCaller_numeric_store, countCaller_numeric_result] at hr
  obtain ⟨m, hm, he⟩ := count_result_copy_executes r c hrc base hc frame guard cs bits
  have hread := RoutineComposition.seq_executes
    (unaryCountRoutine (.inl .source : NumericStack K) (.inl .output))
    (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) true) hr he
  have hall := RoutineComposition.seq_executes (Atom.routine numericStartOp)
    (RoutineComposition.seq (unaryCountRoutine (.inl .source : NumericStack K) (.inl .output))
      (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) true)) hstart hread
  exact ⟨1 + (n + m), by omega, hall⟩

theorem listCountPrefix_invariant (r c : K) (base : K → List Bool) (frame : F)
    (C L : ℕ) (bits : List Bool) (hL : bits.length ≤ L) :
    NumericLoopInv C L
      (listCountPrefixResult r c base frame (List.replicate C true) (readUnaryFrame bits)) := by
  cases hp : readUnaryFrame bits with
  | none => simp [listCountPrefixResult, hp, NumericLoopInv, numericStore, numericStacks]
  | some p =>
      rcases p with ⟨n, rest⟩
      have hl := readUnaryFrame_consumption bits n rest hp
      have hr : rest.length ≤ L := by omega
      simpa [listCountPrefixResult, hp, NumericLoopInv, numericStore, numericStacks] using hr

theorem listCountPrefix_counter_bound (r c : K) (base : K → List Bool) (hc : base c = [])
    (frame : F) (cs bits : List Bool) :
    ((listCountPrefixResult r c base frame cs (readUnaryFrame bits)).stk (.inr c)).length ≤ bits.length := by
  cases hp : readUnaryFrame bits with
  | none => simp [listCountPrefixResult, hp, numericStore, numericStacks, hc]
  | some p =>
      rcases p with ⟨n, rest⟩
      have hl := readUnaryFrame_consumption bits n rest hp
      simp only [listCountPrefixResult, numericStore, numericStacks, Function.update_same,
        List.length_replicate]
      omega

theorem listCountPrefix_record_bound (r c : K) (hrc : r ≠ c) (base : K → List Bool)
    (frame : F) (cs bits : List Bool) :
    ((listCountPrefixResult r c base frame cs (readUnaryFrame bits)).stk (.inr r)).length ≤
      (base r).length + bits.length + 1 := by
  cases hp : readUnaryFrame bits with
  | none => simp [listCountPrefixResult, hp, numericStore, numericStacks]
  | some p =>
      rcases p with ⟨n, rest⟩
      have hl := readUnaryFrame_consumption bits n rest hp
      simp only [listCountPrefixResult, numericStore, numericStacks, Function.update_of_ne hrc,
        Function.update_same, List.length_append, List.length_reverse, unaryFrame,
        List.length_replicate, List.length_singleton]
      omega

/- Actual unary count reading, record emission and fresh physical count
copy are now composed with exact original readUnaryFrame behavior. Cap and
unrelated ports remain untouched. These statements still do not execute a
complete row or the outer source grammar. The next composition must join
this result to the observed numeric-list loop, then retain the complete
source suffix/record/failure and cleanup obligations. All code and prior
dependencies remain unelaborated; no runtime or full closure is claimed.
-/

end PolytomyReductionModel
