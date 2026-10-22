/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

An actual body for the original nested parser: reset the incoming success
bit for the already specified numeric-reader entry, read/decode one capped
binary value, and append its unary frame to the reversed internal record.
All code is composed at actual Routine boundaries. This is not a whole
parser; reserved physical list counters are preserved for that integration.
-/
import PolytomyUnaryFrameEmitter

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem updates_at_own_values (base : K → List Bool) (r c : K) :
    Function.update (Function.update base r (base r)) c (base c) = base := by
  funext k
  by_cases hc : k = c <;> by_cases hr : k = r <;> simp_all

theorem update_other_restore (base : K → List Bool) (r c : K) (hrc : r ≠ c)
    (ys : List Bool) :
    Function.update (Function.update base r ys) c (base c) = Function.update base r ys := by
  funext k
  by_cases hc : k = c <;> by_cases hr : k = r <;> simp_all

/-- Explicit public-store conversion. No port-renaming oracle or assumed
    multiport implementation is used. Extra record/count ports are in K. -/
theorem emitStore_numeric (r c : K) (base : K → List Bool) (frame : F)
    (guard flag : Bool) (xs ps cs ws os ys zs : List Bool) :
    emitStore (.inl .output : NumericStack K) (.inr r) (.inr c)
      (numericStacks base xs ps cs ws []) frame guard flag os ys zs =
    numericStore (Function.update (Function.update base r ys) c zs)
      (frame, guard) flag xs ps cs ws os := by
  apply countdownStore_ext
  · rfl
  · funext j
    cases j with
    | inl p => cases p <;> simp [emitStore, numericStore, numericStacks]
    | inr k => simp [emitStore, numericStore, numericStacks]

def numericEmittedStore (r : K) (base : K → List Bool) (frame : F)
    (flag : Bool) (xs ps cs ws os : List Bool) : CountdownStore (NumericStack K) F :=
  if flag then numericStore
    (Function.update base r ((unaryFrame os.length).reverse ++ base r))
    (frame, false) true xs ps cs ws []
  else numericStore base (frame, false) false xs ps cs ws os

theorem emitNumeric_executes (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (frame : F) (guard flag : Bool)
    (xs ps cs ws os : List Bool) :
    ∃ n ≤ 5 * os.length + 5,
      (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) false).Executes
        (numericStore base (frame, guard) flag xs ps cs ws os)
        (numericEmittedStore r base frame flag xs ps cs ws os) n := by
  obtain ⟨n, hn, he⟩ := emitFrame_executes
    (.inl .output : NumericStack K) (.inr r) (.inr c) (by simp) (by simp)
    (by simpa using hrc) false (numericStacks base xs ps cs ws []) frame guard flag os
    (base r) (base c)
  refine ⟨n, hn, ?_⟩
  cases flag <;>
    simpa only [emitFrameResult, numericEmittedStore, Bool.false_eq_true, Bool.true_eq_true,
      ↓reduceIte, emitStore_numeric, updates_at_own_values, update_other_restore base r c hrc,
      reverse_unaryFrame_append] using he

def numericStartOp : Op (NumericStack K) Bool (CountdownState F) :=
  .load (fun s => (s.1, false))

def numericRecordRoutine (r c : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine numericStartOp)
    (RoutineComposition.seq (numericFrameRoutine (K := K) (F := F × Bool))
      (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) false))

def numericRecordRawResult (r : K) (base : K → List Bool) (frame : F) (C : ℕ) :
    Option (List Bool × List Bool) → CountdownStore (NumericStack K) F
  | none => numericStore base (frame, false) false [] [] (List.replicate C true) [] []
  | some (word, rest) => numericStore
      (Function.update base r ((unaryFrame (saturatedBinaryValue C word)).reverse ++ base r))
      (frame, false) true rest [] (List.replicate C true) [] []

def numericRecordResult (r : K) (base : K → List Bool) (frame : F) (C : ℕ) :
    Option (ℕ × List Bool) → CountdownStore (NumericStack K) F
  | none => numericStore base (frame, false) false [] [] (List.replicate C true) [] []
  | some (a, rest) => numericStore
      (Function.update base r ((unaryFrame a).reverse ++ base r))
      (frame, false) true rest [] (List.replicate C true) [] []

theorem numericRecordRawResult_eq (r : K) (base : K → List Bool) (frame : F)
    (C : ℕ) (bits : List Bool) :
    numericRecordRawResult r base frame C (readRawBinaryFrame bits) =
      numericRecordResult r base frame C (readSaturatedBinaryNatFrame C bits) := by
  rw [← readSaturatedViaPrimitive_eq]
  unfold readSaturatedViaPrimitive
  cases hp : readRawBinaryFrame bits with
  | none => rfl
  | some p =>
      rcases p with ⟨word, rest⟩
      simp only [Option.map_some, cappedUnaryWord_original_payload,
        List.length_replicate, numericRecordRawResult, numericRecordResult]

theorem emit_numeric_result (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (frame : F) (guard : Bool) (C : ℕ)
    (result : Option (List Bool × List Bool)) :
    ∃ n ≤ 5 * C + 5,
      (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) false).Executes
        (numericFrameResult base (frame, guard) C result)
        (numericRecordRawResult r base frame C result) n := by
  cases result with
  | none =>
      obtain ⟨n, hn, he⟩ := emitNumeric_executes r c hrc base frame guard false
        [] [] (List.replicate C true) [] []
      exact ⟨n, by simp only [List.length_nil] at hn; omega, he⟩
  | some p =>
      rcases p with ⟨word, rest⟩
      obtain ⟨n, hn, he⟩ := emitNumeric_executes r c hrc base frame guard true
        rest [] (List.replicate C true) [] (List.replicate (saturatedBinaryValue C word) true)
      simp only [List.length_replicate] at hn
      have hv := saturatedBinaryValue_le C word
      refine ⟨n, by omega, ?_⟩
      simpa only [numericFrameResult, numericRecordRawResult, numericEmittedStore,
        ↓reduceIte, List.length_replicate] using he

def numericRecordStepBound (L C : ℕ) : ℕ := 6 * L * C + 8 * L + 8 * C + 14

/-- Exact all-word original-reader semantics, including failed frames and
    successful zero. The initial flag is deliberately reset for this NEW
    attempt. A higher-level failed parse must skip this routine, as the
    countdown guard does; this is not a failure-absorbing wrapper. -/
theorem numericRecord_executes (r c : K) (hrc : r ≠ c) (C : ℕ)
    (bits : List Bool) (base : K → List Bool) (frame : F) (guard flag : Bool) :
    ∃ n ≤ numericRecordStepBound bits.length C,
      (numericRecordRoutine r c).Executes
        (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] [])
        (numericRecordResult r base frame C (readSaturatedBinaryNatFrame C bits)) n := by
  have hstart := Atom.executes (numericStartOp (K := K) (F := F))
    (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] [])
  obtain ⟨n, hn, hr⟩ := numericFrame_executes C bits base (frame, guard)
  obtain ⟨m, hm, he⟩ := emit_numeric_result r c hrc base frame guard C (readRawBinaryFrame bits)
  have hread := RoutineComposition.seq_executes
    (numericFrameRoutine (K := K) (F := F × Bool))
    (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) false) hr he
  have hall := RoutineComposition.seq_executes (Atom.routine numericStartOp)
    (RoutineComposition.seq (numericFrameRoutine (K := K) (F := F × Bool))
      (emitFrameRoutine (.inl .output : NumericStack K) (.inr r) (.inr c) false)) hstart hread
  refine ⟨1 + (n + m), ?_, ?_⟩
  · unfold numericRecordStepBound numericFrameStepBound at *
    omega
  · simpa only [numericRecordRoutine, numericRecordRawResult_eq] using hall

theorem numericRecord_preserves_counter (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (frame : F) (C : ℕ) (result : Option (ℕ × List Bool)) :
    (numericRecordResult r base frame C result).stk (.inr c) = base c := by
  cases result with
  | none => rfl
  | some p => rcases p with ⟨a, rest⟩; simp [numericRecordResult, numericStore, numericStacks, Ne.symm hrc]

theorem numericRecord_preserves_scratch (r : K) (base : K → List Bool)
    (frame : F) (C : ℕ) (result : Option (ℕ × List Bool)) :
    (numericRecordResult r base frame C result).state.1 = (frame, false) ∧
      (numericRecordResult r base frame C result).stk (.inl .cap) = List.replicate C true ∧
      (numericRecordResult r base frame C result).stk (.inl .payload) = [] ∧
      (numericRecordResult r base frame C result).stk (.inl .work) = [] ∧
      (numericRecordResult r base frame C result).stk (.inl .output) = [] := by
  cases result with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some p => rcases p with ⟨a, rest⟩; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/- The reserved counter is preserved and all numeric/emit scratch is
returned clean. The reversed record is extended only after successful
parsing, and failure never becomes a successful zero. This is one actual
body, not the full inner/outer loop contract: whole-state invariants,
source-length/counter bounds, row-count reader/copy composition, two-level
assembly, suffix rejection, caps and final cleanup remain to be supplied.
The complete original reduction, independent checker, closed encoded
hardness and kernel verification obligations remain unchanged and open.
-/

end PolytomyReductionModel
