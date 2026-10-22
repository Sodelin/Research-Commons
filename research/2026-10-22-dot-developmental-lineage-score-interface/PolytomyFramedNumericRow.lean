/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual complete framed-row component for the ORIGINAL source grammar:
unary count reading/copy, followed by that many capped binary numeric
readers, with exact readFramedList observation and partial-storage bound.
This starts a new row attempt. Overall failure absorption is still the
outer caller's responsibility, not a claim about unconditional calls.
-/
import PolytomyListCountPrefix

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def framedNumericRowRoutine (r c : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (listCountPrefixRoutine r c) (numericListRoutine r c)

def framedNumericRowResult (r c : K) (base : K → List Bool) (frame : F)
    (C : ℕ) (bits : List Bool) : CountdownStore (NumericStack K) F :=
  numericListEval r c C
    (listCountPrefixResult r c base frame (List.replicate C true) (readUnaryFrame bits))

def framedNumericRowStepBound (L C : ℕ) : ℕ :=
  L * (numericRecordStepBound L C + 3) + 7 * L + 11

theorem framedNumericRow_executes (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (hc : base c = []) (frame : F) (guard flag : Bool)
    (C L : ℕ) (bits : List Bool) (hL : bits.length ≤ L) :
    ∃ n ≤ framedNumericRowStepBound L C,
      (framedNumericRowRoutine r c).Executes
        (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] [])
        (framedNumericRowResult r c base frame C bits) n ∧
      NumericLoopInv C L (framedNumericRowResult r c base frame C bits) ∧
      (framedNumericRowResult r c base frame C bits).state.1.2 = false ∧
      ((framedNumericRowResult r c base frame C bits).state.2 = true →
        (framedNumericRowResult r c base frame C bits).stk (.inr c) = []) := by
  obtain ⟨n, hn, hp⟩ := listCountPrefix_executes r c hrc base hc frame guard flag
    (List.replicate C true) bits
  let p := listCountPrefixResult r c base frame (List.replicate C true) (readUnaryFrame bits)
  have hi := listCountPrefix_invariant r c base frame C L bits hL
  obtain ⟨m, hm, hrun, hInv, hguard, hclear⟩ := numericList_executes r c hrc C L p hi
  have hcount : (p.stk (.inr c)).length ≤ L :=
    (listCountPrefix_counter_bound r c base hc frame (List.replicate C true) bits).trans hL
  have hmul := Nat.mul_le_mul_right (numericRecordStepBound L C + 3) hcount
  have hall := RoutineComposition.seq_executes (listCountPrefixRoutine r c) (numericListRoutine r c) hp hrun
  refine ⟨n + m, ?_, hall, hInv, hguard, hclear⟩
  unfold framedNumericRowStepBound
  omega

theorem readMany_saturated_length (C n : ℕ) (bits : List Bool) (values : List ℕ)
    (rest : List Bool) (h : readMany (readSaturatedBinaryNatFrame C) n bits = some (values, rest)) :
    values.length = n := by
  have hc : ∀ xs a tail, readSaturatedBinaryNatFrame C xs = some (a, tail) →
      (fun _ : ℕ => 0) a + tail.length ≤ xs.length := by
    intro xs a tail hp
    simpa using readSaturated_remaining C xs a tail hp
  exact (readMany_consumption (readSaturatedBinaryNatFrame C) (fun _ => 0) hc n bits values rest h).1

/-- Exact original row grammar: list counts are unary record COUNTS,
    but each row item is still the original capped BINARY numeric frame.
    Successful observation includes both untouched suffix and exact log. -/
theorem framedNumericRow_observation (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (frame : F) (C : ℕ) (bits : List Bool) :
    numericListObservation r (framedNumericRowResult r c base frame C bits) =
      (readFramedList (readSaturatedBinaryNatFrame C) bits).map
        (fun p => (p.2, (encodeFramedList unaryFrame p.1).reverse ++ base r)) := by
  unfold framedNumericRowResult
  rw [numericList_observation_eq r c hrc]
  cases hp : readUnaryFrame bits with
  | none =>
      simp [numericListSpecification, listCountPrefixResult, hp, numericStore,
        numericStacks, readFramedList]
  | some p =>
      rcases p with ⟨n, tail⟩
      simp only [numericListSpecification, listCountPrefixResult, numericStore, numericStacks,
        ↓reduceIte, Function.update_same, Function.update_of_ne hrc, List.length_replicate,
        readFramedList, hp]
      cases hq : readMany (readSaturatedBinaryNatFrame C) n tail with
      | none => simp [hq]
      | some q =>
          rcases q with ⟨values, rest⟩
          have hv := readMany_saturated_length C n tail values rest hq
          simp [hq, encodeFramedList, hv, List.reverse_append, List.append_assoc]

theorem framedNumericRow_record_bound (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (hc : base c = []) (frame : F)
    (C L : ℕ) (bits : List Bool) (hL : bits.length ≤ L) :
    ((framedNumericRowResult r c base frame C bits).stk (.inr r)).length ≤
      (base r).length + L * (C + 2) + 1 := by
  let p := listCountPrefixResult r c base frame (List.replicate C true) (readUnaryFrame bits)
  have hloop := numericList_record_length r c hrc C p
  have hprefix := listCountPrefix_record_bound r c hrc base frame (List.replicate C true) bits
  have hcount := (listCountPrefix_counter_bound r c base hc frame (List.replicate C true) bits).trans hL
  have hmul := Nat.mul_le_mul_right (C + 1) hcount
  change ((numericListEval r c C p).stk (.inr r)).length ≤ _
  nlinarith

/-- One complete framed-row component, with actual execution, exact
    original grammar observation and all-path boundary storage together. -/
theorem framedNumericRow_executes_observed (r c : K) (hrc : r ≠ c)
    (base : K → List Bool) (hc : base c = []) (frame : F) (guard flag : Bool)
    (C L : ℕ) (bits : List Bool) (hL : bits.length ≤ L) :
    ∃ n ≤ framedNumericRowStepBound L C,
      (framedNumericRowRoutine r c).Executes
        (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] [])
        (framedNumericRowResult r c base frame C bits) n ∧
      numericListObservation r (framedNumericRowResult r c base frame C bits) =
        (readFramedList (readSaturatedBinaryNatFrame C) bits).map
          (fun p => (p.2, (encodeFramedList unaryFrame p.1).reverse ++ base r)) ∧
      NumericLoopInv C L (framedNumericRowResult r c base frame C bits) ∧
      ((framedNumericRowResult r c base frame C bits).state.2 = true →
        (framedNumericRowResult r c base frame C bits).stk (.inr c) = []) ∧
      ((framedNumericRowResult r c base frame C bits).stk (.inr r)).length ≤
        (base r).length + L * (C + 2) + 1 := by
  obtain ⟨n, hn, hr, hi, hg, hclear⟩ :=
    framedNumericRow_executes r c hrc base hc frame guard flag C L bits hL
  exact ⟨n, hn, hr, framedNumericRow_observation r c hrc base frame C bits, hi, hclear,
    framedNumericRow_record_bound r c hrc base hc frame C L bits hL⟩

/- Complete framed ROW semantics is supplied here, not the whole source.
The input inner counter must be empty. On successful return it is empty
again, but early failure may leave a suffix. An outer invariant must thus
require emptiness only when success is true and skip new row attempts once
failure occurs. It must also prove preservation of its DISTINCT outer
counter. Shared cached guard reuse is safe only because the outer loop
re-peeks after each body, not because an inner loop preserves that guard.
Outer rows, headers/cap construction/switching, complete-input validation,
final reversal/tagging/all-path cleanup, whole constructor/checker, closed
encoded hardness and every kernel check remain open. No runtime or model
change, and no full closure or novelty claim, is introduced.
-/

end PolytomyReductionModel
