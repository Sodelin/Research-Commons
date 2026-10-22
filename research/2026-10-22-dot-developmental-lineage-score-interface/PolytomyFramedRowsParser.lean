/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual complete two-level ROWS parser for the ORIGINAL source grammar:
outer unary count, guarded original framed rows, exact nested observation,
and partial/failing-state bounds. Source headers and complete-input finish
are deliberately not claimed here.
-/
import PolytomyOuterRowsObservation

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem readMany_length_exact {A : Type} (read : List Bool → Option (A × List Bool))
    (n : ℕ) : ∀ bits values rest, readMany read n bits = some (values, rest) → values.length = n := by
  induction n with
  | zero =>
      intro bits values rest h
      simp only [readMany, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      rfl
  | succ n ih =>
      intro bits values rest h
      cases hp : read bits with
      | none => simp [readMany, hp] at h
      | some p =>
          rcases p with ⟨a, tail⟩
          cases hq : readMany read n tail with
          | none => simp [readMany, hp, hq] at h
          | some q =>
              rcases q with ⟨xs, after⟩
              have hi := ih tail xs after hq
              simp only [readMany, hp, hq, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1]
              simp [hi]

theorem listCountPrefix_extra (r d k : K) (hkr : k ≠ r) (hkd : k ≠ d)
    (base : K → List Bool) (frame : F) (cs : List Bool) (result : Option (ℕ × List Bool)) :
    (listCountPrefixResult r d base frame cs result).stk (.inr k) = base k := by
  cases result with
  | none => rfl
  | some p => rcases p with ⟨n, rest⟩; simp [listCountPrefixResult, numericStore, numericStacks, hkr, hkd]

theorem framedRowsPrefix_invariant (r c d : K) (hrc : r ≠ c) (hcd : c ≠ d)
    (base : K → List Bool) (hc : base c = []) (frame : F) (C L : ℕ)
    (bits : List Bool) (hL : bits.length ≤ L) :
    RowOuterInv c C L
      (listCountPrefixResult r d base frame (List.replicate C true) (readUnaryFrame bits)) := by
  refine ⟨listCountPrefix_invariant r d base frame C L bits hL, ?_⟩
  intro hok
  rw [listCountPrefix_extra r d c (Ne.symm hrc) hcd, hc]

def framedRowsRoutine (r c d : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (listCountPrefixRoutine r d) (rowOuterRoutine r c d)

def framedRowsResult (r c d : K) (base : K → List Bool) (frame : F)
    (C : ℕ) (bits : List Bool) : CountdownStore (NumericStack K) F :=
  rowOuterEval r c d C
    (listCountPrefixResult r d base frame (List.replicate C true) (readUnaryFrame bits))

def framedRowsStepBound (L C : ℕ) : ℕ :=
  L * (framedNumericRowStepBound L C + 4) + 7 * L + 11

theorem framedRows_extra (r c d k : K) (hkr : k ≠ r) (hkc : k ≠ c) (hkd : k ≠ d)
    (base : K → List Bool) (frame : F) (C : ℕ) (bits : List Bool) :
    (framedRowsResult r c d base frame C bits).stk (.inr k) = base k := by
  unfold framedRowsResult
  rw [rowOuter_extra r c d k hkr hkc hkd]
  exact listCountPrefix_extra r d k hkr hkd base frame (List.replicate C true) (readUnaryFrame bits)

theorem framedRows_frame (r c d : K) (base : K → List Bool) (frame : F)
    (C : ℕ) (bits : List Bool) :
    (framedRowsResult r c d base frame C bits).state.1.1 = frame := by
  unfold framedRowsResult
  rw [rowOuter_frame]
  cases hp : readUnaryFrame bits <;> simp [listCountPrefixResult, hp, numericStore]

theorem framedRows_executes (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (base : K → List Bool) (hc : base c = []) (hd : base d = [])
    (frame : F) (guard flag : Bool) (C L : ℕ) (bits : List Bool) (hL : bits.length ≤ L) :
    ∃ n ≤ framedRowsStepBound L C,
      (framedRowsRoutine r c d).Executes
        (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] [])
        (framedRowsResult r c d base frame C bits) n ∧
      RowOuterInv c C L (framedRowsResult r c d base frame C bits) ∧
      (framedRowsResult r c d base frame C bits).state.1.2 = false ∧
      ((framedRowsResult r c d base frame C bits).state.2 = true →
        (framedRowsResult r c d base frame C bits).stk (.inr d) = []) := by
  obtain ⟨n, hn, hp⟩ := listCountPrefix_executes r d hrd base hd frame guard flag
    (List.replicate C true) bits
  let p := listCountPrefixResult r d base frame (List.replicate C true) (readUnaryFrame bits)
  have hi := framedRowsPrefix_invariant r c d hrc hcd base hc frame C L bits hL
  obtain ⟨m, hm, hrun, hInv, hguard, hclear⟩ := rowOuter_executes r c d hrc hrd hcd C L p hi
  have hcount : (p.stk (.inr d)).length ≤ L :=
    (listCountPrefix_counter_bound r d base hd frame (List.replicate C true) bits).trans hL
  have hmul := Nat.mul_le_mul_right (framedNumericRowStepBound L C + 4) hcount
  have hall := RoutineComposition.seq_executes (listCountPrefixRoutine r d) (rowOuterRoutine r c d) hp hrun
  refine ⟨n + m, ?_, hall, hInv, hguard, hclear⟩
  unfold framedRowsStepBound
  omega

theorem framedRows_observation (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (base : K → List Bool) (frame : F) (C : ℕ) (bits : List Bool) :
    numericListObservation r (framedRowsResult r c d base frame C bits) =
      (readFramedList (readFramedList (readSaturatedBinaryNatFrame C)) bits).map
        (fun p => (p.2, (encodeFramedList (encodeFramedList unaryFrame) p.1).reverse ++ base r)) := by
  unfold framedRowsResult
  rw [rowOuter_observation_eq r c d hrc hrd hcd]
  cases hp : readUnaryFrame bits with
  | none =>
      simp [rowOuterSpecification, listCountPrefixResult, hp, numericStore,
        numericStacks, readFramedList]
  | some p =>
      rcases p with ⟨n, tail⟩
      simp only [rowOuterSpecification, listCountPrefixResult, numericStore, numericStacks,
        ↓reduceIte, Function.update_same, Function.update_of_ne hrd, List.length_replicate,
        readFramedList, hp]
      cases hq : readMany (readFramedList (readSaturatedBinaryNatFrame C)) n tail with
      | none => simp [hq]
      | some q =>
          rcases q with ⟨rows, rest⟩
          have hv := readMany_length_exact (readFramedList (readSaturatedBinaryNatFrame C)) n tail rows rest hq
          simp [hq, encodeFramedList, hv, List.reverse_append, List.append_assoc]

theorem framedRows_record_bound (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (base : K → List Bool) (hc : base c = []) (hd : base d = []) (frame : F)
    (C L : ℕ) (bits : List Bool) (hL : bits.length ≤ L) :
    ((framedRowsResult r c d base frame C bits).stk (.inr r)).length ≤
      (base r).length + L ^ 2 * (C + 2) + 2 * L + 1 := by
  let p := listCountPrefixResult r d base frame (List.replicate C true) (readUnaryFrame bits)
  have hi := framedRowsPrefix_invariant r c d hrc hcd base hc frame C L bits hL
  have hloop := rowOuter_record_bound r c d hrc hrd hcd C L p hi
  have hprefix := listCountPrefix_record_bound r d hrd base frame (List.replicate C true) bits
  have hcount := (listCountPrefix_counter_bound r d base hd frame (List.replicate C true) bits).trans hL
  have hmul := Nat.mul_le_mul_right (L * (C + 2) + 1) hcount
  change ((rowOuterEval r c d C p).stk (.inr r)).length ≤ _
  nlinarith

/-- Complete TWO-LEVEL rows component, with exact original nested grammar,
    actual execution, both success-cleared counters and all-path storage. -/
theorem framedRows_executes_observed (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (base : K → List Bool) (hc : base c = []) (hd : base d = [])
    (frame : F) (guard flag : Bool) (C L : ℕ) (bits : List Bool) (hL : bits.length ≤ L) :
    ∃ n ≤ framedRowsStepBound L C,
      (framedRowsRoutine r c d).Executes
        (numericStore base (frame, guard) flag bits [] (List.replicate C true) [] [])
        (framedRowsResult r c d base frame C bits) n ∧
      numericListObservation r (framedRowsResult r c d base frame C bits) =
        (readFramedList (readFramedList (readSaturatedBinaryNatFrame C)) bits).map
          (fun p => (p.2, (encodeFramedList (encodeFramedList unaryFrame) p.1).reverse ++ base r)) ∧
      RowOuterInv c C L (framedRowsResult r c d base frame C bits) ∧
      ((framedRowsResult r c d base frame C bits).state.2 = true →
        (framedRowsResult r c d base frame C bits).stk (.inr c) = [] ∧
        (framedRowsResult r c d base frame C bits).stk (.inr d) = []) ∧
      ((framedRowsResult r c d base frame C bits).stk (.inr r)).length ≤
        (base r).length + L ^ 2 * (C + 2) + 2 * L + 1 := by
  obtain ⟨n, hn, he, hi, hg, hclear⟩ := framedRows_executes r c d hrc hrd hcd
    base hc hd frame guard flag C L bits hL
  refine ⟨n, hn, he, framedRows_observation r c d hrc hrd hcd base frame C bits, hi, ?_, ?_⟩
  · intro hok; exact ⟨hi.2 hok, hclear hok⟩
  · exact framedRows_record_bound r c d hrc hrd hcd base hc hd frame C L bits hL

/- Both initial counters must be empty. The outer and inner guards absorb
failures within this new rows attempt, with exact suffix observation on
success. This is NOT the complete source parser: three numeric headers
and their two different original caps, physical cap creation/switching,
trailing-input rejection, final reversal/tagging and cleanup of all failed
partial records/counters remain. Complete original constructor/checker,
closed compatible hardness and all kernel checks remain open. No runtime,
new model, biological closure or full-verification claim is introduced.
-/

end PolytomyReductionModel
