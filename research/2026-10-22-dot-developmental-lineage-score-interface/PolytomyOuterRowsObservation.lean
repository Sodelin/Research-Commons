/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact original repeated-row observation for the actual guarded outer loop.
The physical outer count is supplied separately; reading its prefix and
the full-source headers/completion/cleanup remain separate obligations.
-/
import PolytomyGuardedRowOuterLoop

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem numericObservation_none_iff (r : K) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r s = none ↔ s.state.2 = false := by
  cases h : s.state.2 <;> simp [numericListObservation, h]

theorem numericObservation_some_iff (r : K) (s : CountdownStore (NumericStack K) F)
    (rest record : List Bool) :
    numericListObservation r s = some (rest, record) ↔
      s.state.2 = true ∧ s.stk (.inl .source) = rest ∧ s.stk (.inr r) = record := by
  cases h : s.state.2 <;> simp [numericListObservation, h, Prod.mk.injEq]

theorem guardedRow_observation (r c : K) (hrc : r ≠ c) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (guardedRowEval r c C s) =
      if s.state.2 then
        (readFramedList (readSaturatedBinaryNatFrame C) (s.stk (.inl .source))).map
          (fun p => (p.2, (encodeFramedList unaryFrame p.1).reverse ++ s.stk (.inr r)))
      else none := by
  cases hflag : s.state.2 with
  | false => simp [guardedRowEval, hflag, numericObservation_reset, numericListObservation]
  | true =>
      simpa only [guardedRowEval, hflag, ↓reduceIte] using
        framedNumericRow_observation r c hrc (fun k => s.stk (.inr k)) s.state.1.1 C
          (s.stk (.inl .source))

def rowsReadLog (C : ℕ) : ℕ → List Bool → List Bool → Option (List Bool × List Bool)
  | 0, bits, record => some (bits, record)
  | n + 1, bits, record =>
      match readFramedList (readSaturatedBinaryNatFrame C) bits with
      | none => none
      | some (row, rest) => rowsReadLog C n rest ((encodeFramedList unaryFrame row).reverse ++ record)

theorem rowsReadLog_eq_readMany (C n : ℕ) : ∀ bits record,
    rowsReadLog C n bits record =
      (readMany (readFramedList (readSaturatedBinaryNatFrame C)) n bits).map
        (fun p => (p.2, (p.1.flatMap (encodeFramedList unaryFrame)).reverse ++ record)) := by
  induction n with
  | zero => intro bits record; simp [rowsReadLog, readMany]
  | succ n ih =>
      intro bits record
      cases hp : readFramedList (readSaturatedBinaryNatFrame C) bits with
      | none => simp [rowsReadLog, readMany, hp]
      | some p =>
          rcases p with ⟨row, rest⟩
          rw [rowsReadLog, hp, ih]
          cases hq : readMany (readFramedList (readSaturatedBinaryNatFrame C)) n rest with
          | none => simp [readMany, hp, hq]
          | some q =>
              rcases q with ⟨rows, after⟩
              simp [readMany, hp, hq, List.flatMap_cons, List.reverse_append, List.append_assoc]

/-- Pure store observation has this equality even outside the operational
    invariant. Actual routine execution uses the preceding RowOuterInv;
    the two are explicitly joined in the final theorem below. -/
theorem rowOuterLoop_observation (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C n : ℕ) : ∀ s : CountdownStore (NumericStack K) F,
      (s.stk (.inr d)).length = n → s.state.2 = true →
      numericListObservation r
        (countdownLoopEval (.inr d) (guardedRowEval r c C) n (countdownPeek (.inr d) s)) =
      rowsReadLog C n (s.stk (.inl .source)) (s.stk (.inr r)) := by
  induction n with
  | zero =>
      intro s hlen hok
      simp [countdownLoopEval, numericObservation_peek, numericListObservation, hok, rowsReadLog]
  | succ n ih =>
      intro s hlen hok
      have hhead : (s.stk (.inr d)).head?.isSome = true := by
        cases hw : s.stk (.inr d) with
        | nil => simp [hw] at hlen
        | cons b xs => rfl
      have hg : countdownGuard (countdownPeek (.inr d) s).state = true := by
        simp [countdownGuard, countdownPeek, countdownPeekOp, Op.apply, hhead, hok]
      let p := countdownPop (.inr d) (countdownPeek (.inr d) s)
      have hsrc : p.stk (.inl .source) = s.stk (.inl .source) := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply]
      have hrec : p.stk (.inr r) = s.stk (.inr r) := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply, hrd]
      have hpflag : p.state.2 = true := hok
      have htail : p.stk (.inr d) = (s.stk (.inr d)).tail := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply]
      have hplen : (p.stk (.inr d)).length = n := by
        rw [htail]
        cases hw : s.stk (.inr d) with
        | nil => simp [hw] at hlen
        | cons b xs => simp only [hw, List.length_cons] at hlen; simp only [List.tail_cons]; omega
      have hb := guardedRow_observation r c hrc C p
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      change numericListObservation r
        (countdownLoopEval (.inr d) (guardedRowEval r c C) n
          (countdownPeek (.inr d) (guardedRowEval r c C p))) = _
      cases hp : readFramedList (readSaturatedBinaryNatFrame C) (s.stk (.inl .source)) with
      | none =>
          have ho : numericListObservation r (guardedRowEval r c C p) = none := by
            simpa only [hpflag, ↓reduceIte, hsrc, hp, Option.map_none] using hb
          have hf := (numericObservation_none_iff r _).mp ho
          rw [countdownLoop_failed (.inr d) (guardedRowEval r c C) n
            (countdownPeek (.inr d) (guardedRowEval r c C p)) hf, numericObservation_peek, ho]
          simp [rowsReadLog, hp]
      | some q =>
          rcases q with ⟨row, rest⟩
          have ho : numericListObservation r (guardedRowEval r c C p) =
              some (rest, (encodeFramedList unaryFrame row).reverse ++ s.stk (.inr r)) := by
            simpa only [hpflag, ↓reduceIte, hsrc, hp, Option.map_some, hrec] using hb
          obtain ⟨hflag, hsource, hrecord⟩ := (numericObservation_some_iff r _ _ _).mp ho
          have hcounter := guardedRow_extra r c d (Ne.symm hrd) (Ne.symm hcd) C p
          have hi := ih (guardedRowEval r c C p) (by rw [hcounter]; exact hplen) hflag
          simpa only [hsource, hrecord, rowsReadLog, hp] using hi

def rowOuterSpecification (r d : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    Option (List Bool × List Bool) :=
  if s.state.2 then
    (readMany (readFramedList (readSaturatedBinaryNatFrame C)) (s.stk (.inr d)).length
      (s.stk (.inl .source))).map
        (fun p => (p.2, (p.1.flatMap (encodeFramedList unaryFrame)).reverse ++ s.stk (.inr r)))
  else none

theorem rowOuter_observation_eq (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (rowOuterEval r c d C s) = rowOuterSpecification r d C s := by
  change numericListObservation r (countdownReset
    (countdownLoopEval (.inr d) (guardedRowEval r c C) (s.stk (.inr d)).length
      (countdownPeek (.inr d) s))) = _
  rw [numericObservation_reset]
  cases hflag : s.state.2 with
  | false =>
      rw [countdownLoop_failed (.inr d) (guardedRowEval r c C) (s.stk (.inr d)).length
        (countdownPeek (.inr d) s) hflag, numericObservation_peek]
      simp [rowOuterSpecification, numericListObservation, hflag]
  | true =>
      rw [rowOuterLoop_observation r c d hrc hrd hcd C (s.stk (.inr d)).length s rfl hflag,
        rowsReadLog_eq_readMany]
      simp only [rowOuterSpecification, hflag, ↓reduceIte]

theorem rowOuter_executes_observed (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C L : ℕ) (s : CountdownStore (NumericStack K) F) (hs : RowOuterInv c C L s) :
    ∃ n ≤ (s.stk (.inr d)).length * (framedNumericRowStepBound L C + 4) + 3,
      (rowOuterRoutine r c d).Executes s (rowOuterEval r c d C s) n ∧
      numericListObservation r (rowOuterEval r c d C s) = rowOuterSpecification r d C s ∧
      RowOuterInv c C L (rowOuterEval r c d C s) ∧
      ((rowOuterEval r c d C s).stk (.inr r)).length ≤
        (s.stk (.inr r)).length + (s.stk (.inr d)).length * (L * (C + 2) + 1) := by
  obtain ⟨n, hn, he, hi, hg, hc⟩ := rowOuter_executes r c d hrc hrd hcd C L s hs
  exact ⟨n, hn, he, rowOuter_observation_eq r c d hrc hrd hcd C s, hi,
    rowOuter_record_bound r c d hrc hrd hcd C L s hs⟩

/- This is exact repeated ORIGINAL row reading, not an assumed outer
grammar equivalence. The initial outer count is still supplied physically;
its unary prefix must be read/copied and logged next. Source headers/caps,
trailing-suffix rejection, record reversal/tagging, failure cleanup, whole
constructor/checker, closed encoded hardness and all kernel checks remain.
-/

end PolytomyReductionModel
