/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact observation agreement between the ACTUAL numeric-list loop's store
semantics and the ORIGINAL readMany grammar. Failure is observed as none;
successful source suffix and reversed unary-value log are both exact.
Partial failed stores still need the whole parser's later cleanup.
-/
import PolytomyNumericListLoop

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def numericReadLog (C : ℕ) : ℕ → List Bool → List Bool → Option (List Bool × List Bool)
  | 0, bits, record => some (bits, record)
  | n + 1, bits, record =>
      match readSaturatedBinaryNatFrame C bits with
      | none => none
      | some (a, rest) => numericReadLog C n rest ((unaryFrame a).reverse ++ record)

theorem numericReadLog_eq_readMany (C n : ℕ) : ∀ bits record,
    numericReadLog C n bits record =
      (readMany (readSaturatedBinaryNatFrame C) n bits).map
        (fun p => (p.2, (p.1.flatMap unaryFrame).reverse ++ record)) := by
  induction n with
  | zero => intro bits record; simp [numericReadLog, readMany]
  | succ n ih =>
      intro bits record
      cases hp : readSaturatedBinaryNatFrame C bits with
      | none => simp [numericReadLog, readMany, hp]
      | some p =>
          rcases p with ⟨a, rest⟩
          rw [numericReadLog, hp, ih]
          cases hq : readMany (readSaturatedBinaryNatFrame C) n rest with
          | none => simp [readMany, hp, hq]
          | some q =>
              rcases q with ⟨values, after⟩
              simp [readMany, hp, hq, List.flatMap_cons, List.reverse_append, List.append_assoc]

def numericListObservation (r : K) (s : CountdownStore (NumericStack K) F) :
    Option (List Bool × List Bool) :=
  if s.state.2 then some (s.stk (.inl .source), s.stk (.inr r)) else none

theorem numericObservation_peek (r c : K) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (countdownPeek (.inr c) s) = numericListObservation r s := by rfl
theorem numericObservation_reset (r : K) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (countdownReset s) = numericListObservation r s := by rfl

theorem countdownLoop_failed (counter : K)
    (f : CountdownStore K F → CountdownStore K F) (fuel : ℕ)
    (s : CountdownStore K F) (h : s.state.2 = false) :
    countdownLoopEval counter f fuel s = s := by
  cases fuel with
  | zero => rfl
  | succ n => simp [countdownLoopEval, countdownGuard, h]

/-- No validity or final-success promise is used. The initial physical
    count determines how many values are required; a failed reader stops.
    Counter symbols may be arbitrary here because only length is used. -/
theorem numericLoop_observation (r c : K) (hrc : r ≠ c) (C n : ℕ) :
    ∀ s : CountdownStore (NumericStack K) F,
      (s.stk (.inr c)).length = n → s.state.2 = true →
      numericListObservation r
        (countdownLoopEval (.inr c) (numericRecordEval r C) n (countdownPeek (.inr c) s)) =
      numericReadLog C n (s.stk (.inl .source)) (s.stk (.inr r)) := by
  induction n with
  | zero =>
      intro s hlen hok
      simp [countdownLoopEval, numericObservation_peek, numericListObservation, hok, numericReadLog]
  | succ n ih =>
      intro s hlen hok
      have hhead : (s.stk (.inr c)).head?.isSome = true := by
        cases hw : s.stk (.inr c) with
        | nil => simp [hw] at hlen
        | cons b xs => rfl
      have hg : countdownGuard (countdownPeek (.inr c) s).state = true := by
        simp [countdownGuard, countdownPeek, countdownPeekOp, Op.apply, hhead, hok]
      let p := countdownPop (.inr c) (countdownPeek (.inr c) s)
      have hsrc : p.stk (.inl .source) = s.stk (.inl .source) := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply]
      have hrec : p.stk (.inr r) = s.stk (.inr r) := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply, hrc]
      have htail : p.stk (.inr c) = (s.stk (.inr c)).tail := by
        simp [p, countdownPop, countdownPopOp, countdownPeek, countdownPeekOp, Op.apply]
      have hplen : (p.stk (.inr c)).length = n := by
        rw [htail]
        cases hw : s.stk (.inr c) with
        | nil => simp [hw] at hlen
        | cons b xs =>
            simp only [hw, List.length_cons] at hlen
            simp only [List.tail_cons]
            omega
      rw [countdownLoopEval, hg]
      simp only [↓reduceIte]
      change numericListObservation r
        (countdownLoopEval (.inr c) (numericRecordEval r C) n
          (countdownPeek (.inr c) (numericRecordEval r C p))) = _
      cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
      | none =>
          have hf : (numericRecordEval r C p).state.2 = false := by
            simp [numericRecordEval, hsrc, hp, numericRecordResult, numericStore]
          rw [countdownLoop_failed (.inr c) (numericRecordEval r C) n
            (countdownPeek (.inr c) (numericRecordEval r C p)) hf,
            numericObservation_peek]
          simp [numericListObservation, hf, numericReadLog, hp]
      | some q =>
          rcases q with ⟨a, rest⟩
          have hflag : (numericRecordEval r C p).state.2 = true := by
            simp [numericRecordEval, hsrc, hp, numericRecordResult, numericStore]
          have hcounter : (numericRecordEval r C p).stk (.inr c) = p.stk (.inr c) :=
            numericRecord_preserves_counter r c hrc (fun k => p.stk (.inr k)) p.state.1.1 C
              (readSaturatedBinaryNatFrame C (p.stk (.inl .source)))
          have hsource : (numericRecordEval r C p).stk (.inl .source) = rest := by
            simp [numericRecordEval, hsrc, hp, numericRecordResult, numericStore, numericStacks]
          have hrecord : (numericRecordEval r C p).stk (.inr r) =
              (unaryFrame a).reverse ++ s.stk (.inr r) := by
            simp [numericRecordEval, hsrc, hp, numericRecordResult, numericStore, numericStacks, hrec]
          have hi := ih (numericRecordEval r C p) (by rw [hcounter]; exact hplen) hflag
          simpa only [hsource, hrecord, numericReadLog, hp] using hi

def numericListSpecification (r c : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    Option (List Bool × List Bool) :=
  if s.state.2 then
    (readMany (readSaturatedBinaryNatFrame C) (s.stk (.inr c)).length
      (s.stk (.inl .source))).map
        (fun p => (p.2, (p.1.flatMap unaryFrame).reverse ++ s.stk (.inr r)))
  else none

/-- Exact equality on arbitrary source words, including failed frames,
    successful zeros, zero count and an already-failed incoming state. -/
theorem numericList_observation_eq (r c : K) (hrc : r ≠ c) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (numericListEval r c C s) = numericListSpecification r c C s := by
  change numericListObservation r (countdownReset
    (countdownLoopEval (.inr c) (numericRecordEval r C) (s.stk (.inr c)).length
      (countdownPeek (.inr c) s))) = _
  rw [numericObservation_reset]
  cases hflag : s.state.2 with
  | false =>
      rw [countdownLoop_failed (.inr c) (numericRecordEval r C) (s.stk (.inr c)).length
        (countdownPeek (.inr c) s) hflag, numericObservation_peek]
      simp [numericListSpecification, numericListObservation, hflag]
  | true =>
      rw [numericLoop_observation r c hrc C (s.stk (.inr c)).length s rfl hflag,
        numericReadLog_eq_readMany]
      simp only [numericListSpecification, hflag, ↓reduceIte]

/-- The original grammar observation is now joined to the ACTUAL routine
    execution and partial-store bound, not to a new abstract cost model. -/
theorem numericList_executes_observed (r c : K) (hrc : r ≠ c) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (h : NumericLoopInv C L s) :
    ∃ n ≤ (s.stk (.inr c)).length * (numericRecordStepBound L C + 3) + 3,
      (numericListRoutine r c).Executes s (numericListEval r c C s) n ∧
      numericListObservation r (numericListEval r c C s) = numericListSpecification r c C s ∧
      NumericLoopInv C L (numericListEval r c C s) ∧
      ((numericListEval r c C s).stk (.inr r)).length ≤
        (s.stk (.inr r)).length + (s.stk (.inr c)).length * (C + 1) := by
  obtain ⟨n, hn, hr, hi, hg, hc⟩ := numericList_executes r c hrc C L s h
  exact ⟨n, hn, hr, numericList_observation_eq r c hrc C s, hi,
    numericList_record_length r c hrc C s⟩

/- This closes the numeric-list component's hand/source-proposal grammar
correspondence, not the full nested-source normalizer. The list count has
not yet been read/copied by this routine, and no complete-input suffix test
is made here. Outer rows, three headers and caps, final record reversal/
tagging and cleanup of every failed partial store remain. Complete original
constructor/checker, closed compatible encoded hardness and every kernel
check remain open. No runtime, new model or broader closure is claimed.
-/

end PolytomyReductionModel
