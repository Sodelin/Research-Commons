/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Concrete operational instantiation of the physical countdown for the
original numeric-reader/emitter body. Its invariant covers failing and
partial states, and its record-storage bound does not assume final parse
success. Exact agreement with the full nested grammar is still separate.
-/
import PolytomyNumericRecordBody

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def NumericLoopInv (C L : ℕ) (s : CountdownStore (NumericStack K) F) : Prop :=
  s.stk (.inl .payload) = [] ∧ s.stk (.inl .work) = [] ∧
    s.stk (.inl .output) = [] ∧ s.stk (.inl .cap) = List.replicate C true ∧
    (s.stk (.inl .source)).length ≤ L

def numericRecordEval (r : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  numericRecordResult r (fun k => s.stk (.inr k)) s.state.1.1 C
    (readSaturatedBinaryNatFrame C (s.stk (.inl .source)))

theorem numericLoop_reconstruct (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (h : NumericLoopInv C L s) :
    s = numericStore (fun k => s.stk (.inr k)) (s.state.1.1, s.state.1.2) s.state.2
      (s.stk (.inl .source)) [] (List.replicate C true) [] [] := by
  apply countdownStore_ext
  · rcases s.state with ⟨⟨f, g⟩, flag⟩; rfl
  · funext j
    rcases h with ⟨hp, hw, ho, hc, hl⟩
    cases j with
    | inl p => cases p <;> simp [numericStore, numericStacks, hp, hw, ho, hc]
    | inr k => rfl

theorem readSaturated_remaining (C : ℕ) (bits : List Bool) (a : ℕ) (rest : List Bool)
    (h : readSaturatedBinaryNatFrame C bits = some (a, rest)) : rest.length ≤ bits.length := by
  rw [readSaturatedBinaryNatFrame_eq] at h
  cases hb : readBinaryNatFrame bits with
  | none => simp [hb] at h
  | some p =>
      rcases p with ⟨n, tail⟩
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      simpa only [h.2] using readBinaryNatFrame_remaining bits n tail hb

theorem readSaturated_value_le (C : ℕ) (bits : List Bool) (a : ℕ) (rest : List Bool)
    (h : readSaturatedBinaryNatFrame C bits = some (a, rest)) : a ≤ C := by
  rw [readSaturatedBinaryNatFrame_eq] at h
  cases hb : readBinaryNatFrame bits with
  | none => simp [hb] at h
  | some p =>
      rcases p with ⟨n, tail⟩
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact min_le_right _ _

theorem numericRecordEval_invariant (r : K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (h : NumericLoopInv C L s) :
    NumericLoopInv C L (numericRecordEval r C s) := by
  cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
  | none => simp [numericRecordEval, hp, NumericLoopInv, numericRecordResult, numericStore, numericStacks]
  | some p =>
      rcases p with ⟨a, rest⟩
      have hl := (readSaturated_remaining C (s.stk (.inl .source)) a rest hp).trans h.2.2.2.2
      simpa [numericRecordEval, hp, NumericLoopInv,
        numericRecordResult, numericStore, numericStacks] using hl

theorem numericRecordStepBound_mono (inner outer C : ℕ) (h : inner ≤ outer) :
    numericRecordStepBound inner C ≤ numericRecordStepBound outer C := by
  have hm := Nat.mul_le_mul_right C (Nat.mul_le_mul_left 6 h)
  unfold numericRecordStepBound
  omega

def numericListContract (r c : K) (hrc : r ≠ c) (C L : ℕ) :
    CountdownContract (.inr c : NumericStack K) (numericRecordRoutine r c)
      (numericRecordEval r C) (NumericLoopInv C L) (numericRecordStepBound L C) where
  peek_closed s hs := by
    simpa only [NumericLoopInv, countdownPeek, countdownPeekOp, Op.apply] using hs
  pop_closed s hs hg := by
    simpa [NumericLoopInv, countdownPop, countdownPopOp, Op.apply] using hs
  body_closed s hs := numericRecordEval_invariant r C L s hs
  reset_closed s hs := by
    simpa only [NumericLoopInv, countdownReset, countdownResetOp, Op.apply] using hs
  counter_preserved s hs :=
    numericRecord_preserves_counter r c hrc (fun k => s.stk (.inr k)) s.state.1.1 C
      (readSaturatedBinaryNatFrame C (s.stk (.inl .source)))
  body_executes s hs := by
    obtain ⟨n, hn, he⟩ := numericRecord_executes r c hrc C (s.stk (.inl .source))
      (fun k => s.stk (.inr k)) s.state.1.1 s.state.1.2 s.state.2
    have hb := numericRecordStepBound_mono (s.stk (.inl .source)).length L C hs.2.2.2.2
    refine ⟨n, hn.trans hb, ?_⟩
    rw [← numericLoop_reconstruct C L s hs] at he
    exact he

def numericListRoutine (r c : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  countdownRoutine (.inr c) (numericRecordRoutine r c)

def numericListEval (r c : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  countdownEval (.inr c) (numericRecordEval r C) s

/-- The supplied-body premise is discharged by the concrete reader plus
    emitter. No final-success assumption is made. The routine stops before
    making another numeric attempt after its success flag becomes false. -/
theorem numericList_executes (r c : K) (hrc : r ≠ c) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (h : NumericLoopInv C L s) :
    ∃ n ≤ (s.stk (.inr c)).length * (numericRecordStepBound L C + 3) + 3,
      (numericListRoutine r c).Executes s (numericListEval r c C s) n ∧
      NumericLoopInv C L (numericListEval r c C s) ∧
      (numericListEval r c C s).state.1.2 = false ∧
      ((numericListEval r c C s).state.2 = true →
        (numericListEval r c C s).stk (.inr c) = []) := by
  exact countdownRoutine_executes (.inr c) (numericRecordRoutine r c)
    (numericRecordEval r C) (NumericLoopInv C L) (numericRecordStepBound L C)
    (numericListContract r c hrc C L) s h

theorem numericRecordEval_record_length (r : K) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    ((numericRecordEval r C s).stk (.inr r)).length ≤ (s.stk (.inr r)).length + (C + 1) := by
  cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
  | none => simp [numericRecordEval, hp, numericRecordResult, numericStore, numericStacks]
  | some p =>
      rcases p with ⟨a, rest⟩
      have ha := readSaturated_value_le C (s.stk (.inl .source)) a rest hp
      simp only [numericRecordEval, hp, numericRecordResult, numericStore, numericStacks,
        Function.update_same, List.length_append, List.length_reverse, unaryFrame,
        List.length_replicate, List.length_singleton]
      omega

/-- Boundary storage during a partial/failed loop is bounded, independently
    of the successful normal form's sharper final-length theorem. -/
theorem numericLoop_record_length (r c : K) (hrc : r ≠ c) (C fuel : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    ((countdownLoopEval (.inr c) (numericRecordEval r C) fuel s).stk (.inr r)).length ≤
      (s.stk (.inr r)).length + fuel * (C + 1) := by
  induction fuel generalizing s with
  | zero => simp [countdownLoopEval]
  | succ fuel ih =>
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          let u := countdownPeek (.inr c) (numericRecordEval r C (countdownPop (.inr c) s))
          have hi := ih u
          have hb := numericRecordEval_record_length r C (countdownPop (.inr c) s)
          have hpop : (countdownPop (.inr c) s).stk (.inr r) = s.stk (.inr r) := by
            simp [countdownPop, countdownPopOp, Op.apply, hrc]
          rw [hpop] at hb
          have hpeek : (u.stk (.inr r)).length =
              ((numericRecordEval r C (countdownPop (.inr c) s)).stk (.inr r)).length := rfl
          rw [hpeek] at hi
          simp only [countdownLoopEval, hg, ↓reduceIte]
          change ((countdownLoopEval (.inr c) (numericRecordEval r C) fuel u).stk (.inr r)).length ≤ _
          nlinarith

theorem numericList_record_length (r c : K) (hrc : r ≠ c) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    ((numericListEval r c C s).stk (.inr r)).length ≤
      (s.stk (.inr r)).length + (s.stk (.inr c)).length * (C + 1) := by
  exact numericLoop_record_length r c hrc C (s.stk (.inr c)).length (countdownPeek (.inr c) s)

/- This packet gives a concrete operational inner loop and a partial-store
bound, but does not silently identify its store semantics with readMany.
That exact original-grammar observation theorem, list-count reader/copy,
outer rows, headers/caps, trailing-input rejection, full cleanup and final
record reversal are the next obligations. Whole constructor/checker,
closed compatible encoded hardness and all kernel checks remain open.
-/

end PolytomyReductionModel
