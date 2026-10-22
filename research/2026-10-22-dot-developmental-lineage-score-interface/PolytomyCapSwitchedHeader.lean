/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual third-header pattern: exchange small/large physical caps, execute
a failure-absorbing ORIGINAL numeric reader, then restore both caps even
if parsing failed. This is not cap creation or the whole source parser.
-/
import PolytomyGuardedNumericHeader

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

abbrev numericCapSwap (b t : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  capExchangeRoutine (.inl .cap : NumericStack K) (.inr b) (.inr t)
abbrev numericCapSwapEval (b t : K) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  capExchangeEval (.inl .cap : NumericStack K) (.inr b) (.inr t) s

theorem numericCapSwap_observation (r b t : K) (hrb : r ≠ b) (hrt : r ≠ t)
    (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (numericCapSwapEval b t s) = numericListObservation r s := by
  have hsrc := capExchange_outside (.inl .cap : NumericStack K) (.inr b) (.inr t) (.inl .source)
    (by simp) (by simp) (by simp) s
  have hrec := capExchange_outside (.inl .cap : NumericStack K) (.inr b) (.inr t) (.inr r)
    (by simp) (by simpa using hrb) (by simpa using hrt) s
  change (if s.state.2 then some ((numericCapSwapEval b t s).stk (.inl .source),
    (numericCapSwapEval b t s).stk (.inr r)) else none) = _
  rw [hsrc, hrec]
  rfl

theorem numericCapSwap_invariant (b t : K) (hbt : b ≠ t) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s)
    (hb : s.stk (.inr b) = List.replicate D true) (ht : s.stk (.inr t) = []) :
    NumericLoopInv D L (numericCapSwapEval b t s) := by
  have he := capExchange_effect (.inl .cap : NumericStack K) (.inr b) (.inr t)
    (by simp) (by simp) (by simpa using hbt) s ht
  change NumericLoopInv D L (capExchangeEval (.inl .cap : NumericStack K) (.inr b) (.inr t) s)
  rw [he]
  have ha := hs.2.2.2.1
  simpa [NumericLoopInv, capExchangeResult, hb, ha] using hs

theorem numericCapSwap_executes (b t : K) (hbt : b ≠ t) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s)
    (hb : s.stk (.inr b) = List.replicate D true) (ht : s.stk (.inr t) = []) :
    (numericCapSwap (F := F) b t).Executes s (numericCapSwapEval b t s) (2 * C + D + 3) ∧
      NumericLoopInv D L (numericCapSwapEval b t s) ∧
      (numericCapSwapEval b t s).stk (.inr b) = List.replicate C true ∧
      (numericCapSwapEval b t s).stk (.inr t) = [] := by
  have h := capExchange_unary_executes (.inl .cap : NumericStack K) (.inr b) (.inr t)
    (by simp) (by simp) (by simpa using hbt) s C D hs.2.2.2.1 hb ht
  exact ⟨h.1, numericCapSwap_invariant b t hbt C D L s hs hb ht, h.2.2.1, h.2.2.2.1⟩

def capSwitchedHeaderRoutine (r c b t : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (numericCapSwap b t)
    (RoutineComposition.seq (guardedNumericRoutine r c) (numericCapSwap b t))

def capSwitchedHeaderEval (r b t : K) (D : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  numericCapSwapEval b t (guardedNumericEval r D (numericCapSwapEval b t s))

def capSwitchedHeaderStepBound (L C D : ℕ) : ℕ :=
  numericRecordStepBound L D + 3 * C + 3 * D + 7

theorem capSwitchedHeader_executes (r c b t : K) (hrc : r ≠ c) (hrb : r ≠ b)
    (hrt : r ≠ t) (hbt : b ≠ t) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s)
    (hb : s.stk (.inr b) = List.replicate D true) (ht : s.stk (.inr t) = []) :
    ∃ n ≤ capSwitchedHeaderStepBound L C D,
      (capSwitchedHeaderRoutine r c b t).Executes s (capSwitchedHeaderEval r b t D s) n ∧
      NumericLoopInv C L (capSwitchedHeaderEval r b t D s) ∧
      (capSwitchedHeaderEval r b t D s).stk (.inr b) = List.replicate D true ∧
      (capSwitchedHeaderEval r b t D s).stk (.inr t) = [] := by
  let u := numericCapSwapEval b t s
  obtain ⟨h1, hi1, hb1, ht1⟩ := numericCapSwap_executes b t hbt C D L s hs hb ht
  obtain ⟨n, hn, h2, hi2⟩ := guardedNumeric_executes r c hrc D L u hi1
  let v := guardedNumericEval r D u
  have hb2 : v.stk (.inr b) = List.replicate C true :=
    (guardedNumeric_extra r b (Ne.symm hrb) D u).trans hb1
  have ht2 : v.stk (.inr t) = [] := (guardedNumeric_extra r t (Ne.symm hrt) D u).trans ht1
  obtain ⟨h3, hi3, hb3, ht3⟩ := numericCapSwap_executes b t hbt D C L v hi2 hb2 ht2
  have h23 := RoutineComposition.seq_executes (guardedNumericRoutine r c) (numericCapSwap b t) h2 h3
  have hall := RoutineComposition.seq_executes (numericCapSwap b t)
    (RoutineComposition.seq (guardedNumericRoutine r c) (numericCapSwap b t)) h1 h23
  refine ⟨(2 * C + D + 3) + (n + (2 * D + C + 3)), ?_, hall, hi3, hb3, ht3⟩
  unfold capSwitchedHeaderStepBound
  omega

theorem capSwitchedHeader_observation (r b t : K) (hrb : r ≠ b) (hrt : r ≠ t)
    (D : ℕ) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (capSwitchedHeaderEval r b t D s) =
      if s.state.2 then
        (readSaturatedBinaryNatFrame D (s.stk (.inl .source))).map
          (fun p => (p.2, (unaryFrame p.1).reverse ++ s.stk (.inr r)))
      else none := by
  unfold capSwitchedHeaderEval
  rw [numericCapSwap_observation r b t hrb hrt, guardedNumeric_observation]
  have hsrc := capExchange_outside (.inl .cap : NumericStack K) (.inr b) (.inr t) (.inl .source)
    (by simp) (by simp) (by simp) s
  have hrec := capExchange_outside (.inl .cap : NumericStack K) (.inr b) (.inr t) (.inr r)
    (by simp) (by simpa using hrb) (by simpa using hrt) s
  change (if s.state.2 then
    (readSaturatedBinaryNatFrame D ((numericCapSwapEval b t s).stk (.inl .source))).map
      (fun p => (p.2, (unaryFrame p.1).reverse ++ (numericCapSwapEval b t s).stk (.inr r))) else none) = _
  rw [hsrc, hrec]

theorem capSwitchedHeader_extra (r b t k : K) (hkr : k ≠ r) (hkb : k ≠ b) (hkt : k ≠ t)
    (D : ℕ) (s : CountdownStore (NumericStack K) F) :
    (capSwitchedHeaderEval r b t D s).stk (.inr k) = s.stk (.inr k) := by
  unfold capSwitchedHeaderEval
  rw [capExchange_outside (.inl .cap : NumericStack K) (.inr b) (.inr t) (.inr k)
    (by simp) (by simpa using hkb) (by simpa using hkt)]
  rw [guardedNumeric_extra r k hkr]
  exact capExchange_outside (.inl .cap : NumericStack K) (.inr b) (.inr t) (.inr k)
    (by simp) (by simpa using hkb) (by simpa using hkt) s

theorem capSwitchedHeader_record_bound (r b t : K) (hrb : r ≠ b) (hrt : r ≠ t)
    (D : ℕ) (s : CountdownStore (NumericStack K) F) :
    ((capSwitchedHeaderEval r b t D s).stk (.inr r)).length ≤ (s.stk (.inr r)).length + D + 1 := by
  have h := guardedNumeric_record_bound r D (numericCapSwapEval b t s)
  unfold capSwitchedHeaderEval
  rw [capExchange_outside (.inl .cap : NumericStack K) (.inr b) (.inr t) (.inr r)
    (by simp) (by simpa using hrb) (by simpa using hrt)]
  simpa only [capExchange_outside (.inl .cap : NumericStack K) (.inr b) (.inr t) (.inr r)
    (by simp) (by simpa using hrb) (by simpa using hrt) s] using h

/- The large-cap header now restores both PHYSICAL caps and empty swap
scratch on success or failure. Public flags are preserved by switching,
and the guarded read absorbs an already failed prefix. The observation is
the original large-cap numeric reader, not an approximation or shrinking
cap. Actual cap creation, three-header/rows assembly, complete-input finish,
record reversal/tagging/all-path cleanup and full constructor/checker/
hardness/kernel closure remain open. No runtime or changed biological model.
-/

end PolytomyReductionModel
