/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Join actual complete-input range scan with destructive declared-count
equality. Successful parse supplies exact physical headerM/savedCount;
malformed parsing never enters the comparison. Coverage is still separate.
-/
import PolytomyOriginalRangePass

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def originalCountRangeRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState Bool) :=
  RoutineComposition.seq originalRangeRoutine
    (guardedDeclaredCountRoutine (.inr .headerM) (.inr .savedCount))

def originalCountRangeEval (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  guardedDeclaredCountEval (.inr .headerM) (.inr .savedCount) (originalRangeEval s)

def countRangeSpec (bits : List Bool) : Bool :=
  match readNormalizedSource bits with
  | none => false
  | some R => decide (R.rows.length = R.declaredM) && R.rows.flatten.all (fun a => decide (a < R.N))

theorem originalRange_success_data (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) (R : RawMSSCRecord)
    (hp : readNormalizedSource (s.stk (.inr .original)) = some R) :
    (originalRangeEval s).state.2 = true ∧
      (originalRangeEval s).state.1.1 = R.rows.flatten.all (fun a => decide (a < R.N)) ∧
      (originalRangeEval s).stk (.inr .headerM) = List.replicate R.declaredM true ∧
      (originalRangeEval s).stk (.inr .savedCount) = List.replicate R.rows.length true := by
  have ho := originalRange_observation L s hs hq
  have hf : (originalRangeEval s).state.2 = true := by
    cases hx : (originalRangeEval s).state.2 <;> simp [unaryScanCompleteObservation, hx, hp] at ho ⊢
  have hacc : (originalRangeEval s).state.1.1 = R.rows.flatten.all (fun a => decide (a < R.N)) := by
    simpa [unaryScanCompleteObservation, hf, hp] using ho
  obtain ⟨hN, hi, hc, hd, hz, hqueries⟩ := validationPrepared_ready L s hs hq
  obtain ⟨hNeq, hflag, hsrc, hm⟩ := validationPrepared_values L s hs R hp
  have hrows : readFramedList (readFramedList readUnaryFrame) ((validationPrepared s).stk (.inl .source)) = some (R.rows, []) := by
    rw [hsrc]
    have hrow : ∀ row rest, readFramedList readUnaryFrame (encodeFramedList unaryFrame row ++ rest) = some (row, rest) :=
      readFramedList_encode _ _ readUnaryFrame_encode
    simpa only [List.append_nil] using readFramedList_encode (encodeFramedList unaryFrame)
      (readFramedList readUnaryFrame) hrow R.rows []
  have hsaved := unaryRows_saved_length_on_success scanRowsPorts .less (fun a b => a && b)
    (validationN s) L (validationPrepared s) hi hc hz hflag R.rows [] hrows
  have hmPres := unaryRows_extra scanRowsPorts .headerM (by decide) (by decide) (by decide)
    .less (fun a b => a && b) (validationN s) L (validationPrepared s) hi hc
  exact ⟨hf, hacc, hmPres.trans hm, hsaved⟩

theorem originalRange_failure (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = [])
    (hp : readNormalizedSource (s.stk (.inr .original)) = none) :
    (originalRangeEval s).state.2 = false := by
  have ho := originalRange_observation L s hs hq
  cases hf : (originalRangeEval s).state.2 <;> simp [unaryScanCompleteObservation, hf, hp] at ho ⊢

theorem originalCountRange_verdict (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) :
    (originalCountRangeEval s).state.2 = countRangeSpec (s.stk (.inr .original)) := by
  rw [originalCountRangeEval, guardedDeclaredCount_verdict _ _ (by decide)]
  cases hp : readNormalizedSource (s.stk (.inr .original)) with
  | none => simp [countRangeSpec, hp, originalRange_failure L s hs hq hp]
  | some R =>
      obtain ⟨hf, hacc, hm, hz⟩ := originalRange_success_data L s hs hq R hp
      simp only [hf, hacc, hm, hz, List.length_replicate, Bool.true_and, countRangeSpec, hp]
      by_cases heq : R.rows.length = R.declaredM <;>
        cases hbound : R.rows.flatten.all (fun a => decide (a < R.N)) <;> simp_all [eq_comm]

theorem originalCountRange_executes (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) :
    ∃ n ≤ originalRangeBound L + L + 3,
      originalCountRangeRoutine.Executes s (originalCountRangeEval s) n := by
  obtain ⟨n, hn, hrange⟩ := originalRange_executes L s hs hq
  have hwords : (originalRangeEval s).state.2 = true →
      IsUnaryWord ((originalRangeEval s).stk (.inr .headerM)) ∧
      IsUnaryWord ((originalRangeEval s).stk (.inr .savedCount)) := by
    intro hf
    cases hp : readNormalizedSource (s.stk (.inr .original)) with
    | none => have hfalse := originalRange_failure L s hs hq hp; simp [hfalse] at hf
    | some R =>
        obtain ⟨hflag, hacc, hm, hz⟩ := originalRange_success_data L s hs hq R hp
        simp [IsUnaryWord, hm, hz]
  obtain ⟨m, hm, hcompare⟩ := guardedDeclaredCount_executes
    (.inr .headerM : NumericStack UnaryScanPort) (.inr .savedCount) (by decide)
    (originalRangeEval s) (fun hf => (hwords hf).1) (fun hf => (hwords hf).2)
  obtain ⟨hN, hi, hc, hd, hz, hquery⟩ := validationPrepared_ready L s hs hq
  have hbound := (unaryRows_counter_bounds scanRowsPorts .less (fun a b => a && b)
    (validationN s) L (validationPrepared s) hi hc hd hz).2.2
  exact ⟨n + m, by change ((originalRangeEval s).stk (.inr .savedCount)).length ≤ L at hbound; omega,
    RoutineComposition.seq_executes originalRangeRoutine
      (guardedDeclaredCountRoutine (.inr .headerM) (.inr .savedCount)) hrange hcompare⟩

theorem originalCountRange_preserves (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) :
    (originalCountRangeEval s).stk (.inr .original) = s.stk (.inr .original) ∧
      (originalCountRangeEval s).stk (.inr .queries) = List.replicate (validationN s) true := by
  obtain ⟨hN, hi, hc, hd, hz, hqueries⟩ := validationPrepared_ready L s hs hq
  constructor
  · rw [originalCountRangeEval, guardedDeclaredCount_extra _ _ _ (by decide) (by decide)]
    change (originalRangeRows s).stk (.inr .original) = _
    rw [originalRangeRows, unaryRows_extra scanRowsPorts .original (by decide) (by decide) (by decide)
      .less (fun a b => a && b) (validationN s) L (validationPrepared s) hi hc,
      validationPrepared_record]
  · rw [originalCountRangeEval, guardedDeclaredCount_extra _ _ _ (by decide) (by decide)]
    change (originalRangeRows s).stk (.inr .queries) = _
    rw [originalRangeRows, unaryRows_extra scanRowsPorts .queries (by decide) (by decide) (by decide)
      .less (fun a b => a && b) (validationN s) L (validationPrepared s) hi hc]
    exact hqueries

end PolytomyReductionModel
