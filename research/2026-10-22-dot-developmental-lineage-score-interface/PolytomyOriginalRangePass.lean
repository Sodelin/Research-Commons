/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual first complete-input range pass. Query cap and preserved coverage
count are created from the physical original N header, not supplied as a
numerical oracle. Exact syntax observation still separates false range
from malformed input. Declared-count comparison and cleanup are next.
-/
import PolytomyPhysicalValidationPreparation

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def originalRangeRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState Bool) :=
  RoutineComposition.seq validationPrepareRoutine
    (RoutineComposition.seq (unaryRowsRoutine scanRowsPorts .less (fun a b => a && b))
      (Atom.routine suffixCheckOp))

def originalRangeRows (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  unaryRowsEval scanRowsPorts .less (fun a b => a && b) (validationN s) (validationPrepared s)

def originalRangeEval (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  suffixChecked (originalRangeRows s)

def originalRangeBound (L : ℕ) := 17 * L ^ 3 + 27 * L ^ 2 + 31 * L + 34

theorem originalRange_executes (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) (hq : s.stk (.inr .queries) = []) :
    ∃ n ≤ originalRangeBound L, originalRangeRoutine.Executes s (originalRangeEval s) n := by
  obtain ⟨n, hn, hprep⟩ := validationPrepare_executes L s hs
  obtain ⟨hN, hi, hc, hd, hz, hquery⟩ := validationPrepared_ready L s hs hq
  obtain ⟨m, hm, hrows, hout, hg, hclear⟩ := unaryRows_executes scanRowsPorts .less
    (fun a b => a && b) (validationN s) L (validationPrepared s) hi hc hd hz
  have hsuffix := Atom.executes suffixCheckOp (originalRangeRows s)
  have htail := RoutineComposition.seq_executes (unaryRowsRoutine scanRowsPorts .less (fun a b => a && b))
    (Atom.routine suffixCheckOp) hrows hsuffix
  have hall := RoutineComposition.seq_executes validationPrepareRoutine
    (RoutineComposition.seq (unaryRowsRoutine scanRowsPorts .less (fun a b => a && b))
      (Atom.routine suffixCheckOp)) hprep htail
  have hmul := Nat.mul_le_mul_right (L * L) hN
  refine ⟨n + (m + 1), ?_, hall⟩
  unfold unaryRowsBound unaryFramedRowBound at hm
  unfold originalRangeBound
  nlinarith

theorem validationPrepared_header_observation (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s) :
    internalHeaderObservation scanHeaderPorts (validationPrepared s) =
      readInternalHeaderPrefix (s.stk (.inr .original)) := by
  obtain ⟨n, hn, he, ho, hb⟩ := scanHeader_executes 0 L (rangeStartOp.apply s) (rangeStart_ready L s hs)
  simpa [validationPrepared, validationCap, validationHeader, wordDuplicateEval,
    internalHeaderObservation, scanHeaderPorts, rangeStartOp, Op.apply] using ho

theorem validationPrepared_values (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) (R : RawMSSCRecord)
    (hp : readNormalizedSource (s.stk (.inr .original)) = some R) :
    validationN s = R.N ∧ (validationPrepared s).state.2 = true ∧
      (validationPrepared s).stk (.inl .source) = encodeFramedList (encodeFramedList unaryFrame) R.rows ∧
      (validationPrepared s).stk (.inr .headerM) = List.replicate R.declaredM true := by
  let u := wordDuplicateEval (.inr .original) (.inl .source) (rangeStartOp.apply s)
  have hn : u.stk (.inr .headerN) = [] := by
    simpa [u, wordDuplicateEval, rangeStartOp, Op.apply] using hs.empty .headerN (by simp [scanWorkExtras])
  have hm : u.stk (.inr .headerM) = [] := by
    simpa [u, wordDuplicateEval, rangeStartOp, Op.apply] using hs.empty .headerM (by simp [scanWorkExtras])
  have hk : u.stk (.inr .headerK) = [] := by
    simpa [u, wordDuplicateEval, rangeStartOp, Op.apply] using hs.empty .headerK (by simp [scanWorkExtras])
  have hsource : u.stk (.inl .source) = s.stk (.inr .original) := by
    simp [u, wordDuplicateEval, rangeStartOp, Op.apply, hs.source_empty]
  have hparse : readNormalizedSource (u.stk (.inl .source)) = some R := by rw [hsource]; exact hp
  obtain ⟨hf, hsrc, hN, hM, hK⟩ := internalHeader_complete_record_values scanHeaderPorts u hn hm hk R hparse
  have hlen : validationN s = R.N := by
    change ((internalHeaderEval scanHeaderPorts u).stk (.inr .headerN)).length = R.N
    rw [hN]; simp
  refine ⟨hlen, hf, ?_, ?_⟩
  · simpa only [validationPrepared, validationCap, wordDuplicateEval,
      Function.update_of_ne (by decide : (Sum.inl NumericPort.source : NumericStack UnaryScanPort) ≠ .inr .queries),
      Function.update_of_ne (by decide : (Sum.inl NumericPort.source : NumericStack UnaryScanPort) ≠ .inl .cap)] using hsrc
  · rw [validationPrepared_extra s .headerM (by decide)]
    exact hM

theorem originalRange_prefix_observation (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) :
    unaryVisitObservation (originalRangeRows s) =
      (readTaggedUnaryPrefix (s.stk (.inr .original))).map
        (fun z => (z.2, z.1.rows.flatten.all (fun a => decide (a < validationN s)))) := by
  obtain ⟨hN, hi, hc, hd, hz, hqueries⟩ := validationPrepared_ready L s hs hq
  have hr := unaryRows_range_observation scanRowsPorts (validationN s) L (validationPrepared s) hi hc
  have ho := validationPrepared_header_observation L s hs
  have hacc : (validationPrepared s).state.1.1 = true := congrArg Prod.fst (validationPrepared_control s)
  have hfold := unaryScanReadFold_tagged .less (fun a b => a && b) (validationN s) true
    (s.stk (.inr .original))
  simp only [visitFold_rows, visitFold_and, Bool.true_and] at hfold
  rw [← hfold]
  cases hp : readInternalHeaderPrefix (s.stk (.inr .original)) with
  | none =>
      have hf : (validationPrepared s).state.2 = false := by
        cases hx : (validationPrepared s).state.2 <;> simp [internalHeaderObservation, hx, hp] at ho ⊢
      simpa [originalRangeRows, unaryScanReadFold, hp, hf] using hr
  | some z =>
      rcases z with ⟨⟨N, M, K⟩, rest⟩
      have hf : (validationPrepared s).state.2 = true := by
        cases hx : (validationPrepared s).state.2 <;> simp [internalHeaderObservation, hx, hp] at ho ⊢
      have hsrc : (validationPrepared s).stk (.inl .source) = rest := by
        simpa [internalHeaderObservation, scanHeaderPorts, hp, hf] using congrArg (Option.map Prod.snd) ho
      simpa [originalRangeRows, unaryScanReadFold, hp, hf, hsrc, hacc, visitFold_rows, visitFold_and] using hr

theorem originalRange_observation (L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) :
    unaryScanCompleteObservation (originalRangeEval s) =
      (readNormalizedSource (s.stk (.inr .original))).map
        (fun R => R.rows.flatten.all (fun a => decide (a < R.N))) := by
  have ho := originalRange_prefix_observation L s hs hq
  cases hp : readTaggedUnaryPrefix (s.stk (.inr .original)) with
  | none =>
      have hn : unaryVisitObservation (originalRangeRows s) = none := by simpa [hp] using ho
      have hf := (unaryVisitObservation_none _).mp hn
      simp [originalRangeEval, unaryScanCompleteObservation, suffixChecked, suffixCheckOp, Op.apply,
        hf, readNormalizedSource_tagged, hp]
  | some z =>
      rcases z with ⟨R, suffix⟩
      have hsome : unaryVisitObservation (originalRangeRows s) =
          some (suffix, R.rows.flatten.all (fun a => decide (a < validationN s))) := by simpa [hp] using ho
      obtain ⟨hf, hsrc, hacc⟩ := (unaryVisitObservation_some _ _ _).mp hsome
      cases suffix with
      | nil =>
          have hcomplete : readNormalizedSource (s.stk (.inr .original)) = some R := by
            rw [readNormalizedSource_tagged, hp]
          have hN := (validationPrepared_values L s hs R hcomplete).1
          simp [originalRangeEval, unaryScanCompleteObservation, suffixChecked, suffixCheckOp, Op.apply,
            hf, hsrc, hacc, hcomplete, hN]
      | cons b suffix =>
          simp [originalRangeEval, unaryScanCompleteObservation, suffixChecked, suffixCheckOp, Op.apply,
            hf, hsrc, readNormalizedSource_tagged, hp]

/- This is a complete original syntax/range pass with actual N creation.
The saved actual count and declared m still need their guarded comparison;
all-path cleanup must preserve the freshly created query counter and feed
the correct first-pass verdict into coverage. Full constructor/checker,
encoded hardness and all kernel checks remain separate.
-/

end PolytomyReductionModel
