/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual original-record replay/header followed by selected-row scanning.
The existing reserved queries port is used as a disposable row selector;
the query identifier remains on the separate physical numeric cap tape.
-/
import PolytomySelectedRowsBounds

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def selectedScanPrefixRoutine :
    Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq scanHeaderRoutine (selectedRowsRoutine scanVisitPorts .inner .outer .queries)

def selectedScanPrefixEval (C : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) :=
  selectedRowsEval scanVisitPorts .inner .outer .queries C (scanHeaderEval s)

def selectedScanPrefixBound (C L : ℕ) := 9 * L + 16 + selectedRowsBound C L

theorem selectedScanPrefix_executes (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    ∃ n ≤ selectedScanPrefixBound C L,
      selectedScanPrefixRoutine.Executes s (selectedScanPrefixEval C s) n ∧
      UnaryRowsInv scanVisitPorts .inner C L (selectedScanPrefixEval C s) := by
  obtain ⟨n, hn, hhead, ho, hsrc, hN, hM, hK⟩ := scanHeader_executes C L s hs
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  obtain ⟨m, hm, hrows, hout, hg, hclear⟩ := selectedRows_executes scanVisitPorts
    .inner .outer .queries (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    C L (scanHeaderEval s) hi hc hd
  exact ⟨n + m, by unfold selectedScanPrefixBound; omega,
    RoutineComposition.seq_executes _ _ hhead hrows, hout⟩

def selectedScanReadFold (C : ℕ) (acc : ℕ × SelectedRowFrame) (bits : List Bool) :
    Option (List Bool × (ℕ × SelectedRowFrame)) :=
  match readInternalHeaderPrefix bits with
  | none => none
  | some (_, rest) => (readFramedList (readFramedList readUnaryFrame) rest).map
      (fun z => (z.2, z.1.foldl (selectedRowStep C) acc))

theorem selectedScanPrefix_observation (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    dataVisitObservation (selectedRowData UnaryScanPort.queries) (selectedScanPrefixEval C s) =
      selectedScanReadFold C (selectedRowData .queries s) (s.stk (.inr .original)) := by
  obtain ⟨n, hn, he, ho, hsrc, hN, hM, hK⟩ := scanHeader_executes C L s hs
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  rw [selectedScanPrefixEval, selectedRows_observation scanVisitPorts .inner .outer .queries
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C L (scanHeaderEval s) hi hc]
  have hframe := congrArg Prod.fst (copiedHeader_frame (.inr .original : NumericStack UnaryScanPort) scanHeaderPorts s)
  have hsel := scanHeader_extra s .queries (by decide) (by decide) (by decide)
  have hacc : selectedRowData .queries (scanHeaderEval s) = selectedRowData .queries s := by
    simp only [selectedRowData, hsel, hframe]
  cases hp : readInternalHeaderPrefix (s.stk (.inr .original)) with
  | none =>
      have hflag : (scanHeaderEval s).state.2 = false := by
        cases hh : (scanHeaderEval s).state.2 <;> simp [internalHeaderObservation, hh, hp] at ho ⊢
      simp [selectedScanReadFold, hp, hflag]
  | some z =>
      rcases z with ⟨⟨N, M, K⟩, rest⟩
      have hflag : (scanHeaderEval s).state.2 = true := by
        cases hh : (scanHeaderEval s).state.2 <;> simp [internalHeaderObservation, hh, hp] at ho ⊢
      have hrest : (scanHeaderEval s).stk (.inl .source) = rest := by
        simpa [internalHeaderObservation, hflag, hp, scanHeaderPorts] using congrArg (Option.map Prod.snd) ho
      simp only [hflag, ↓reduceIte, hrest, hacc, selectedScanReadFold, hp]

theorem selectedScanPrefix_record_preserved (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    (selectedScanPrefixEval C s).stk (.inr .original) = s.stk (.inr .original) := by
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  rw [selectedScanPrefixEval, selectedRows_extra scanVisitPorts .inner .outer .queries .original
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) C L (scanHeaderEval s) hi hc]
  exact scanHeader_extra s .original (by decide) (by decide) (by decide)

theorem selectedScanReadFold_tagged (C : ℕ) (acc : ℕ × SelectedRowFrame) (bits : List Bool) :
    selectedScanReadFold C acc bits = (readTaggedUnaryPrefix bits).map
      (fun z => (z.2, z.1.rows.foldl (selectedRowStep C) acc)) := by
  cases bits with
  | nil => rfl
  | cons tag bits =>
      cases tag with
      | false => rfl
      | true =>
          cases h1 : readUnaryFrame bits with
          | none => simp [selectedScanReadFold, readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1]
          | some z1 =>
              rcases z1 with ⟨N, r1⟩
              cases h2 : readUnaryFrame r1 with
              | none => simp [selectedScanReadFold, readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1, h2]
              | some z2 =>
                  rcases z2 with ⟨m, r2⟩
                  cases h3 : readUnaryFrame r2 with
                  | none => simp [selectedScanReadFold, readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1, h2, h3]
                  | some z3 =>
                      rcases z3 with ⟨K, rest⟩
                      cases hrows : readFramedList (readFramedList readUnaryFrame) rest with
                      | none => simp [selectedScanReadFold, readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1, h2, h3, hrows]
                      | some z4 => rcases z4 with ⟨rows, suffix⟩; simp [selectedScanReadFold,
                          readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1, h2, h3, hrows]

def selectedScanCompleteRoutine :
    Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq selectedScanPrefixRoutine (Atom.routine suffixCheckOp)

def selectedScanCompleteEval (C : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) :=
  suffixChecked (selectedScanPrefixEval C s)

theorem selectedScanComplete_executes (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    ∃ n ≤ selectedScanPrefixBound C L + 1,
      selectedScanCompleteRoutine.Executes s (selectedScanCompleteEval C s) n := by
  obtain ⟨n, hn, he, hi⟩ := selectedScanPrefix_executes C L s hs
  exact ⟨n + 1, by omega, RoutineComposition.seq_executes _ _ he (Atom.executes suffixCheckOp _)⟩

theorem selectedScanComplete_observation (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    unaryScanCompleteObservation (selectedScanCompleteEval C s) =
      (readNormalizedSource (s.stk (.inr .original))).map
        (fun R => (R.rows.foldl (selectedRowStep C) (selectedRowData .queries s)).2) := by
  have ho := selectedScanPrefix_observation C L s hs
  rw [selectedScanReadFold_tagged] at ho
  rw [readNormalizedSource_tagged]
  cases hp : readTaggedUnaryPrefix (s.stk (.inr .original)) with
  | none =>
      have hn : dataVisitObservation (selectedRowData UnaryScanPort.queries) (selectedScanPrefixEval C s) = none := by
        simpa [hp] using ho
      have hf := (dataVisitObservation_none _ _).mp hn
      simp [unaryScanCompleteObservation, selectedScanCompleteEval, suffixChecked, suffixCheckOp, Op.apply, hf, hp]
  | some z =>
      rcases z with ⟨R, suffix⟩
      have hsome : dataVisitObservation (selectedRowData UnaryScanPort.queries) (selectedScanPrefixEval C s) =
          some (suffix, R.rows.foldl (selectedRowStep C) (selectedRowData .queries s)) := by
        simpa [hp] using ho
      obtain ⟨hf, hsource, hacc⟩ := (dataVisitObservation_some _ _ _ _).mp hsome
      have hframe := congrArg Prod.snd hacc
      change (selectedScanPrefixEval C s).state.1.1 = _ at hframe
      cases suffix <;> simp [unaryScanCompleteObservation, selectedScanCompleteEval,
        suffixChecked, suffixCheckOp, Op.apply, hf, hsource, hframe, hp]

/- Suffix rejection is actual and the observation uses the complete
ORIGINAL readNormalizedSource, not prefix-only syntax. Initial physical
cap/selector creation, reset-to-no-hit, unconditional cleanup and final
Boolean verdict are still separate obligations at this checkpoint.
-/

end PolytomyReductionModel
