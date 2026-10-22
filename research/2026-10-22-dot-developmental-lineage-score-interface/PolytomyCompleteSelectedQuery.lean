/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Complete actual selected-row query: real finite reset, preserved-record
replay/header, physical nested selection, original suffix rejection,
unconditional cleanup and Boolean verdict. Query/selector must really be
present on their entry tapes; their creation is not supplied for free.
-/
import PolytomySelectedQueryCleanup

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def selectedQueryStartOp : Op (NumericStack UnaryScanPort) Bool (CountdownState SelectedRowFrame) :=
  .load (fun _ => ((⟨false, false, false⟩, false), false))

def selectedQueryVerdictOp : Op (NumericStack UnaryScanPort) Bool (CountdownState SelectedRowFrame) :=
  .load (fun s => (s.1, s.2 && s.1.1.found))

def selectedQueryRoutine :
    Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (Atom.routine selectedQueryStartOp)
    (RoutineComposition.seq selectedScanCleanRoutine (Atom.routine selectedQueryVerdictOp))

def selectedQueryEval (C : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) :=
  selectedQueryVerdictOp.apply (selectedScanCleanEval C (selectedQueryStartOp.apply s))

def selectedQueryMember (C I : ℕ) (bits : List Bool) : Bool :=
  match readNormalizedSource bits with
  | none => false
  | some R => selectedRowMembership C I R.rows

def selectedQueryBound (C L I : ℕ) :=
  7 * C * L^2 + 10 * L^3 + 27 * L^2 + 30 * L + C + I + 41

theorem selectedQuery_verdict (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    (selectedQueryEval C s).state.2 =
      selectedQueryMember C (s.stk (.inr .queries)).length (s.stk (.inr .original)) := by
  let u := selectedQueryStartOp.apply s
  have hu : UnaryScanReady C L u :=
    ⟨hs.numeric, hs.source_empty, hs.empty, hs.original_bound⟩
  have ho := selectedScanClean_observation C L u hu
  cases hp : readNormalizedSource (s.stk (.inr .original)) with
  | none =>
      have hf : (selectedScanCleanEval C u).state.2 = false := by
        cases h : (selectedScanCleanEval C u).state.2 <;>
          simp [u, selectedQueryStartOp, Op.apply, unaryScanCompleteObservation, h, hp] at ho ⊢
      simp [selectedQueryEval, selectedQueryVerdictOp, Op.apply, ← u, hf, selectedQueryMember, hp]
  | some R =>
      have hf : (selectedScanCleanEval C u).state.2 = true := by
        cases h : (selectedScanCleanEval C u).state.2 <;>
          simp [u, selectedQueryStartOp, Op.apply, unaryScanCompleteObservation, h, hp] at ho ⊢
      have hframe : (selectedScanCleanEval C u).state.1.1 =
          (R.rows.foldl (selectedRowStep C) ((s.stk (.inr .queries)).length, ⟨false, false, false⟩)).2 := by
        simpa [unaryScanCompleteObservation, hf, u, selectedQueryStartOp, Op.apply, selectedRowData, hp] using ho
      have hfound := congrArg SelectedRowFrame.found hframe
      rw [selectedRowFold_found] at hfound
      simp only [Bool.not_false, Bool.true_and, Bool.false_or] at hfound
      simp [selectedQueryEval, selectedQueryVerdictOp, Op.apply, ← u, hf, hfound, selectedQueryMember, hp]

theorem selectedQuery_executes (C L I : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s)
    (hI : (s.stk (.inr .queries)).length ≤ I) :
    ∃ n ≤ selectedQueryBound C L I,
      selectedQueryRoutine.Executes s (selectedQueryEval C s) n ∧
      UnaryScanReady 0 L (selectedQueryEval C s) ∧
      (selectedQueryEval C s).stk (.inr .queries) = [] ∧
      (selectedQueryEval C s).stk (.inr .original) = s.stk (.inr .original) ∧
      (selectedQueryEval C s).state.2 =
        selectedQueryMember C (s.stk (.inr .queries)).length (s.stk (.inr .original)) := by
  let u := selectedQueryStartOp.apply s
  have hu : UnaryScanReady C L u :=
    ⟨hs.numeric, hs.source_empty, hs.empty, hs.original_bound⟩
  obtain ⟨n, hn, he⟩ := selectedScanClean_executes C L I u hu hI
  have hfinish := Atom.executes selectedQueryVerdictOp (selectedScanCleanEval C u)
  have htail := RoutineComposition.seq_executes selectedScanCleanRoutine (Atom.routine selectedQueryVerdictOp) he hfinish
  have hall := RoutineComposition.seq_executes (Atom.routine selectedQueryStartOp)
    (RoutineComposition.seq selectedScanCleanRoutine (Atom.routine selectedQueryVerdictOp))
    (Atom.executes selectedQueryStartOp s) htail
  have hpoly : selectedScanCleanBound C L I + 2 = selectedQueryBound C L I := by
    unfold selectedScanCleanBound selectedScanPrefixBound selectedRowsBound unaryFramedRowBound selectedQueryBound
    ring
  have hready := selectedScanClean_ready C L u hu
  have horig := selectedScanClean_original C L u hu
  refine ⟨1 + (n + 1), by omega, hall, ?_, ?_, ?_, selectedQuery_verdict C L s hs⟩
  · exact ⟨hready.1.numeric, hready.1.source_empty, hready.1.empty, hready.1.original_bound⟩
  · exact hready.2
  · exact horig

theorem selectedQuery_original_row (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s)
    (R : RawMSSCRecord) (hR : readNormalizedSource (s.stk (.inr .original)) = some R)
    (i : Fin R.rows.length) (hsel : (s.stk (.inr .queries)).length = i.val) :
    (selectedQueryEval C s).state.2 = decide (C ∈ R.rows.get i) := by
  rw [selectedQuery_verdict C L s hs]
  simp only [selectedQueryMember, hR, hsel]
  exact selectedRowMembership_get C R.rows i.val i.isLt

/- This is a COMPLETE supplied-physical-cap/selector query component,
not a whole constructor. Its actual body has fixed finite ports/Boolean
alphabets/three-bit semantic control. All-input malformed syntax and
trailing bytes reject, even if an earlier identifier matched. The full
source validity guard is a separate original validator; this query does
not pretend to revalidate declared m, coverage or all identifier ranges.
The original block-membership range/marker branches, physical parameter
copies, descending canonical loops, arithmetic/serializer/cleanup and
whole-machine packaging remain open, as do checker/hardness/kernel checks.
-/

end PolytomyReductionModel
