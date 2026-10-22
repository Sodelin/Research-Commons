/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual first-pass preparation: seed range=true, read the original physical
headers, copy parsed N into both the range cap and reserved coverage count.
Both copies and header work are included in the transition bound. Initial
cap and query counter must be empty; failed headers are not revived.
-/
import PolytomyGuardedDeclaredCountCheck

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def rangeStartOp : Op (NumericStack UnaryScanPort) Bool (CountdownState Bool) :=
  .load (fun _ => ((true, false), false))

theorem scanHeader_unary (C L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady C L s) :
    IsUnaryWord ((scanHeaderEval s).stk (.inr .headerN)) ∧
      IsUnaryWord ((scanHeaderEval s).stk (.inr .headerM)) ∧
      IsUnaryWord ((scanHeaderEval s).stk (.inr .headerK)) := by
  let u := wordDuplicateEval (.inr .original) (.inl .source) s
  have hn : u.stk (.inr .headerN) = [] := by
    simpa [u, wordDuplicateEval] using hs.empty .headerN (by simp [scanWorkExtras])
  have hm : u.stk (.inr .headerM) = [] := by
    simpa [u, wordDuplicateEval] using hs.empty .headerM (by simp [scanWorkExtras])
  have hk : u.stk (.inr .headerK) = [] := by
    simpa [u, wordDuplicateEval] using hs.empty .headerK (by simp [scanWorkExtras])
  exact internalHeader_unary_scalars scanHeaderPorts u hn hm hk

def validationHeader (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  scanHeaderEval (rangeStartOp.apply s)

def validationCap (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  wordDuplicateEval (.inr .headerN) (.inl .cap) (validationHeader s)

def validationPrepared (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  wordDuplicateEval (.inr .headerN) (.inr .queries) (validationCap s)

def validationN (s : CountdownStore (NumericStack UnaryScanPort) Bool) : ℕ :=
  ((validationHeader s).stk (.inr .headerN)).length

def validationPrepareRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState Bool) :=
  RoutineComposition.seq (Atom.routine rangeStartOp)
    (RoutineComposition.seq scanHeaderRoutine
      (RoutineComposition.seq (wordDuplicateRoutine (.inr .headerN) (.inr .copyTemp) (.inl .cap))
        (wordDuplicateRoutine (.inr .headerN) (.inr .copyTemp) (.inr .queries))))

theorem rangeStart_ready (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) : UnaryScanReady 0 L (rangeStartOp.apply s) :=
  ⟨hs.numeric, hs.source_empty, hs.empty, hs.original_bound⟩

theorem validationPrepare_executes (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) : ∃ n ≤ 15 * L + 23,
      validationPrepareRoutine.Executes s (validationPrepared s) n := by
  have hstart := Atom.executes rangeStartOp s
  obtain ⟨n, hn, hhead, ho, hsrc, hN, hM, hK⟩ := scanHeader_executes 0 L
    (rangeStartOp.apply s) (rangeStart_ready L s hs)
  have htemp : (validationHeader s).stk (.inr .copyTemp) = [] := by
    rw [validationHeader, scanHeader_extra _ .copyTemp (by decide) (by decide) (by decide)]
    exact hs.empty .copyTemp (by simp [scanWorkExtras])
  have hcap := wordDuplicate_executes (.inr .headerN : NumericStack UnaryScanPort) (.inr .copyTemp) (.inl .cap)
    (by decide) (by decide) (by decide) (validationHeader s) htemp
  have htemp2 : (validationCap s).stk (.inr .copyTemp) = [] := by simp [validationCap, wordDuplicateEval, htemp]
  have hqueries := wordDuplicate_executes (.inr .headerN : NumericStack UnaryScanPort) (.inr .copyTemp) (.inr .queries)
    (by decide) (by decide) (by decide) (validationCap s) htemp2
  have hlen : ((validationCap s).stk (.inr .headerN)).length = validationN s := by
    simp [validationCap, wordDuplicateEval, validationN]
  rw [hlen] at hqueries
  have h34 := RoutineComposition.seq_executes
    (wordDuplicateRoutine (.inr .headerN) (.inr .copyTemp) (.inl .cap))
    (wordDuplicateRoutine (.inr .headerN) (.inr .copyTemp) (.inr .queries)) hcap hqueries
  have h234 := RoutineComposition.seq_executes scanHeaderRoutine
    (RoutineComposition.seq (wordDuplicateRoutine (.inr .headerN) (.inr .copyTemp) (.inl .cap))
      (wordDuplicateRoutine (.inr .headerN) (.inr .copyTemp) (.inr .queries))) hhead h34
  have hall := RoutineComposition.seq_executes (Atom.routine rangeStartOp)
    (RoutineComposition.seq scanHeaderRoutine
      (RoutineComposition.seq (wordDuplicateRoutine (.inr .headerN) (.inr .copyTemp) (.inl .cap))
        (wordDuplicateRoutine (.inr .headerN) (.inr .copyTemp) (.inr .queries)))) hstart h234
  exact ⟨1 + (n + ((3 * validationN s + 3) + (3 * validationN s + 3))), by change validationN s ≤ L at hN; omega, hall⟩

theorem validationPrepared_extra (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (k : UnaryScanPort) (hk : k ≠ .queries) :
    (validationPrepared s).stk (.inr k) = (validationHeader s).stk (.inr k) := by
  simp [validationPrepared, validationCap, wordDuplicateEval, hk]

theorem validationPrepared_ready (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) (hq : s.stk (.inr .queries) = []) :
    validationN s ≤ L ∧ UnaryVisitInv scanVisitPorts (validationN s) L (validationPrepared s) ∧
      (validationPrepared s).stk (.inr .inner) = [] ∧
      (validationPrepared s).stk (.inr .outer) = [] ∧
      (validationPrepared s).stk (.inr .savedCount) = [] ∧
      (validationPrepared s).stk (.inr .queries) = List.replicate (validationN s) true := by
  let u := rangeStartOp.apply s
  have hu := rangeStart_ready L s hs
  obtain ⟨n, hn, he, ho, hsrc, hN, hM, hK⟩ := scanHeader_executes 0 L u hu
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready 0 L u hu
  have hword := (scanHeader_unary 0 L u hu).1
  have hcap : (validationHeader s).stk (.inl .cap) = [] := by
    rw [validationHeader, scanHeader_numeric_extra _ .cap (by decide)]
    simpa using hs.numeric.2.2.2.1
  have hqueries : (validationHeader s).stk (.inr .queries) = [] := by
    rw [validationHeader, scanHeader_extra _ .queries (by decide) (by decide) (by decide)]
    exact hq
  refine ⟨hN, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hi with ⟨hnum, hm, ht, hl, hr⟩
    rcases hnum with ⟨hp, hw, hout, hzero, hlen⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals simp only [validationPrepared, validationCap, wordDuplicateEval]
    · exact hp
    · exact hw
    · exact hout
    · simpa only [Function.update_same, hcap, List.append_nil] using hword
    · exact hlen
    · exact hm
    · exact ht
    · exact hl
    · exact hr
  · rw [validationPrepared_extra s .inner (by decide)]; exact hc
  · rw [validationPrepared_extra s .outer (by decide)]; exact hd
  · rw [validationPrepared_extra s .savedCount (by decide)]; exact hz
  · simpa [validationPrepared, validationCap, wordDuplicateEval, hqueries, validationN, IsUnaryWord] using hword

theorem validationPrepared_control (s : CountdownStore (NumericStack UnaryScanPort) Bool) :
    (validationPrepared s).state.1 = (true, false) := by
  change (validationHeader s).state.1 = _
  exact copiedHeader_frame (.inr .original) scanHeaderPorts (rangeStartOp.apply s)

theorem validationPrepared_record (s : CountdownStore (NumericStack UnaryScanPort) Bool) :
    (validationPrepared s).stk (.inr .original) = s.stk (.inr .original) := by
  rw [validationPrepared_extra s .original (by decide), validationHeader,
    scanHeader_extra _ .original (by decide) (by decide) (by decide)]
  rfl

/- Prepared N is obtained from a true-only physical header output and is
bounded by original input length even after malformed later headers. The
incoming syntax bit is not changed by either copy; the range accumulator
is physically initialized true. The next composition must actually run
rows, check suffix/count, clear scan work and feed this reserved count to
the existing coverage loop. No full validator/constructor claim yet.
-/

end PolytomyReductionModel
