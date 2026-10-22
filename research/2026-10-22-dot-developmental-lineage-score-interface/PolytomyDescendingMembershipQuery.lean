/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual one coverage query. It copies the remaining physical outer query
counter into the cap, scans the original record afresh, rejects malformed
or trailing input, cleans all scan tapes and returns the membership verdict.
The query counter and original record survive. No Nat-valued control.
-/
import PolytomyUnaryScanCleanup

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def queryStartOp : Op (NumericStack UnaryScanPort) Bool (CountdownState Bool) :=
  .load (fun _ => ((false, false), false))

def queryVerdictOp : Op (NumericStack UnaryScanPort) Bool (CountdownState Bool) :=
  .load (fun st => (st.1, st.2 && st.1.1))

def queryCopied (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  wordDuplicateEval (.inr .queries) (.inl .cap) s

def queryPrepared (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  queryStartOp.apply (queryCopied s)

theorem queryPrepared_ready (C L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) (hq : s.stk (.inr .queries) = List.replicate C true) :
    UnaryScanReady C L (queryPrepared s) := by
  have hcap : s.stk (.inl .cap) = [] := by simpa using hs.numeric.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [NumericLoopInv, queryPrepared, queryStartOp, queryCopied, wordDuplicateEval,
      Op.apply, hcap, hq] using And.intro hs.numeric.1
        (And.intro hs.numeric.2.1 (And.intro hs.numeric.2.2.1 hs.numeric.2.2.2.2))
  · simpa [queryPrepared, queryStartOp, queryCopied, wordDuplicateEval, Op.apply] using hs.source_empty
  · intro k hk
    simpa [queryPrepared, queryStartOp, queryCopied, wordDuplicateEval, Op.apply] using hs.empty k hk
  · simpa [queryPrepared, queryStartOp, queryCopied, wordDuplicateEval, Op.apply] using hs.original_bound

def descendingQueryRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState Bool) :=
  RoutineComposition.seq (wordDuplicateRoutine (.inr .queries) (.inr .copyTemp) (.inl .cap))
    (RoutineComposition.seq (Atom.routine queryStartOp)
      (RoutineComposition.seq (unaryScanCleanRoutine .equal (fun a b => a || b))
        (Atom.routine queryVerdictOp)))

def descendingQueryEval (C : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  queryVerdictOp.apply (unaryScanCleanEval .equal (fun a b => a || b) C (queryPrepared s))

def descendingQueryStepBound (L : ℕ) := 17 * L ^ 3 + 27 * L ^ 2 + 36 * L + 46

theorem descendingQuery_executes (C L : ℕ) (hC : C ≤ L)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = List.replicate C true) :
    ∃ n ≤ descendingQueryStepBound L, descendingQueryRoutine.Executes s (descendingQueryEval C s) n := by
  have hcopy := wordDuplicate_executes (.inr .queries : NumericStack UnaryScanPort) (.inr .copyTemp) (.inl .cap)
    (by decide) (by decide) (by decide) s (hs.empty .copyTemp (by simp [scanWorkExtras]))
  have hstart := Atom.executes queryStartOp (queryCopied s)
  obtain ⟨n, hn, hscan⟩ := unaryScanClean_executes .equal (fun a b => a || b) C L
    (queryPrepared s) (queryPrepared_ready C L s hs hq)
  have hfinal := Atom.executes queryVerdictOp (unaryScanCleanEval .equal (fun a b => a || b) C (queryPrepared s))
  have h34 := RoutineComposition.seq_executes (unaryScanCleanRoutine .equal (fun a b => a || b))
    (Atom.routine queryVerdictOp) hscan hfinal
  have h234 := RoutineComposition.seq_executes (Atom.routine queryStartOp)
    (RoutineComposition.seq (unaryScanCleanRoutine .equal (fun a b => a || b)) (Atom.routine queryVerdictOp)) hstart h34
  have hall := RoutineComposition.seq_executes
    (wordDuplicateRoutine (.inr .queries) (.inr .copyTemp) (.inl .cap))
    (RoutineComposition.seq (Atom.routine queryStartOp)
      (RoutineComposition.seq (unaryScanCleanRoutine .equal (fun a b => a || b)) (Atom.routine queryVerdictOp))) hcopy h234
  have hlen : (s.stk (.inr .queries)).length = C := by simp [hq]
  rw [hlen] at hall
  have hmul := Nat.mul_le_mul_right (L * L) hC
  refine ⟨(3 * C + 3) + (1 + (n + 1)), ?_, hall⟩
  unfold unaryScanCleanBound unaryScanPrefixBound unaryRowsBound unaryFramedRowBound at hn
  unfold descendingQueryStepBound
  nlinarith

def normalizedMember (C : ℕ) (bits : List Bool) : Bool :=
  match readNormalizedSource bits with
  | none => false
  | some R => decide (C ∈ R.rows.flatten)

theorem descendingQuery_verdict (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = List.replicate C true) :
    (descendingQueryEval C s).state.2 = normalizedMember C (s.stk (.inr .original)) := by
  have ho := unaryScanClean_observation .equal (fun a b => a || b) C L
    (queryPrepared s) (queryPrepared_ready C L s hs hq)
  have hinput : (queryPrepared s).stk (.inr .original) = s.stk (.inr .original) := by
    simp [queryPrepared, queryCopied, queryStartOp, wordDuplicateEval, Op.apply]
  have hacc : (queryPrepared s).state.1.1 = false := rfl
  rw [hinput, hacc] at ho
  let u := unaryScanCleanEval .equal (fun a b => a || b) C (queryPrepared s)
  cases hp : readNormalizedSource (s.stk (.inr .original)) with
  | none =>
      have hf : u.state.2 = false := by
        cases hx : u.state.2 <;> simp [unaryScanCompleteObservation, hp, ← u, hx] at ho ⊢
      simp [descendingQueryEval, ← u, queryVerdictOp, Op.apply, hf, normalizedMember, hp]
  | some R =>
      have hsome : unaryScanCompleteObservation u = some (decide (C ∈ R.rows.flatten)) := by
        simpa only [hp, Option.map_some, visitFold_rows, visitFold_or, Bool.false_or] using ho
      have hf : u.state.2 = true := by
        cases hx : u.state.2 <;> simp [unaryScanCompleteObservation, hx] at hsome ⊢
      have ha : u.state.1.1 = decide (C ∈ R.rows.flatten) := by
        simpa [unaryScanCompleteObservation, hf] using hsome
      simp [descendingQueryEval, ← u, queryVerdictOp, Op.apply, hf, ha, normalizedMember, hp]

theorem descendingQuery_preserves (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = List.replicate C true) :
    (descendingQueryEval C s).stk (.inr .original) = s.stk (.inr .original) ∧
      (descendingQueryEval C s).stk (.inr .queries) = s.stk (.inr .queries) := by
  have h := unaryScanClean_preserves .equal (fun a b => a || b) C L
    (queryPrepared s) (queryPrepared_ready C L s hs hq)
  simpa [descendingQueryEval, queryVerdictOp, Op.apply, queryPrepared, queryCopied,
    queryStartOp, wordDuplicateEval] using h

theorem descendingQuery_ready (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = List.replicate C true) :
    UnaryScanReady 0 L (descendingQueryEval C s) := by
  have h := unaryScanClean_ready .equal (fun a b => a || b) C L
    (queryPrepared s) (queryPrepared_ready C L s hs hq)
  exact ⟨h.numeric, h.source_empty, h.empty, h.original_bound⟩

/- One actual body is now ready for an outer countdown: after that
countdown pops once, its remaining length C is copied and queried, without
altering the reserved counter. C<=L is proved at the loop invariant, not
assumed for arbitrary numeric external input. The full coverage loop,
initial query-count creation and original range/count validation join
remain next. No whole constructor/checker/kernel closure is claimed.
-/

end PolytomyReductionModel
