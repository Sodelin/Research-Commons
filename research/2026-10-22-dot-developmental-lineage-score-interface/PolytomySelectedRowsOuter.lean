/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual outer physical row countdown with the selected-row body, and its
exact original readMany observation. The mathematical accumulator records
selector-tape length; machine control remains three Boolean frame bits.
-/
import PolytomySelectedRowVisitor
import PolytomyDataObservedCountdown

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K : Type} [DecidableEq K]

def selectedRowData (selector : K) (s : CountdownStore (NumericStack K) SelectedRowFrame) :
    ℕ × SelectedRowFrame := ((s.stk (.inr selector)).length, s.state.1.1)

def selectedRowStep (C : ℕ) (a : ℕ × SelectedRowFrame) (row : List ℕ) : ℕ × SelectedRowFrame :=
  (a.1 - 1, row.foldl (unaryVisitStep .equal selectedRowBump C)
    (selectedRowStart a.2 (decide (a.1 = 0))))

theorem selectedRow_data_observation (p : UnaryVisitPorts K) (c selector : K)
    (hc : UnaryVisitOutside p c) (hk : UnaryVisitOutside p selector) (hkc : selector ≠ c)
    (C L : ℕ) (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    dataVisitObservation (selectedRowData selector) (selectedRowEval p c selector C s) =
      if s.state.2 then (readFramedList readUnaryFrame (s.stk (.inl .source))).map
        (fun q => (q.2, selectedRowStep C (selectedRowData selector s) q.1)) else none := by
  have h := selectedRow_observation p c selector hc hk hkc C L s hs
  have ht := selectedRow_selector p c selector hc hk hkc C L s hs
  cases hf : s.state.2 with
  | false =>
      have ho : unaryVisitObservation (selectedRowEval p c selector C s) = none := by simpa [hf] using h
      have hz := (unaryVisitObservation_none _).mp ho
      simp [dataVisitObservation, hz, hf]
  | true =>
      cases hp : readFramedList readUnaryFrame (s.stk (.inl .source)) with
      | none =>
          have ho : unaryVisitObservation (selectedRowEval p c selector C s) = none := by simpa [hf, hp] using h
          have hz := (unaryVisitObservation_none _).mp ho
          simp [dataVisitObservation, hz, hf, hp]
      | some q =>
          rcases q with ⟨row, rest⟩
          have ho : unaryVisitObservation (selectedRowEval p c selector C s) = some
              (rest, row.foldl (unaryVisitStep .equal selectedRowBump C)
                (selectedRowStart s.state.1.1 (decide ((s.stk (.inr selector)).length = 0)))) := by
            simpa [hf, hp] using h
          obtain ⟨hok, hsrc, hframe⟩ := (unaryVisitObservation_some _ _ _).mp ho
          simp [dataVisitObservation, selectedRowData, selectedRowStep, hok, hsrc, hframe,
            ht, List.length_tail, hf, hp]

def selectedRowsOuterContract (p : UnaryVisitPorts K) (c d selector : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d) (C L : ℕ) :
    CountdownContract (.inr d) (selectedRowRoutine p c selector)
      (selectedRowEval p c selector C) (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 3) where
  peek_closed s hs := by
    simpa only [UnaryRowsInv, UnaryVisitInv, NumericLoopInv, countdownPeek, countdownPeekOp, Op.apply] using hs
  pop_closed s hs hg := by
    rcases hd with ⟨hdm, hdt, hdl, hdr⟩
    simpa [UnaryRowsInv, UnaryVisitInv, NumericLoopInv, countdownPop, countdownPopOp, Op.apply,
      Ne.symm hdm, Ne.symm hdt, Ne.symm hdl, Ne.symm hdr, hcd] using hs
  body_closed s hs := by
    obtain ⟨n, hn, he, hi⟩ := selectedRow_executes p c selector hc hk hkc C L s hs
    exact hi
  reset_closed s hs := by
    simpa only [UnaryRowsInv, UnaryVisitInv, NumericLoopInv, countdownReset, countdownResetOp, Op.apply] using hs
  counter_preserved s hs := selectedRow_extra p c selector d hc hk hkc (Ne.symm hcd) (Ne.symm hkd) C L s hs
  body_executes s hs := by
    obtain ⟨n, hn, he, hi⟩ := selectedRow_executes p c selector hc hk hkc C L s hs
    exact ⟨n, hn, he⟩

def selectedRowsOuterRoutine (p : UnaryVisitPorts K) (c d selector : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState SelectedRowFrame) :=
  countdownRoutine (.inr d) (selectedRowRoutine p c selector)

def selectedRowsOuterEval (p : UnaryVisitPorts K) (c d selector : K) (C : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) :=
  countdownEval (.inr d) (selectedRowEval p c selector C) s

theorem selectedRowsOuter_executes (p : UnaryVisitPorts K) (c d selector : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    ∃ n ≤ (s.stk (.inr d)).length * (unaryFramedRowBound C L + 6) + 3,
      (selectedRowsOuterRoutine p c d selector).Executes s (selectedRowsOuterEval p c d selector C s) n ∧
      UnaryRowsInv p c C L (selectedRowsOuterEval p c d selector C s) ∧
      (selectedRowsOuterEval p c d selector C s).state.1.2 = false ∧
      ((selectedRowsOuterEval p c d selector C s).state.2 = true →
        (selectedRowsOuterEval p c d selector C s).stk (.inr d) = []) := by
  simpa only [Nat.add_assoc] using countdownRoutine_executes (.inr d)
    (selectedRowRoutine p c selector) (selectedRowEval p c selector C)
    (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 3)
    (selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L) s hs

theorem selectedRowsOuter_observation (p : UnaryVisitPorts K) (c d selector : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    dataVisitObservation (selectedRowData selector) (selectedRowsOuterEval p c d selector C s) =
      if s.state.2 then (readMany (readFramedList readUnaryFrame)
        (s.stk (.inr d)).length (s.stk (.inl .source))).map
          (fun q => (q.2, q.1.foldl (selectedRowStep C) (selectedRowData selector s))) else none := by
  exact dataObservedCountdown d (selectedRowRoutine p c selector) (selectedRowEval p c selector C)
    (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 3)
    (selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L)
    (selectedRowData selector) (fun _ => rfl)
    (by intro s; simp [selectedRowData, countdownPop, countdownPopOp, Op.apply, hkd])
    (fun _ => rfl) (readFramedList readUnaryFrame) (selectedRowStep C)
    (selectedRow_data_observation p c selector hc hk hkc C L) s hs

theorem selectedRowsOuter_extra (p : UnaryVisitPorts K) (c d selector k : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d)
    (hkeyc : k ≠ c) (hkeyd : k ≠ d) (hkeysel : k ≠ selector) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    (selectedRowsOuterEval p c d selector C s).stk (.inr k) = s.stk (.inr k) := by
  let hc' := selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L
  exact countdownLoop_preserves_on (.inr d) (selectedRowRoutine p c selector)
    (selectedRowEval p c selector C) (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 3) hc'
    (fun t => t.stk (.inr k)) (fun _ => rfl)
    (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hkeyd])
    (fun t ht => selectedRow_extra p c selector k hc hk hkc hkeyc hkeysel C L t ht)
    (s.stk (.inr d)).length (countdownPeek (.inr d) s) (hc'.peek_closed s hs)

/- This is an actual selected-row outer loop with exact original prefix
parsing. A whole-record wrapper must still read/copy the original input,
prepare both physical query and selector, reject trailing bytes, perform
unconditional scratch cleanup and bind the resulting predicate into the
original canonical type/block enumeration. No such steps are free.
-/

end PolytomyReductionModel
