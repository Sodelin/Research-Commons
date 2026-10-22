/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual selected-row section with ORIGINAL outer unary count parsing.
No count is supplied for free and no saved-count copy is needed here.
The selector is an existing disposable physical tape, not finite control.
-/
import PolytomySelectedRowMeaning

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K : Type} [DecidableEq K]

def selectedRowsRoutine (p : UnaryVisitPorts K) (c d selector : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (guardedUnaryFieldRoutine (.inl .source) (.inr d))
    (selectedRowsOuterRoutine p c d selector)

def selectedRowsEval (p : UnaryVisitPorts K) (c d selector : K) (C : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) :=
  selectedRowsOuterEval p c d selector C (guardedUnaryFieldEval (.inl .source) (.inr d) s)

def selectedRowsBound (C L : ℕ) := L * (unaryFramedRowBound C L + 6) + 2 * L + 7

theorem selectedRowsPrefix_invariant (p : UnaryVisitPorts K) (c d : K)
    (hd : UnaryVisitOutside p d) (hcd : c ≠ d) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryVisitInv p C L s)
    (hc : s.stk (.inr c) = []) :
    UnaryRowsInv p c C L (guardedUnaryFieldEval (.inl .source) (.inr d) s) := by
  refine ⟨unaryField_visit_invariant p d hd C L s hs, ?_⟩
  intro hf
  rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using hcd)]
  exact hc

theorem selectedRows_executes (p : UnaryVisitPorts K) (c d selector : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryVisitInv p C L s)
    (hempty : s.stk (.inr c) = []) (hdempty : s.stk (.inr d) = []) :
    ∃ n ≤ selectedRowsBound C L,
      (selectedRowsRoutine p c d selector).Executes s (selectedRowsEval p c d selector C s) n ∧
      UnaryRowsInv p c C L (selectedRowsEval p c d selector C s) ∧
      (selectedRowsEval p c d selector C s).state.1.2 = false ∧
      ((selectedRowsEval p c d selector C s).state.2 = true →
        (selectedRowsEval p c d selector C s).stk (.inr d) = []) := by
  let u := guardedUnaryFieldEval (.inl .source) (.inr d) s
  obtain ⟨n, hn, hread⟩ := guardedUnaryField_executes (.inl .source : NumericStack K) (.inr d)
    (by simp) s hdempty L hs.1.2.2.2.2
  have hi := selectedRowsPrefix_invariant p c d hd hcd C L s hs hempty
  obtain ⟨m, hm, he, hout, hg, hclear⟩ := selectedRowsOuter_executes p c d selector hc hd hk
    hcd hkc hkd C L u hi
  have hlen := (guardedUnaryField_output_bound (.inl .source : NumericStack K) (.inr d) s hdempty).trans hs.1.2.2.2.2
  have hmul := Nat.mul_le_mul_right (unaryFramedRowBound C L + 6) hlen
  exact ⟨n + m, by unfold selectedRowsBound; omega,
    RoutineComposition.seq_executes _ _ hread he, hout, hg, hclear⟩

theorem selectedRows_observation (p : UnaryVisitPorts K) (c d selector : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryVisitInv p C L s)
    (hempty : s.stk (.inr c) = []) :
    dataVisitObservation (selectedRowData selector) (selectedRowsEval p c d selector C s) =
      if s.state.2 then (readFramedList (readFramedList readUnaryFrame) (s.stk (.inl .source))).map
        (fun q => (q.2, q.1.foldl (selectedRowStep C) (selectedRowData selector s))) else none := by
  rw [selectedRowsEval, selectedRowsOuter_observation p c d selector hc hd hk hcd hkc hkd C L _
    (selectedRowsPrefix_invariant p c d hd hcd C L s hs hempty)]
  cases hf : s.state.2 with
  | false => simp [guardedUnaryFieldEval, hf]
  | true =>
      cases hp : readUnaryFrame (s.stk (.inl .source)) with
      | none => simp [guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore, readFramedList]
      | some q =>
          rcases q with ⟨n, rest⟩
          simp [guardedUnaryFieldEval, hf, hp, unaryCallerResult, frameCallerStore,
            selectedRowData, hkd, readFramedList]

theorem selectedRows_extra (p : UnaryVisitPorts K) (c d selector k : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d)
    (hkeyc : k ≠ c) (hkeyd : k ≠ d) (hkeysel : k ≠ selector) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryVisitInv p C L s)
    (hempty : s.stk (.inr c) = []) :
    (selectedRowsEval p c d selector C s).stk (.inr k) = s.stk (.inr k) := by
  rw [selectedRowsEval, selectedRowsOuter_extra p c d selector k hc hd hk hcd hkc hkd
    hkeyc hkeyd hkeysel C L _ (selectedRowsPrefix_invariant p c d hd hcd C L s hs hempty)]
  exact guardedUnaryField_extra _ _ _ (by simp) (by simpa using hkeyd) s

theorem selectedRows_found_on_parse (p : UnaryVisitPorts K) (c d selector : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryVisitInv p C L s)
    (hempty : s.stk (.inr c) = []) (hok : s.state.2 = true)
    (rows : List (List ℕ)) (rest : List Bool)
    (hparse : readFramedList (readFramedList readUnaryFrame) (s.stk (.inl .source)) = some (rows, rest))
    (hseed : s.state.1.1 = ⟨false, false, false⟩) :
    (selectedRowsEval p c d selector C s).state.2 = true ∧
      (selectedRowsEval p c d selector C s).stk (.inl .source) = rest ∧
      (selectedRowsEval p c d selector C s).state.1.1.found =
        selectedRowMembership C (s.stk (.inr selector)).length rows := by
  have h := selectedRows_observation p c d selector hc hd hk hcd hkc hkd C L s hs hempty
  have ho : dataVisitObservation (selectedRowData selector) (selectedRowsEval p c d selector C s) =
      some (rest, rows.foldl (selectedRowStep C) (selectedRowData selector s)) := by
    simpa [hok, hparse] using h
  obtain ⟨hf, hsrc, hacc⟩ := (dataVisitObservation_some (selectedRowData selector) _ _ _).mp ho
  refine ⟨hf, hsrc, ?_⟩
  have he := congrArg (fun a : ℕ × SelectedRowFrame => a.2.found) hacc
  simpa [selectedRowData, selectedRowFold_found, hseed] using he

/- The complete original row section is now physically counted and
selected, with exact prefix/suffix and row-specific membership meaning.
Whole-record replay/header/suffix acceptance/cleanup and the original
canonical controller still must be supplied; this is not a whole query
or a downstream-machine witness.
-/

end PolytomyReductionModel
