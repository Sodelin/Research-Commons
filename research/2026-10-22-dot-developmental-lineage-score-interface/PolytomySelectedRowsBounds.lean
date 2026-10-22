/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

All-path bounds for selected-row scanning, including malformed rows and
partial counters. These bounds support unconditional actual cleanup.
-/
import PolytomySelectedRowsSection
import PolytomyUnaryRowsCounterBounds

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K : Type} [DecidableEq K]

theorem selectedRow_counter_bound (p : UnaryVisitPorts K) (c selector : K)
    (hc : UnaryVisitOutside p c) (hk : UnaryVisitOutside p selector) (hkc : selector ≠ c)
    (C L : ℕ) (s : CountdownStore (NumericStack K) SelectedRowFrame)
    (hs : BoundedUnaryRowsInv p c C L s) :
    ((selectedRowEval p c selector C s).stk (.inr c)).length ≤ L := by
  apply guardedUnaryRow_counter_bound p c hc .equal selectedRowBump C L
  refine ⟨selectedRowStart_invariant p c selector hk hkc C L s hs.1, ?_⟩
  simpa [selectedRowStartEval, selectedRowStartOp, countdownPop, countdownPopOp,
    Op.apply, Ne.symm hkc] using hs.2

def BoundedSelectedRowsInv (p : UnaryVisitPorts K) (c selector : K) (C L I : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) : Prop :=
  BoundedUnaryRowsInv p c C L s ∧ (s.stk (.inr selector)).length ≤ I

def boundedSelectedRowsContract (p : UnaryVisitPorts K) (c d selector : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d) (C L I : ℕ) :
    CountdownContract (.inr d) (selectedRowRoutine p c selector)
      (selectedRowEval p c selector C) (BoundedSelectedRowsInv p c selector C L I)
      (unaryFramedRowBound C L + 3) where
  peek_closed s hs :=
    ⟨⟨(selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L).peek_closed s hs.1.1, hs.1.2⟩, hs.2⟩
  pop_closed s hs hg := by
    refine ⟨⟨(selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L).pop_closed s hs.1.1 hg, ?_⟩, ?_⟩
    · simpa [countdownPop, countdownPopOp, Op.apply, hcd] using hs.1.2
    · simpa [countdownPop, countdownPopOp, Op.apply, hkd] using hs.2
  body_closed s hs := by
    refine ⟨⟨(selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L).body_closed s hs.1.1,
      selectedRow_counter_bound p c selector hc hk hkc C L s hs.1⟩, ?_⟩
    rw [selectedRow_selector p c selector hc hk hkc C L s hs.1.1, List.length_tail]
    omega
  reset_closed s hs :=
    ⟨⟨(selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L).reset_closed s hs.1.1, hs.1.2⟩, hs.2⟩
  counter_preserved s hs := (selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L).counter_preserved s hs.1.1
  body_executes s hs := (selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L).body_executes s hs.1.1

theorem selectedRows_counter_bounds (p : UnaryVisitPorts K) (c d selector : K)
    (hc : UnaryVisitOutside p c) (hd : UnaryVisitOutside p d) (hk : UnaryVisitOutside p selector)
    (hcd : c ≠ d) (hkc : selector ≠ c) (hkd : selector ≠ d) (C L I : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryVisitInv p C L s)
    (hempty : s.stk (.inr c) = []) (hdempty : s.stk (.inr d) = [])
    (hselector : (s.stk (.inr selector)).length ≤ I) :
    ((selectedRowsEval p c d selector C s).stk (.inr c)).length ≤ L ∧
      ((selectedRowsEval p c d selector C s).stk (.inr d)).length ≤ L ∧
      ((selectedRowsEval p c d selector C s).stk (.inr selector)).length ≤ I := by
  let u := guardedUnaryFieldEval (.inl .source) (.inr d) s
  have hi : UnaryRowsInv p c C L u := selectedRowsPrefix_invariant p c d hd hcd C L s hs hempty
  have hc' : u.stk (.inr c) = [] := by
    rw [guardedUnaryField_extra _ _ _ (by simp) (by simpa using hcd)]
    exact hempty
  have hk' : u.stk (.inr selector) = s.stk (.inr selector) :=
    guardedUnaryField_extra _ _ _ (by simp) (by simpa using hkd) s
  have hib : BoundedSelectedRowsInv p c selector C L I u :=
    ⟨⟨hi, by rw [hc']; simp⟩, by rw [hk']; exact hselector⟩
  obtain ⟨n, hn, he, hout, hg, hz⟩ := countdownRoutine_executes (.inr d)
    (selectedRowRoutine p c selector) (selectedRowEval p c selector C)
    (BoundedSelectedRowsInv p c selector C L I) (unaryFramedRowBound C L + 3)
    (boundedSelectedRowsContract p c d selector hc hd hk hcd hkc hkd C L I) u hib
  have houter := countdown_counter_le_on (.inr d) (selectedRowRoutine p c selector)
    (selectedRowEval p c selector C) (UnaryRowsInv p c C L) (unaryFramedRowBound C L + 3)
    (selectedRowsOuterContract p c d selector hc hd hk hcd hkc hkd C L) u hi
  have hcount := (guardedUnaryField_output_bound (.inl .source : NumericStack K) (.inr d) s hdempty).trans hs.1.2.2.2.2
  exact ⟨hout.1.2, houter.trans hcount, hout.2⟩

/- Bounds do not assume successful exhaustion. The selector starts at
length at most I, only loses symbols, and remains bounded even after a
failed inner row. Query C can exceed source length L; the runtime keeps
its explicit polynomial dependence rather than assuming C<=L.
-/

end PolytomyReductionModel
