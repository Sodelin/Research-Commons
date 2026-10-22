/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual ORIGINAL row-specific membership body. A disposable physical row
selector is popped once per row. Fixed chosen/active bits ensure that
only the first row reached after selector exhaustion is active. Query C
remains on the physical cap tape. This is not flattened-row membership.
-/
import PolytomyCanonicalCombPrefix
import PolytomyUnaryRowsPredicates

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

@[ext] structure SelectedRowFrame where
  found : Bool
  chosen : Bool
  active : Bool
  deriving DecidableEq, Fintype

def selectedRowStart (f : SelectedRowFrame) (empty : Bool) : SelectedRowFrame :=
  ⟨f.found, f.chosen || empty, !f.chosen && empty⟩

def selectedRowBump (f : SelectedRowFrame) (hit : Bool) : SelectedRowFrame :=
  ⟨f.found || (f.active && hit), f.chosen, f.active⟩

variable {K : Type} [DecidableEq K]

def selectedRowStartOp (selector : K) : Op (NumericStack K) Bool (CountdownState SelectedRowFrame) :=
  .peek (.inr selector) (fun s h => ((selectedRowStart s.1.1 (!h.isSome), s.1.2), s.2))

def selectedRowStartRoutine (selector : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (Atom.routine (selectedRowStartOp selector)) (Atom.routine (countdownPopOp (.inr selector)))

def selectedRowStartEval (selector : K) (s : CountdownStore (NumericStack K) SelectedRowFrame) :=
  countdownPop (.inr selector) ((selectedRowStartOp selector).apply s)

theorem selectedRowStart_executes (selector : K) (s : CountdownStore (NumericStack K) SelectedRowFrame) :
    (selectedRowStartRoutine selector).Executes s (selectedRowStartEval selector s) 2 :=
  RoutineComposition.seq_executes _ _ (Atom.executes (selectedRowStartOp selector) s)
    (Atom.executes (countdownPopOp (.inr selector)) ((selectedRowStartOp selector).apply s))

theorem selectedRowStart_invariant (p : UnaryVisitPorts K) (c selector : K)
    (hk : UnaryVisitOutside p selector) (hkc : selector ≠ c) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    UnaryRowsInv p c C L (selectedRowStartEval selector s) := by
  rcases hk with ⟨hkm, hkt, hkl, hkr⟩
  simpa [UnaryRowsInv, UnaryVisitInv, NumericLoopInv, selectedRowStartEval,
    selectedRowStartOp, countdownPop, countdownPopOp, Op.apply,
    Ne.symm hkm, Ne.symm hkt, Ne.symm hkl, Ne.symm hkr, Ne.symm hkc] using hs

def selectedRowRoutine (p : UnaryVisitPorts K) (c selector : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (selectedRowStartRoutine selector)
    (guardedUnaryRowRoutine p c .equal selectedRowBump)

def selectedRowEval (p : UnaryVisitPorts K) (c selector : K) (C : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) :=
  guardedUnaryRowEval p c .equal selectedRowBump C (selectedRowStartEval selector s)

theorem selectedRow_executes (p : UnaryVisitPorts K) (c selector : K)
    (hc : UnaryVisitOutside p c) (hk : UnaryVisitOutside p selector) (hkc : selector ≠ c)
    (C L : ℕ) (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    ∃ n ≤ unaryFramedRowBound C L + 3,
      (selectedRowRoutine p c selector).Executes s (selectedRowEval p c selector C s) n ∧
      UnaryRowsInv p c C L (selectedRowEval p c selector C s) := by
  have hi := selectedRowStart_invariant p c selector hk hkc C L s hs
  obtain ⟨n, hn, he, hout⟩ := guardedUnaryRow_executes p c hc .equal selectedRowBump C L
    (selectedRowStartEval selector s) hi
  exact ⟨2 + n, by omega,
    RoutineComposition.seq_executes _ _ (selectedRowStart_executes selector s) he, hout⟩

theorem selectedRow_selector (p : UnaryVisitPorts K) (c selector : K)
    (hc : UnaryVisitOutside p c) (hk : UnaryVisitOutside p selector) (hkc : selector ≠ c)
    (C L : ℕ) (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    (selectedRowEval p c selector C s).stk (.inr selector) = (s.stk (.inr selector)).tail := by
  rw [selectedRowEval, guardedUnaryRow_extra p c selector hc hkc .equal selectedRowBump C L _
    (selectedRowStart_invariant p c selector hk hkc C L s hs)]
  simp [selectedRowStartEval, selectedRowStartOp, countdownPop, countdownPopOp, Op.apply]

theorem selectedRow_extra (p : UnaryVisitPorts K) (c selector k : K)
    (hc : UnaryVisitOutside p c) (hk : UnaryVisitOutside p selector) (hkc : selector ≠ c)
    (hkeyc : k ≠ c) (hkeysel : k ≠ selector) (C L : ℕ)
    (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    (selectedRowEval p c selector C s).stk (.inr k) = s.stk (.inr k) := by
  rw [selectedRowEval, guardedUnaryRow_extra p c k hc hkeyc .equal selectedRowBump C L _
    (selectedRowStart_invariant p c selector hk hkc C L s hs)]
  simp [selectedRowStartEval, selectedRowStartOp, countdownPop, countdownPopOp, Op.apply, hkeysel]

theorem selectedRow_observation (p : UnaryVisitPorts K) (c selector : K)
    (hc : UnaryVisitOutside p c) (hk : UnaryVisitOutside p selector) (hkc : selector ≠ c)
    (C L : ℕ) (s : CountdownStore (NumericStack K) SelectedRowFrame) (hs : UnaryRowsInv p c C L s) :
    unaryVisitObservation (selectedRowEval p c selector C s) =
      if s.state.2 then (readFramedList readUnaryFrame (s.stk (.inl .source))).map
        (fun q => (q.2, q.1.foldl (unaryVisitStep .equal selectedRowBump C)
          (selectedRowStart s.state.1.1 (decide ((s.stk (.inr selector)).length = 0))))) else none := by
  have h := guardedUnaryRow_observation p c hc .equal selectedRowBump C L
    (selectedRowStartEval selector s) (selectedRowStart_invariant p c selector hk hkc C L s hs)
  have hz : !(s.stk (.inr selector)).head?.isSome = decide ((s.stk (.inr selector)).length = 0) := by
    cases s.stk (.inr selector) <;> simp
  simpa [selectedRowEval, selectedRowStartEval, selectedRowStartOp,
    countdownPop, countdownPopOp, Op.apply, hz] using h

theorem selectedRow_fold (C : ℕ) (row : List ℕ) : ∀ f : SelectedRowFrame,
    row.foldl (unaryVisitStep .equal selectedRowBump C) f =
      ⟨f.found || (f.active && decide (C ∈ row)), f.chosen, f.active⟩ := by
  induction row with
  | nil => intro f; cases f; simp
  | cons x xs ih =>
      intro f
      rw [List.foldl_cons, ih]
      rcases f with ⟨found, chosen, active⟩
      by_cases hx : x = C <;> by_cases hm : C ∈ xs <;> cases found <;> cases active <;>
        simp_all [unaryVisitStep, unaryVisitTest, selectedRowBump, eq_comm]

/- The selector is intentionally CONSUMED, unlike the original block
index that the eventual controller must copy into it. Chosen prevents
all later rows from becoming active after the selector has emptied.
Even an empty selected row consumes this one-row opportunity. Comparison
nonmatches are successful syntax, not a reason to stop the parser.
The actual outer selection loop and whole-record replay remain to join.
-/

end PolytomyReductionModel
