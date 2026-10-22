/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

All four ORIGINAL dispatch conditions computed by actual finite-control
instructions and physical operand routines. The three saved bits are
N=0, m<=1, N<=K; success holds N*m<=K. Every tape is restored unchanged.
-/
import PolytomyPhysicalDispatchCompare

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def dispatchEmptyOp (k : CanonicalGlobalStack) : Op CanonicalGlobalStack Bool (CountdownState SelectedRowFrame) :=
  .peek k (fun s h => (s.1, !h.isSome))

theorem dispatchEmpty_executes (k : CanonicalGlobalStack) (N : ℕ) (s : CanonicalGlobalStore)
    (hN : s.stk k = List.replicate N true) :
    (Atom.routine (dispatchEmptyOp k)).Executes s (dispatchFlagStore (decide (N = 0)) s) 1 := by
  have hout : (dispatchEmptyOp k).apply s = dispatchFlagStore (decide (N = 0)) s := by
    apply countdownStore_ext
    · cases N <;> simp [dispatchEmptyOp, Op.apply, dispatchFlagStore, hN, List.replicate_succ]
    · rfl
  rw [← hout]
  exact Atom.executes _ _

def smallRowsCopied (s : CanonicalGlobalStore) := wordDuplicateEval (.inr .rowCount) (globalFilterPort .count) s
def smallRowsPopped (s : CanonicalGlobalStore) := countdownPop (globalFilterPort .count) (smallRowsCopied s)
def smallRowsTested (s : CanonicalGlobalStore) := (dispatchEmptyOp (globalFilterPort .count)).apply (smallRowsPopped s)
def smallRowsEval (s : CanonicalGlobalStore) := clearStackEval (globalFilterPort .count) (smallRowsTested s)

def smallRowsRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (wordDuplicateRoutine (.inr .rowCount) (globalFilterPort .temp) (globalFilterPort .count))
    (RoutineComposition.seq (Atom.routine (countdownPopOp (globalFilterPort .count)))
      (RoutineComposition.seq (Atom.routine (dispatchEmptyOp (globalFilterPort .count)))
        (clearStackRoutine (globalFilterPort .count))))

theorem smallRows_result (m : ℕ) (s : CanonicalGlobalStore)
    (hm : s.stk (.inr .rowCount) = List.replicate m true) (hc : s.stk (globalFilterPort .count) = []) :
    smallRowsEval s = dispatchFlagStore (decide (m ≤ 1)) s := by
  apply countdownStore_ext
  · cases m with
    | zero => simp [smallRowsEval, clearStackEval, smallRowsTested, dispatchEmptyOp, smallRowsPopped,
        countdownPop, countdownPopOp, smallRowsCopied, wordDuplicateEval, dispatchFlagStore, Op.apply, hm, hc]
    | succ m => cases m <;> simp [smallRowsEval, clearStackEval, smallRowsTested, dispatchEmptyOp,
        smallRowsPopped, countdownPop, countdownPopOp, smallRowsCopied, wordDuplicateEval,
        dispatchFlagStore, Op.apply, hm, hc, List.replicate_succ]
  · funext k
    by_cases hk : k = globalFilterPort .count
    · subst k; simp [smallRowsEval, clearStackEval, dispatchFlagStore, hc]
    · simp [smallRowsEval, clearStackEval, smallRowsTested, dispatchEmptyOp, smallRowsPopped,
        countdownPop, countdownPopOp, smallRowsCopied, wordDuplicateEval, dispatchFlagStore, Op.apply, hk]

theorem smallRows_executes (m : ℕ) (s : CanonicalGlobalStore)
    (hm : s.stk (.inr .rowCount) = List.replicate m true)
    (hc : s.stk (globalFilterPort .count) = []) (ht : s.stk (globalFilterPort .temp) = []) :
    ∃ n ≤ 4 * m + 6, smallRowsRoutine.Executes s (dispatchFlagStore (decide (m ≤ 1)) s) n := by
  have h1 := wordDuplicate_executes (.inr CanonicalGlobalPort.rowCount : CanonicalGlobalStack)
    (globalFilterPort .temp) (globalFilterPort .count) (by decide) (by decide) (by decide) s ht
  rw [hm, List.length_replicate] at h1
  have h2 := Atom.executes (countdownPopOp (globalFilterPort .count)) (smallRowsCopied s)
  have h3 := Atom.executes (dispatchEmptyOp (globalFilterPort .count)) (smallRowsPopped s)
  have h4 := clearStack_executes (globalFilterPort .count) (smallRowsTested s)
  have hlen : ((smallRowsTested s).stk (globalFilterPort .count)).length = m - 1 := by
    cases m <;> simp [smallRowsTested, dispatchEmptyOp, Op.apply, smallRowsPopped, countdownPop,
      countdownPopOp, smallRowsCopied, wordDuplicateEval, hm, hc, List.replicate_succ]
  rw [hlen] at h4
  have hall := RoutineComposition.seq_executes _ _ h1
    (RoutineComposition.seq_executes _ _ h2 (RoutineComposition.seq_executes _ _ h3 h4))
  change smallRowsRoutine.Executes s (smallRowsEval s) ((3 * m + 3) + (1 + (1 + (m - 1 + 1)))) at hall
  rw [smallRows_result m s hm hc] at hall
  exact ⟨_, by omega, hall⟩

def dispatchSaveFound : Op CanonicalGlobalStack Bool (CountdownState SelectedRowFrame) :=
  .load (fun s => ((⟨s.2, s.1.1.chosen, s.1.1.active⟩, s.1.2), s.2))
def dispatchSaveChosen : Op CanonicalGlobalStack Bool (CountdownState SelectedRowFrame) :=
  .load (fun s => ((⟨s.1.1.found, s.2, s.1.1.active⟩, s.1.2), s.2))
def dispatchSaveActive : Op CanonicalGlobalStack Bool (CountdownState SelectedRowFrame) :=
  .load (fun s => ((⟨s.1.1.found, s.1.1.chosen, s.2⟩, s.1.2), s.2))

def originalDispatchFlag1 (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  dispatchSaveFound.apply (dispatchFlagStore (decide (R.N = 0)) s)
def originalDispatchFlag2 (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  dispatchSaveChosen.apply (dispatchFlagStore (decide (R.rows.length ≤ 1)) (originalDispatchFlag1 R s))
def originalDispatchFlag3 (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  dispatchSaveActive.apply (dispatchFlagStore (decide (R.N ≤ R.K)) (originalDispatchFlag2 R s))

def originalDispatchFlags (R : RawMSSCRecord) (s : CanonicalGlobalStore) : CanonicalGlobalStore :=
  ⟨((⟨decide (R.N = 0), decide (R.rows.length ≤ 1), decide (R.N ≤ R.K)⟩, s.state.1.2),
    decide (R.N * R.rows.length ≤ R.K)), s.stk⟩

def originalDispatchFlagsRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (Atom.routine (dispatchEmptyOp (.inr .universe)))
    (RoutineComposition.seq (Atom.routine dispatchSaveFound)
      (RoutineComposition.seq smallRowsRoutine
        (RoutineComposition.seq (Atom.routine dispatchSaveChosen)
          (RoutineComposition.seq (dispatchCompareRoutine originalBudgetUniversePorts)
            (RoutineComposition.seq (Atom.routine dispatchSaveActive) (dispatchCompareRoutine originalBudgetProductPorts))))))

def originalDispatchFlagsBound (R : RawMSSCRecord) :=
  4 * (R.N * R.rows.length) + 4 * R.N + 4 * R.rows.length + 8 * R.K + 26

theorem originalDispatchFlags_executes (R : RawMSSCRecord) (s : CanonicalGlobalStore)
    (hN : s.stk (.inr .universe) = List.replicate R.N true)
    (hm : s.stk (.inr .rowCount) = List.replicate R.rows.length true)
    (hK : s.stk (.inr .budget) = List.replicate R.K true)
    (hP : s.stk (globalScanPort (.inr .savedCount)) = List.replicate (R.N * R.rows.length) true)
    (hfilter : ∀ k : CanonicalFilterPort, s.stk (globalFilterPort k) = []) :
    ∃ n ≤ originalDispatchFlagsBound R,
      originalDispatchFlagsRoutine.Executes s (originalDispatchFlags R s) n := by
  have h0 := dispatchEmpty_executes (.inr CanonicalGlobalPort.universe) R.N s hN
  have h1 := Atom.executes dispatchSaveFound (dispatchFlagStore (decide (R.N = 0)) s)
  obtain ⟨a, ha, he2⟩ := smallRows_executes R.rows.length (originalDispatchFlag1 R s) hm
    (hfilter .count) (hfilter .temp)
  have h3 := Atom.executes dispatchSaveChosen
    (dispatchFlagStore (decide (R.rows.length ≤ 1)) (originalDispatchFlag1 R s))
  obtain ⟨b, hb, he4⟩ := dispatchCompare_executes originalBudgetUniversePorts R.K R.N
    (originalDispatchFlag2 R s) hK hN (hfilter .typeIndex) (hfilter .remaining) (hfilter .temp)
  have h5 := Atom.executes dispatchSaveActive
    (dispatchFlagStore (decide (R.N ≤ R.K)) (originalDispatchFlag2 R s))
  obtain ⟨c, hc, he6⟩ := dispatchCompare_executes originalBudgetProductPorts R.K (R.N * R.rows.length)
    (originalDispatchFlag3 R s) hK hP (hfilter .typeIndex) (hfilter .remaining) (hfilter .temp)
  have hout : dispatchFlagStore (decide (R.N * R.rows.length ≤ R.K)) (originalDispatchFlag3 R s) =
      originalDispatchFlags R s := rfl
  rw [hout] at he6
  have hall := RoutineComposition.seq_executes _ _ h0
    (RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ he2
      (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ he4
        (RoutineComposition.seq_executes _ _ h5 he6)))))
  exact ⟨1 + (1 + (a + (1 + (b + (1 + c))))), by unfold originalDispatchFlagsBound; omega, hall⟩

/- All data in the result are definitionally the SAME s.stk. None of
these tests changes the original row order, input record or output.
This is not yet the complete dispatch/standalone constructor theorem.
-/

end PolytomyReductionModel
