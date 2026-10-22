/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual reusable per-block preparation from the already physically created
global words. Two fixed modes select real-block versus anchor setup;
there is no natural parameter in the finite control or a free word copy.
-/
import PolytomyOperationalBlockContract

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def blockPrepareOwned : List CanonicalGlobalStack :=
  [globalFilterPort .rowIndex, globalFilterPort .threshold, globalFilterPort .blockCode]

def blockPrepareTailRoutine (realBlock : Bool) (rowSource : CanonicalGlobalPort) :
    Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  if realBlock then
    RoutineComposition.seq (wordDuplicateRoutine (.inr rowSource) (globalFilterPort .temp) (globalFilterPort .blockCode))
      (Atom.routine (prependBitOp (globalFilterPort .blockCode) true))
  else Atom.routine cleanupNoop

def blockPrepareTailEval (realBlock : Bool) (rowSource : CanonicalGlobalPort) (s : CanonicalGlobalStore) :=
  if realBlock then (prependBitOp (globalFilterPort .blockCode) true).apply
    (wordDuplicateEval (.inr rowSource) (globalFilterPort .blockCode) s) else s

theorem blockPrepareTail_executes (realBlock : Bool) (rowSource : CanonicalGlobalPort)
    (s : CanonicalGlobalStore) (ht : s.stk (globalFilterPort .temp) = []) :
    ∃ n ≤ 3 * (s.stk (.inr rowSource)).length + 4,
      (blockPrepareTailRoutine realBlock rowSource).Executes s (blockPrepareTailEval realBlock rowSource s) n := by
  cases realBlock with
  | false => exact ⟨1, by omega, Atom.executes cleanupNoop s⟩
  | true =>
      have h1 := wordDuplicate_executes (.inr rowSource : CanonicalGlobalStack)
        (globalFilterPort .temp) (globalFilterPort .blockCode) (by simp [globalFilterPort])
        (by simp [globalFilterPort]) (by decide) s ht
      have h2 := Atom.executes (prependBitOp (globalFilterPort .blockCode) true)
        (wordDuplicateEval (.inr rowSource) (globalFilterPort .blockCode) s)
      exact ⟨(3 * (s.stk (.inr rowSource)).length + 3) + 1, by omega,
        RoutineComposition.seq_executes _ _ h1 h2⟩

def blockPrepared0 (s : CanonicalGlobalStore) := clearManyEval blockPrepareOwned s
def blockPrepared1 (s : CanonicalGlobalStore) := wordDuplicateEval (.inr .alphabet) (globalFilterPort .typeIndex) (blockPrepared0 s)
def blockPrepared2 (s : CanonicalGlobalStore) := wordDuplicateEval (.inr .alphabet) (globalFilterPort .remaining) (blockPrepared1 s)
def blockPrepared3 (row : CanonicalGlobalPort) (s : CanonicalGlobalStore) :=
  wordDuplicateEval (.inr row) (globalFilterPort .rowIndex) (blockPrepared2 s)
def blockPrepared4 (row threshold : CanonicalGlobalPort) (s : CanonicalGlobalStore) :=
  wordDuplicateEval (.inr threshold) (globalFilterPort .threshold) (blockPrepared3 row s)
def physicalBlockPrepareEval (realBlock : Bool) (row threshold : CanonicalGlobalPort) (s : CanonicalGlobalStore) :=
  blockPrepareTailEval realBlock row (blockPrepared4 row threshold s)

def physicalBlockPrepareRoutine (realBlock : Bool) (row threshold : CanonicalGlobalPort) :
    Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (clearManyRoutine blockPrepareOwned)
  (RoutineComposition.seq (wordDuplicateRoutine (.inr .alphabet) (globalFilterPort .temp) (globalFilterPort .typeIndex))
  (RoutineComposition.seq (wordDuplicateRoutine (.inr .alphabet) (globalFilterPort .temp) (globalFilterPort .remaining))
  (RoutineComposition.seq (wordDuplicateRoutine (.inr row) (globalFilterPort .temp) (globalFilterPort .rowIndex))
  (RoutineComposition.seq (wordDuplicateRoutine (.inr threshold) (globalFilterPort .temp) (globalFilterPort .threshold))
    (blockPrepareTailRoutine realBlock row)))))

def physicalBlockPrepareBound (row threshold : CanonicalGlobalPort) (s : CanonicalGlobalStore) :=
  cleanupMass blockPrepareOwned s + 6 * (s.stk (.inr .alphabet)).length +
    6 * (s.stk (.inr row)).length + 3 * (s.stk (.inr threshold)).length + 20

theorem physicalBlockPrepare_executes (realBlock : Bool) (row threshold : CanonicalGlobalPort)
    (s : CanonicalGlobalStore) (ht : s.stk (globalFilterPort .temp) = []) :
    ∃ n ≤ physicalBlockPrepareBound row threshold s,
      (physicalBlockPrepareRoutine realBlock row threshold).Executes s (physicalBlockPrepareEval realBlock row threshold s) n := by
  obtain ⟨a, ha, he0⟩ := clearMany_executes blockPrepareOwned s
  have ht0 : (blockPrepared0 s).stk (globalFilterPort .temp) = [] := by
    rw [clearMany_outside _ _ (by simp [blockPrepareOwned, globalFilterPort])]; exact ht
  have he1 := wordDuplicate_executes (.inr CanonicalGlobalPort.alphabet : CanonicalGlobalStack)
    (globalFilterPort .temp) (globalFilterPort .typeIndex) (by decide) (by decide) (by decide) (blockPrepared0 s) ht0
  have ht1 : (blockPrepared1 s).stk (globalFilterPort .temp) = [] := by
    simpa [blockPrepared1, wordDuplicateEval, globalFilterPort] using ht0
  have he2 := wordDuplicate_executes (.inr CanonicalGlobalPort.alphabet : CanonicalGlobalStack)
    (globalFilterPort .temp) (globalFilterPort .remaining) (by decide) (by decide) (by decide) (blockPrepared1 s) ht1
  have ht2 : (blockPrepared2 s).stk (globalFilterPort .temp) = [] := by
    simpa [blockPrepared2, wordDuplicateEval, globalFilterPort] using ht1
  have he3 := wordDuplicate_executes (.inr row : CanonicalGlobalStack) (globalFilterPort .temp)
    (globalFilterPort .rowIndex) (by simp [globalFilterPort]) (by simp [globalFilterPort]) (by decide) (blockPrepared2 s) ht2
  have ht3 : (blockPrepared3 row s).stk (globalFilterPort .temp) = [] := by
    simpa [blockPrepared3, wordDuplicateEval, globalFilterPort] using ht2
  have he4 := wordDuplicate_executes (.inr threshold : CanonicalGlobalStack) (globalFilterPort .temp)
    (globalFilterPort .threshold) (by simp [globalFilterPort]) (by simp [globalFilterPort]) (by decide) (blockPrepared3 row s) ht3
  have ht4 : (blockPrepared4 row threshold s).stk (globalFilterPort .temp) = [] := by
    simpa [blockPrepared4, wordDuplicateEval, globalFilterPort] using ht3
  obtain ⟨b, hb, he5⟩ := blockPrepareTail_executes realBlock row (blockPrepared4 row threshold s) ht4
  have globals0 : ∀ k : CanonicalGlobalPort, (blockPrepared0 s).stk (.inr k) = s.stk (.inr k) := by
    intro k; exact clearMany_outside _ _ (by simp [blockPrepareOwned, globalFilterPort]) s
  have globals1 : ∀ k : CanonicalGlobalPort, (blockPrepared1 s).stk (.inr k) = s.stk (.inr k) := by
    intro k; simpa [blockPrepared1, wordDuplicateEval, globalFilterPort] using globals0 k
  have globals2 : ∀ k : CanonicalGlobalPort, (blockPrepared2 s).stk (.inr k) = s.stk (.inr k) := by
    intro k; simpa [blockPrepared2, wordDuplicateEval, globalFilterPort] using globals1 k
  have globals3 : ∀ k : CanonicalGlobalPort, (blockPrepared3 row s).stk (.inr k) = s.stk (.inr k) := by
    intro k; simpa [blockPrepared3, wordDuplicateEval, globalFilterPort] using globals2 k
  have globals4 : ∀ k : CanonicalGlobalPort, (blockPrepared4 row threshold s).stk (.inr k) = s.stk (.inr k) := by
    intro k; simpa [blockPrepared4, wordDuplicateEval, globalFilterPort] using globals3 k
  rw [globals0] at he1
  rw [globals1] at he2
  rw [globals2] at he3
  rw [globals3] at he4
  rw [globals4] at hb
  have hall := RoutineComposition.seq_executes _ _ he0
    (RoutineComposition.seq_executes _ _ he1 (RoutineComposition.seq_executes _ _ he2
    (RoutineComposition.seq_executes _ _ he3 (RoutineComposition.seq_executes _ _ he4 he5))))
  have hlen : blockPrepareOwned.length = 3 := rfl
  rw [hlen] at ha
  refine ⟨a + ((3 * (s.stk (.inr .alphabet)).length + 3) + ((3 * (s.stk (.inr .alphabet)).length + 3) +
    ((3 * (s.stk (.inr row)).length + 3) + ((3 * (s.stk (.inr threshold)).length + 3) + b)))), ?_, hall⟩
  unfold physicalBlockPrepareBound; omega

theorem physicalBlockPrepare_state (realBlock : Bool) (row threshold : CanonicalGlobalPort) (s : CanonicalGlobalStore) :
    (physicalBlockPrepareEval realBlock row threshold s).state = s.state := by
  cases realBlock <;> simpa [physicalBlockPrepareEval, blockPrepareTailEval, blockPrepared4, blockPrepared3,
    blockPrepared2, blockPrepared1, blockPrepared0, prependBitOp, Op.apply, wordDuplicateEval]
    using clearMany_state blockPrepareOwned s

theorem physicalBlockPrepare_extra (realBlock : Bool) (row threshold : CanonicalGlobalPort)
    (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (htype : k ≠ globalFilterPort .typeIndex) (hrem : k ≠ globalFilterPort .remaining)
    (hrow : k ≠ globalFilterPort .rowIndex) (hthreshold : k ≠ globalFilterPort .threshold)
    (hblock : k ≠ globalFilterPort .blockCode) :
    (physicalBlockPrepareEval realBlock row threshold s).stk k = s.stk k := by
  have h0 := clearMany_outside blockPrepareOwned k
    (by simp [blockPrepareOwned, hrow, hthreshold, hblock]) s
  cases realBlock <;>
    simpa [physicalBlockPrepareEval, blockPrepareTailEval, blockPrepared4, blockPrepared3,
      blockPrepared2, blockPrepared1, blockPrepared0, prependBitOp, Op.apply, wordDuplicateEval,
      htype, hrem, hrow, hthreshold, hblock] using h0

theorem physicalBlockPrepare_values (realBlock : Bool) (row threshold : CanonicalGlobalPort)
    (A i T : ℕ) (s : CanonicalGlobalStore)
    (hA : s.stk (.inr .alphabet) = List.replicate A true)
    (hi : s.stk (.inr row) = List.replicate i true)
    (hT : s.stk (.inr threshold) = List.replicate T true)
    (htype : s.stk (globalFilterPort .typeIndex) = [])
    (hrem : s.stk (globalFilterPort .remaining) = []) :
    (physicalBlockPrepareEval realBlock row threshold s).stk (globalFilterPort .typeIndex) = List.replicate A true ∧
      (physicalBlockPrepareEval realBlock row threshold s).stk (globalFilterPort .remaining) = List.replicate A true ∧
      (physicalBlockPrepareEval realBlock row threshold s).stk (globalFilterPort .rowIndex) = List.replicate i true ∧
      (physicalBlockPrepareEval realBlock row threshold s).stk (globalFilterPort .threshold) = List.replicate T true ∧
      (physicalBlockPrepareEval realBlock row threshold s).stk (globalFilterPort .blockCode) =
        List.replicate (if realBlock then i + 1 else 0) true := by
  cases realBlock <;>
    simp [physicalBlockPrepareEval, blockPrepareTailEval, blockPrepared4, blockPrepared3,
      blockPrepared2, blockPrepared1, blockPrepared0, blockPrepareOwned, clearManyEval,
      clearStackEval, prependBitOp, Op.apply, wordDuplicateEval, globalFilterPort,
      hA, hi, hT, htype, hrem, List.replicate_succ]

/- The real fixed setup chooses (true, blockCounter, markerThreshold).
The anchor fixed setup chooses (false, rowCount, universe). Both use the
already physical global alphabet. Old row/threshold/block values are really
cleared before copying. Type/remaining inputs must be fresh from the prior
block endpoint or initial blank caller tapes. Count/cost/output, global
counter and original source are preserved, not silently initialized.
Full actual outer controller and complete original serializer remain.
-/

end PolytomyReductionModel
