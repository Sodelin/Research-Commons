/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Fully instantiated actual global descending real-block controller.
Every preparation/body/counter/invariant premise is discharged against
the concrete routines, including out-of-range operational body states.
-/
import PolytomyGlobalRealBlockBody

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem GlobalCanonicalInv_of_counter_frame (R : RawMSSCRecord) (L : ℕ)
    (s t : CanonicalGlobalStore) (hs : GlobalCanonicalInv R L s)
    (h : ∀ k : CanonicalGlobalStack, k ≠ .inr .blockCounter → t.stk k = s.stk k)
    (hu : IsUnaryWord (t.stk (.inr .blockCounter)))
    (hb : (t.stk (.inr .blockCounter)).length ≤ R.rows.length) (hf : t.state.2 = true) :
    GlobalCanonicalInv R L t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hu, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hf⟩
  · exact UnaryScanReady_of_stacks 0 L _ _ hs.scan (fun k => h (globalScanPort k) (by simp [globalScanPort]))
  · rw [h _ (by decide)]; exact hs.query_empty
  · rw [h _ (by decide)]; exact hs.parsed
  · rw [h _ (by decide)]; exact hs.universe
  · rw [h _ (by decide)]; exact hs.rows
  · rw [h _ (by decide)]; exact hs.budget
  · rw [h _ (by decide)]; exact hs.alphabet
  · rw [h _ (by decide)]; exact hs.marker
  · rw [h _ (by decide)]; exact hs.type_empty
  · rw [h _ (by decide)]; exact hs.count_empty
  · rw [h _ (by decide)]; exact hs.remaining_empty
  · rw [h _ (by decide)]; exact hs.temp_empty
  · rw [h _ (by decide)]; exact hs.cost_unary
  · rw [h _ (by decide)]; exact hs.row_bound
  · rw [h _ (by decide)]; exact hs.threshold_bound
  · rw [h _ (by decide)]; exact hs.block_bound

theorem GlobalCanonicalInv_of_stacks (R : RawMSSCRecord) (L : ℕ)
    (s t : CanonicalGlobalStore) (hs : GlobalCanonicalInv R L s)
    (h : ∀ k, t.stk k = s.stk k) (hf : t.state.2 = s.state.2) : GlobalCanonicalInv R L t := by
  apply GlobalCanonicalInv_of_counter_frame R L s t hs (fun k _ => h k)
  · rw [h]; exact hs.counter_unary
  · rw [h]; exact hs.counter_bound
  · rw [hf]; exact hs.success

theorem globalCanonical_pop (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) : GlobalCanonicalInv R L (countdownPop (.inr .blockCounter) s) := by
  apply GlobalCanonicalInv_of_counter_frame R L s _ hs
  · intro k hk; simp [countdownPop, countdownPopOp, Op.apply, hk]
  · rw [countdownPop_counter]; exact unaryWord_tail _ hs.counter_unary
  · rw [countdownPop_counter, List.length_tail]
    exact (Nat.sub_le _ _).trans hs.counter_bound
  · exact hs.success

def globalRealBlockContract (R : RawMSSCRecord) (L : ℕ) :
    CountdownContract (.inr CanonicalGlobalPort.blockCounter) globalRealBlockBodyRoutine
      (globalRealBlockBodyEval R) (GlobalCanonicalInv R L) (globalRealBlockBodyBound R L) where
  peek_closed s hs := GlobalCanonicalInv_of_stacks R L s _ hs (fun _ => rfl) rfl
  pop_closed s hs hg := globalCanonical_pop R L s hs
  body_closed s hs := by
    obtain ⟨n, hn, he, hi, ho⟩ := globalRealBlockBody_executes R L s hs
    exact hi
  reset_closed s hs := GlobalCanonicalInv_of_stacks R L s _ hs (fun _ => rfl) rfl
  counter_preserved s hs := globalRealBlockBody_globals R s .blockCounter
  body_executes s hs := by
    obtain ⟨n, hn, he, hi, ho⟩ := globalRealBlockBody_executes R L s hs
    exact ⟨n, hn, he⟩

def globalRealBlocksRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  countdownRoutine (.inr .blockCounter) globalRealBlockBodyRoutine

def globalRealBlocksEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  countdownEval (.inr .blockCounter) (globalRealBlockBodyEval R) s

def globalRealBlocksBound (R : RawMSSCRecord) (L : ℕ) :=
  R.rows.length * (globalRealBlockBodyBound R L + 3) + 3

theorem globalRealBlocks_original_preserved (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) :
    (globalRealBlocksEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
  have hb : ∀ t, GlobalCanonicalInv R L t →
      (globalRealBlockBodyEval R t).stk (globalScanPort (.inr .original)) = t.stk (globalScanPort (.inr .original)) := by
    intro t ht
    obtain ⟨n, hn, he, hi, ho⟩ := globalRealBlockBody_executes R L t ht
    exact ho
  exact countdownLoop_preserves_on (.inr .blockCounter) globalRealBlockBodyRoutine (globalRealBlockBodyEval R)
    (GlobalCanonicalInv R L) (globalRealBlockBodyBound R L) (globalRealBlockContract R L)
    (fun t => t.stk (globalScanPort (.inr .original))) (fun _ => rfl)
    (by intro t; simp [countdownPop, countdownPopOp, Op.apply, globalScanPort]) hb
    (s.stk (.inr .blockCounter)).length (countdownPeek (.inr .blockCounter) s)
    ((globalRealBlockContract R L).peek_closed s hs)

theorem globalRealBlocks_executes (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) :
    ∃ n ≤ globalRealBlocksBound R L,
      globalRealBlocksRoutine.Executes s (globalRealBlocksEval R s) n ∧
      GlobalCanonicalInv R L (globalRealBlocksEval R s) ∧
      (globalRealBlocksEval R s).stk (.inr .blockCounter) = [] ∧
      (globalRealBlocksEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
  obtain ⟨n, hn, he, hi, hg, hc⟩ := countdownRoutine_executes (.inr .blockCounter) globalRealBlockBodyRoutine
    (globalRealBlockBodyEval R) (GlobalCanonicalInv R L) (globalRealBlockBodyBound R L)
    (globalRealBlockContract R L) s hs
  have hm := Nat.mul_le_mul_right (globalRealBlockBodyBound R L + 3) hs.counter_bound
  exact ⟨n, by unfold globalRealBlocksBound; omega, he, hi, hc hi.success,
    globalRealBlocks_original_preserved R L s hs⟩

theorem canonicalGlobals_starts_outer (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = [])
    (hglobals : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = [])
    (hfilters : ∀ k : CanonicalFilterPort, s.stk (globalFilterPort k) = [])
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ canonicalGlobalsBound L, canonicalGlobalsRoutine.Executes s (canonicalGlobalsEval R s) n ∧
      GlobalCanonicalInv R L (canonicalGlobalsEval R s) ∧
      (canonicalGlobalsEval R s).stk (.inr .blockCounter) = List.replicate R.rows.length true ∧
      (canonicalGlobalsEval R s).stk (globalFilterPort .cost) = [] ∧
      (canonicalGlobalsEval R s).stk (globalFilterPort .output) = [] := by
  obtain ⟨n, hn, he, hready, hquery, horig, hN, hM, hK, hA, hT, hcounter, hpres, hflag⟩ :=
    canonicalGlobals_executes R hR L s hs hq hglobals hparse
  have hf : ∀ k : CanonicalFilterPort, (canonicalGlobalsEval R s).stk (globalFilterPort k) = [] := by
    intro k; rw [hpres]; exact hfilters k
  have hi : GlobalCanonicalInv R L (canonicalGlobalsEval R s) := by
    refine ⟨hready, hquery, ?_, hN, hM, hK, hA, hT, ?_, ?_, hf .typeIndex, hf .count,
      hf .remaining, hf .temp, ?_, ?_, ?_, ?_, hflag⟩
    · rw [horig]; exact hparse
    · simp [hcounter, IsUnaryWord]
    · simp [hcounter]
    · simp [hf, IsUnaryWord]
    · simp [hf]
    · simp [hf]
    · simp [hf]
  exact ⟨n, hn, he, hi, hcounter, hf .cost, hf .output⟩

/- The outer routine and body are now ACTUAL, with every loop premise
instantiated. An initial true^m really visits m-1,...,0. Ordered ORIGINAL
block bytes and the full C0 fold must be joined to this operational loop,
then the prepared anchor, original budget/headers and standalone caller.
No whole-constructor/checker/hardness/kernel closure is claimed here.
-/

end PolytomyReductionModel
