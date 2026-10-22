/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual physical anchor preparation followed by the SAME complete block
program. It copies rowCount m, universe N and alphabet A; block code is
really cleared to zero. No fabricated source row or anchor oracle.
-/
import PolytomyOriginalOuterLoopFold

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem originalUniverse_le_alphabet (R : RawMSSCRecord) : R.N ≤ rawRowAlphabet R := by
  unfold rawRowAlphabet
  omega

def globalAnchorBlockPrepared (s : CanonicalGlobalStore) :=
  physicalBlockPrepareEval false .rowCount .universe s

def globalAnchorBlockBodyRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (physicalBlockPrepareRoutine false .rowCount .universe)
    (extraPortsRoutine (E := CanonicalGlobalPort) originalCanonicalBlockRoutine)

def globalAnchorBlockBodyEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  extraPortsStore (operationalBlockEval (R.N) (canonicalGlobalBase (globalAnchorBlockPrepared s)))
    (canonicalGlobalExtra (globalAnchorBlockPrepared s))

def globalAnchorBlockBodyBound (R : RawMSSCRecord) (L : ℕ) :=
  10 * rawRowAlphabet R + 8 * R.rows.length + 21 +
    operationalBlockBound L (rawRowAlphabet R) R.rows.length (R.N) (R.rows.length + 1)

theorem globalAnchorBlockBody_globals (R : RawMSSCRecord) (s : CanonicalGlobalStore) (k : CanonicalGlobalPort) :
    (globalAnchorBlockBodyEval R s).stk (.inr k) = s.stk (.inr k) :=
  physicalBlockPrepare_extra false .rowCount .universe s (.inr k)
    (by simp [globalFilterPort]) (by simp [globalFilterPort]) (by simp [globalFilterPort])
    (by simp [globalFilterPort]) (by simp [globalFilterPort])

theorem globalAnchorPrepared_old (s : CanonicalGlobalStore) (k : NumericStack UnaryScanPort) :
    (globalAnchorBlockPrepared s).stk (globalScanPort k) = s.stk (globalScanPort k) :=
  physicalBlockPrepare_extra false .rowCount .universe s (globalScanPort k)
    (by simp [globalFilterPort, globalScanPort]) (by simp [globalFilterPort, globalScanPort])
    (by simp [globalFilterPort, globalScanPort]) (by simp [globalFilterPort, globalScanPort])
    (by simp [globalFilterPort, globalScanPort])

theorem globalAnchorPrepared_ready (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) :
    RealTypeLoopInv L (rawRowAlphabet R) R.rows.length (R.N) (R.rows.length + 1)
      (canonicalGlobalBase (globalAnchorBlockPrepared s)) ∧
      RealTypeUnaryData (canonicalGlobalBase (globalAnchorBlockPrepared s)) ∧
      (canonicalGlobalBase (globalAnchorBlockPrepared s)).stk (.inr .count) = [] ∧
      (globalAnchorBlockPrepared s).state.2 = true := by
  let i := R.rows.length
  obtain ⟨hA, hrem, hrow, hT, hblock⟩ := physicalBlockPrepare_values false .rowCount .universe
    (rawRowAlphabet R) i (R.N) s hs.alphabet hs.rows hs.universe hs.type_empty hs.remaining_empty
  have hcnt : (globalAnchorBlockPrepared s).stk (globalFilterPort .count) = [] := by
    rw [physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hs.count_empty
  have htmp : (globalAnchorBlockPrepared s).stk (globalFilterPort .temp) = [] := by
    rw [physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hs.temp_empty
  have hcost : IsUnaryWord ((globalAnchorBlockPrepared s).stk (globalFilterPort .cost)) := by
    rw [physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hs.cost_unary
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hT, htmp, ?_, ?_⟩, ⟨?_, ?_, hcost⟩, hcnt, ?_⟩
  · exact UnaryScanReady_of_stacks 0 L _ _ hs.scan (globalAnchorPrepared_old s)
  · rw [show (globalAnchorBlockPrepared s).stk (globalScanPort (.inr .queries)) =
      s.stk (globalScanPort (.inr .queries)) from globalAnchorPrepared_old s _]; exact hs.query_empty
  · simp [hA, IsUnaryWord]
  · simp [hA]
  · rw [hrow, List.length_replicate]; exact le_rfl
  · simp [hrem]
  · simp [hblock]
  · simp [hrem, IsUnaryWord]
  · simp [hcnt, IsUnaryWord]
  · rw [physicalBlockPrepare_state]; exact hs.success

theorem globalAnchorBlockBody_executes (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) :
    ∃ n ≤ globalAnchorBlockBodyBound R L,
      globalAnchorBlockBodyRoutine.Executes s (globalAnchorBlockBodyEval R s) n ∧
      GlobalCanonicalInv R L (globalAnchorBlockBodyEval R s) ∧
      (globalAnchorBlockBodyEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
  let p := globalAnchorBlockPrepared s
  obtain ⟨a, ha, hea⟩ := physicalBlockPrepare_executes false .rowCount .universe s hs.temp_empty
  obtain ⟨hi, hu, hcnt, hf⟩ := globalAnchorPrepared_ready R L s hs
  obtain ⟨b, hb, heb, hi', hu', htype, hcount, hrem, hrecord, hflag⟩ :=
    operationalBlock_executes L (rawRowAlphabet R) R.rows.length (R.N) (R.rows.length + 1)
      (canonicalGlobalBase p) hi hu hf hcnt
  have hlift := extraPorts_executes (E := CanonicalGlobalPort) originalCanonicalBlockRoutine
    (canonicalGlobalBase p) (operationalBlockEval (R.N) (canonicalGlobalBase p))
    (canonicalGlobalExtra p) b heb
  rw [canonicalGlobal_split] at hlift
  have hall := RoutineComposition.seq_executes _ _ hea hlift
  have hprep : physicalBlockPrepareBound .rowCount .universe s ≤
      10 * rawRowAlphabet R + 8 * R.rows.length + 21 := by
    unfold physicalBlockPrepareBound cleanupMass blockPrepareOwned
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      hs.alphabet, hs.rows, hs.universe, List.length_replicate]
    have h1 := hs.row_bound
    have h2 := hs.threshold_bound
    have h3 := hs.block_bound
    have h4 := hs.counter_bound
    have h5 := originalUniverse_le_alphabet R
    omega
  have horig : (globalAnchorBlockBodyEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
    change (operationalBlockEval (R.N) (canonicalGlobalBase p)).stk (.inl (.inr .original)) = _
    rw [hrecord]; exact globalAnchorPrepared_old s _
  have hinv : GlobalCanonicalInv R L (globalAnchorBlockBodyEval R s) := by
    refine ⟨hi'.scan, hi'.query_empty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htype, hcount, hrem,
      hi'.temp_empty, hu'.2.2, hi'.row_bound, ?_, hi'.block_bound, hflag⟩
    · rw [horig]; exact hs.parsed
    · rw [globalAnchorBlockBody_globals]; exact hs.universe
    · rw [globalAnchorBlockBody_globals]; exact hs.rows
    · rw [globalAnchorBlockBody_globals]; exact hs.budget
    · rw [globalAnchorBlockBody_globals]; exact hs.alphabet
    · rw [globalAnchorBlockBody_globals]; exact hs.marker
    · rw [globalAnchorBlockBody_globals]; exact hs.counter_unary
    · rw [globalAnchorBlockBody_globals]; exact hs.counter_bound
    · change ((operationalBlockEval (R.N) (canonicalGlobalBase p)).stk (.inr .threshold)).length ≤ _
      rw [hi'.threshold_word, List.length_replicate]; exact originalUniverse_le_alphabet R
  exact ⟨a + b, by unfold globalAnchorBlockBodyBound; omega, hall, hinv, horig⟩


/- The anchor is invoked AFTER all real blocks so its actual prepended
bytes appear FIRST in the original block list. The same operational
contract remains fresh and preserves all global metadata/counter tapes.
Exact original anchor observation and C0 assembly join next. All sources
remain unelaborated, with complete-constructor/verifier/kernel limits.
-/

end PolytomyReductionModel
