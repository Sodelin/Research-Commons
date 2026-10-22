/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual outer-loop body: physically prepare from the current global
counter, then call the complete concrete block routine. Its operational
contract does NOT assume the selector is already less than m.
-/
import PolytomyPhysicalBlockPreparation

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

structure GlobalCanonicalInv (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore) : Prop where
  scan : UnaryScanReady 0 L (canonicalGlobalNumeric s)
  query_empty : s.stk (globalScanPort (.inr .queries)) = []
  parsed : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R
  universe : s.stk (.inr .universe) = List.replicate R.N true
  rows : s.stk (.inr .rowCount) = List.replicate R.rows.length true
  budget : s.stk (.inr .budget) = List.replicate R.K true
  alphabet : s.stk (.inr .alphabet) = List.replicate (rawRowAlphabet R) true
  marker : s.stk (.inr .markerThreshold) = List.replicate (originalMarkerThreshold R) true
  counter_unary : IsUnaryWord (s.stk (.inr .blockCounter))
  counter_bound : (s.stk (.inr .blockCounter)).length ≤ R.rows.length
  type_empty : s.stk (globalFilterPort .typeIndex) = []
  count_empty : s.stk (globalFilterPort .count) = []
  remaining_empty : s.stk (globalFilterPort .remaining) = []
  temp_empty : s.stk (globalFilterPort .temp) = []
  cost_unary : IsUnaryWord (s.stk (globalFilterPort .cost))
  row_bound : (s.stk (globalFilterPort .rowIndex)).length ≤ R.rows.length
  threshold_bound : (s.stk (globalFilterPort .threshold)).length ≤ rawRowAlphabet R
  block_bound : (s.stk (globalFilterPort .blockCode)).length ≤ R.rows.length + 1
  success : s.state.2 = true

theorem originalMarker_le_alphabet (R : RawMSSCRecord) : originalMarkerThreshold R ≤ rawRowAlphabet R := by
  simp [originalMarkerThreshold, privateCount, rawRowAlphabet]
  omega

def globalRealBlockPrepared (s : CanonicalGlobalStore) :=
  physicalBlockPrepareEval true .blockCounter .markerThreshold s

def globalRealBlockBodyRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (physicalBlockPrepareRoutine true .blockCounter .markerThreshold)
    (extraPortsRoutine (E := CanonicalGlobalPort) originalCanonicalBlockRoutine)

def globalRealBlockBodyEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  extraPortsStore (operationalBlockEval (originalMarkerThreshold R) (canonicalGlobalBase (globalRealBlockPrepared s)))
    (canonicalGlobalExtra (globalRealBlockPrepared s))

def globalRealBlockBodyBound (R : RawMSSCRecord) (L : ℕ) :=
  10 * rawRowAlphabet R + 8 * R.rows.length + 21 +
    operationalBlockBound L (rawRowAlphabet R) R.rows.length (originalMarkerThreshold R) (R.rows.length + 1)

theorem globalRealBlockBody_globals (R : RawMSSCRecord) (s : CanonicalGlobalStore) (k : CanonicalGlobalPort) :
    (globalRealBlockBodyEval R s).stk (.inr k) = s.stk (.inr k) :=
  physicalBlockPrepare_extra true .blockCounter .markerThreshold s (.inr k)
    (by simp [globalFilterPort]) (by simp [globalFilterPort]) (by simp [globalFilterPort])
    (by simp [globalFilterPort]) (by simp [globalFilterPort])

theorem globalRealPrepared_old (s : CanonicalGlobalStore) (k : NumericStack UnaryScanPort) :
    (globalRealBlockPrepared s).stk (globalScanPort k) = s.stk (globalScanPort k) :=
  physicalBlockPrepare_extra true .blockCounter .markerThreshold s (globalScanPort k)
    (by simp [globalFilterPort, globalScanPort]) (by simp [globalFilterPort, globalScanPort])
    (by simp [globalFilterPort, globalScanPort]) (by simp [globalFilterPort, globalScanPort])
    (by simp [globalFilterPort, globalScanPort])

theorem globalRealPrepared_ready (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) :
    RealTypeLoopInv L (rawRowAlphabet R) R.rows.length (originalMarkerThreshold R) (R.rows.length + 1)
      (canonicalGlobalBase (globalRealBlockPrepared s)) ∧
      RealTypeUnaryData (canonicalGlobalBase (globalRealBlockPrepared s)) ∧
      (canonicalGlobalBase (globalRealBlockPrepared s)).stk (.inr .count) = [] ∧
      (globalRealBlockPrepared s).state.2 = true := by
  let i := (s.stk (.inr .blockCounter)).length
  obtain ⟨hA, hrem, hrow, hT, hblock⟩ := physicalBlockPrepare_values true .blockCounter .markerThreshold
    (rawRowAlphabet R) i (originalMarkerThreshold R) s hs.alphabet hs.counter_unary hs.marker hs.type_empty hs.remaining_empty
  have hcnt : (globalRealBlockPrepared s).stk (globalFilterPort .count) = [] := by
    rw [physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hs.count_empty
  have htmp : (globalRealBlockPrepared s).stk (globalFilterPort .temp) = [] := by
    rw [physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hs.temp_empty
  have hcost : IsUnaryWord ((globalRealBlockPrepared s).stk (globalFilterPort .cost)) := by
    rw [physicalBlockPrepare_extra _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hs.cost_unary
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hT, htmp, ?_, ?_⟩, ⟨?_, ?_, hcost⟩, hcnt, ?_⟩
  · exact UnaryScanReady_of_stacks 0 L _ _ hs.scan (globalRealPrepared_old s)
  · rw [show (globalRealBlockPrepared s).stk (globalScanPort (.inr .queries)) =
      s.stk (globalScanPort (.inr .queries)) from globalRealPrepared_old s _]; exact hs.query_empty
  · simp [hA, IsUnaryWord]
  · simp [hA]
  · rw [hrow, List.length_replicate]; exact hs.counter_bound
  · simp [hrem]
  · rw [hblock, List.length_replicate]; simp only [↓reduceIte]
    have hi := hs.counter_bound; omega
  · simp [hrem, IsUnaryWord]
  · simp [hcnt, IsUnaryWord]
  · rw [physicalBlockPrepare_state]; exact hs.success

theorem globalRealBlockBody_executes (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : GlobalCanonicalInv R L s) :
    ∃ n ≤ globalRealBlockBodyBound R L,
      globalRealBlockBodyRoutine.Executes s (globalRealBlockBodyEval R s) n ∧
      GlobalCanonicalInv R L (globalRealBlockBodyEval R s) ∧
      (globalRealBlockBodyEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
  let p := globalRealBlockPrepared s
  obtain ⟨a, ha, hea⟩ := physicalBlockPrepare_executes true .blockCounter .markerThreshold s hs.temp_empty
  obtain ⟨hi, hu, hcnt, hf⟩ := globalRealPrepared_ready R L s hs
  obtain ⟨b, hb, heb, hi', hu', htype, hcount, hrem, hrecord, hflag⟩ :=
    operationalBlock_executes L (rawRowAlphabet R) R.rows.length (originalMarkerThreshold R) (R.rows.length + 1)
      (canonicalGlobalBase p) hi hu hf hcnt
  have hlift := extraPorts_executes (E := CanonicalGlobalPort) originalCanonicalBlockRoutine
    (canonicalGlobalBase p) (operationalBlockEval (originalMarkerThreshold R) (canonicalGlobalBase p))
    (canonicalGlobalExtra p) b heb
  rw [canonicalGlobal_split] at hlift
  have hall := RoutineComposition.seq_executes _ _ hea hlift
  have hprep : physicalBlockPrepareBound .blockCounter .markerThreshold s ≤
      10 * rawRowAlphabet R + 8 * R.rows.length + 21 := by
    unfold physicalBlockPrepareBound cleanupMass blockPrepareOwned
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      hs.alphabet, hs.marker, List.length_replicate]
    have h1 := hs.row_bound
    have h2 := hs.threshold_bound
    have h3 := hs.block_bound
    have h4 := hs.counter_bound
    have h5 := originalMarker_le_alphabet R
    omega
  have horig : (globalRealBlockBodyEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) := by
    change (operationalBlockEval (originalMarkerThreshold R) (canonicalGlobalBase p)).stk (.inl (.inr .original)) = _
    rw [hrecord]; exact globalRealPrepared_old s _
  have hinv : GlobalCanonicalInv R L (globalRealBlockBodyEval R s) := by
    refine ⟨hi'.scan, hi'.query_empty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htype, hcount, hrem,
      hi'.temp_empty, hu'.2.2, hi'.row_bound, ?_, hi'.block_bound, hflag⟩
    · rw [horig]; exact hs.parsed
    · rw [globalRealBlockBody_globals]; exact hs.universe
    · rw [globalRealBlockBody_globals]; exact hs.rows
    · rw [globalRealBlockBody_globals]; exact hs.budget
    · rw [globalRealBlockBody_globals]; exact hs.alphabet
    · rw [globalRealBlockBody_globals]; exact hs.marker
    · rw [globalRealBlockBody_globals]; exact hs.counter_unary
    · rw [globalRealBlockBody_globals]; exact hs.counter_bound
    · change ((operationalBlockEval (originalMarkerThreshold R) (canonicalGlobalBase p)).stk (.inr .threshold)).length ≤ _
      rw [hi'.threshold_word, List.length_replicate]; exact originalMarker_le_alphabet R
  exact ⟨a + b, by unfold globalRealBlockBodyBound; omega, hall, hinv, horig⟩

/- This contract holds even when the current global counter is m. The
body then runs an out-of-range query, yet remains operationally bounded
and fresh. The ORIGINAL real-block byte/cost interpretation is applied
only after the actual outer pop gives i<m. All global scalar/counter
words survive the body and are not replaced by proof-supplied data.
-/

end PolytomyReductionModel
