/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

All-path selected-query storage bounds and actual unconditional cleanup.
Both supplied physical query cap and disposable row selector are consumed;
the original record survives. Failure is not assumed to empty counters.
-/
import PolytomySelectedRecordReplay

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem selectedScan_work_bounds (C L I : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s)
    (hI : (s.stk (.inr .queries)).length ≤ I) :
    cleanupMass scanOwned (selectedScanPrefixEval C s) ≤ C + 6 * L ∧
      ((selectedScanPrefixEval C s).stk (.inr .queries)).length ≤ I := by
  obtain ⟨n, hn, he, ho, hsource, hN, hM, hK⟩ := scanHeader_executes C L s hs
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  obtain ⟨m, hm, hr, hfinal⟩ := selectedScanPrefix_executes C L s hs
  have hsel : ((scanHeaderEval s).stk (.inr .queries)).length ≤ I := by
    rw [scanHeader_extra s .queries (by decide) (by decide) (by decide)]
    exact hI
  have hcounts := selectedRows_counter_bounds scanVisitPorts .inner .outer .queries
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    C L I (scanHeaderEval s) hi hc hd hsel
  have hextra : ∀ k : UnaryScanPort, k ≠ .inner → k ≠ .outer → k ≠ .queries →
      (selectedScanPrefixEval C s).stk (.inr k) = (scanHeaderEval s).stk (.inr k) := by
    intro k hkc hkd hks
    exact selectedRows_extra scanVisitPorts .inner .outer .queries k
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hkc hkd hks C L (scanHeaderEval s) hi hc
  have htemp : (selectedScanPrefixEval C s).stk (.inr .copyTemp) = [] := by
    rw [hextra .copyTemp (by decide) (by decide) (by decide),
      scanHeader_extra s .copyTemp (by decide) (by decide) (by decide)]
    exact hs.empty .copyTemp (by simp [scanWorkExtras])
  have hsaved : (selectedScanPrefixEval C s).stk (.inr .savedCount) = [] := by
    rw [hextra .savedCount (by decide) (by decide) (by decide)]
    exact hz
  have hn' : ((selectedScanPrefixEval C s).stk (.inr .headerN)).length ≤ L := by
    rw [hextra .headerN (by decide) (by decide) (by decide)]; exact hN
  have hm' : ((selectedScanPrefixEval C s).stk (.inr .headerM)).length ≤ L := by
    rw [hextra .headerM (by decide) (by decide) (by decide)]; exact hM
  have hk' : ((selectedScanPrefixEval C s).stk (.inr .headerK)).length ≤ L := by
    rw [hextra .headerK (by decide) (by decide) (by decide)]; exact hK
  change ((selectedScanPrefixEval C s).stk (.inr .inner)).length ≤ L ∧
    ((selectedScanPrefixEval C s).stk (.inr .outer)).length ≤ L ∧
    ((selectedScanPrefixEval C s).stk (.inr .queries)).length ≤ I at hcounts
  refine ⟨?_, hcounts.2.2⟩
  rcases hfinal.1 with ⟨hnum, hobs, hswap, hres, hright⟩
  rcases hnum with ⟨hpay, hwork, hout, hcap, hsrc⟩
  simp only [cleanupMass, scanOwned, scanWorkExtras, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, htemp, hsaved, hcap, List.length_replicate,
    show scanVisitPorts.m = UnaryScanPort.observed from rfl,
    show scanVisitPorts.t = UnaryScanPort.swapTemp from rfl,
    show scanVisitPorts.l = UnaryScanPort.residual from rfl,
    show scanVisitPorts.r = UnaryScanPort.right from rfl, hobs, hswap, hres, hright, List.length_nil]
  omega

def selectedScanOwned : List (NumericStack UnaryScanPort) := scanOwned ++ [.inr .queries]

def selectedScanCleanRoutine :
    Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq selectedScanCompleteRoutine (clearManyRoutine selectedScanOwned)

def selectedScanCleanEval (C : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) :=
  clearManyEval selectedScanOwned (selectedScanCompleteEval C s)

def selectedScanCleanBound (C L I : ℕ) := selectedScanPrefixBound C L + C + 6 * L + I + 16

theorem selectedScanClean_executes (C L I : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s)
    (hI : (s.stk (.inr .queries)).length ≤ I) :
    ∃ n ≤ selectedScanCleanBound C L I,
      selectedScanCleanRoutine.Executes s (selectedScanCleanEval C s) n := by
  obtain ⟨n, hn, he⟩ := selectedScanComplete_executes C L s hs
  obtain ⟨m, hm, hclear⟩ := clearMany_executes selectedScanOwned (selectedScanCompleteEval C s)
  have hb := selectedScan_work_bounds C L I s hs hI
  have hmass : cleanupMass selectedScanOwned (selectedScanCompleteEval C s) ≤ C + 6 * L + I := by
    have heq : cleanupMass selectedScanOwned (selectedScanCompleteEval C s) =
        cleanupMass scanOwned (selectedScanPrefixEval C s) +
        ((selectedScanPrefixEval C s).stk (.inr .queries)).length := by
      simp [selectedScanOwned, cleanupMass, selectedScanCompleteEval, suffixChecked, suffixCheckOp, Op.apply]
    rw [heq]; omega
  have hlen : selectedScanOwned.length = 14 := by simp [selectedScanOwned, scanOwned, scanWorkExtras]
  rw [hlen] at hm
  exact ⟨n + m, by unfold selectedScanCleanBound; omega,
    RoutineComposition.seq_executes _ _ he hclear⟩

theorem selectedScanClean_observation (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    unaryScanCompleteObservation (selectedScanCleanEval C s) =
      (readNormalizedSource (s.stk (.inr .original))).map
        (fun R => (R.rows.foldl (selectedRowStep C) (selectedRowData .queries s)).2) := by
  have hstate := clearMany_state selectedScanOwned (selectedScanCompleteEval C s)
  simpa only [selectedScanCleanEval, unaryScanCompleteObservation, hstate] using
    selectedScanComplete_observation C L s hs

theorem selectedScanClean_original (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    (selectedScanCleanEval C s).stk (.inr .original) = s.stk (.inr .original) := by
  rw [selectedScanCleanEval, clearMany_outside selectedScanOwned (.inr .original)
    (by simp [selectedScanOwned, scanOwned, scanWorkExtras])]
  exact selectedScanPrefix_record_preserved C L s hs

theorem selectedScanClean_ready (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady C L s) :
    UnaryScanReady 0 L (selectedScanCleanEval C s) ∧ (selectedScanCleanEval C s).stk (.inr .queries) = [] := by
  obtain ⟨n, hn, he, hi⟩ := selectedScanPrefix_executes C L s hs
  have hmem : ∀ k ∈ selectedScanOwned, (selectedScanCleanEval C s).stk k = [] :=
    fun k hk => clearMany_member selectedScanOwned k hk (selectedScanCompleteEval C s)
  have hsrc := hmem (.inl .source) (by simp [selectedScanOwned, scanOwned])
  have hcap := hmem (.inl .cap) (by simp [selectedScanOwned, scanOwned])
  refine ⟨⟨?_, hsrc, ?_, ?_⟩, hmem (.inr .queries) (by simp [selectedScanOwned])⟩
  · refine ⟨?_, ?_, ?_, by simpa using hcap, by rw [hsrc]; simp⟩
    · rw [selectedScanCleanEval, clearMany_outside selectedScanOwned (.inl .payload)
        (by simp [selectedScanOwned, scanOwned, scanWorkExtras])]
      exact hi.1.1.1
    · rw [selectedScanCleanEval, clearMany_outside selectedScanOwned (.inl .work)
        (by simp [selectedScanOwned, scanOwned, scanWorkExtras])]
      exact hi.1.1.2.1
    · rw [selectedScanCleanEval, clearMany_outside selectedScanOwned (.inl .output)
        (by simp [selectedScanOwned, scanOwned, scanWorkExtras])]
      exact hi.1.1.2.2.1
  · intro k hk
    exact hmem (.inr k) (by simp [selectedScanOwned, scanOwned, hk])
  · rw [selectedScanClean_original C L s hs]
    exact hs.original_bound

/- Unlike the original coverage query, the row selector is disposable
and is actually cleared as well. The preserved original word is the only
nonempty public extra tape at return. No declaration that the selector
or cap survived is used to justify a later call without a fresh copy.
-/

end PolytomyReductionModel
