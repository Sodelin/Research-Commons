/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual failure-independent scan cleanup. The query cap is deliberately
cleared along with every replay/header/row scratch port; only the original
record and external query counter survive. Failed partial storage is
bounded before cleanup, rather than inferred from successful exhaustion.
-/
import PolytomyUnaryScanCompleteInput

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {F : Type}

def scanOwned : List (NumericStack UnaryScanPort) :=
  [.inl .source, .inl .cap] ++ scanWorkExtras.map Sum.inr

theorem scanPrefix_work_bound (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    cleanupMass scanOwned (unaryScanPrefixEval mode bump C s) ≤ C + 7 * L := by
  obtain ⟨n, hn, he, ho, hsource, hN, hM, hK⟩ := scanHeader_executes C L s hs
  obtain ⟨hi, hc, hd, hz⟩ := scanHeader_rows_ready C L s hs
  obtain ⟨m, hm, hr, hfinal⟩ := unaryScanPrefix_executes mode bump C L s hs
  have hcounts := unaryRows_counter_bounds scanRowsPorts mode bump C L (scanHeaderEval s) hi hc hd hz
  have hNpres := unaryRows_extra scanRowsPorts .headerN (by decide) (by decide) (by decide)
    mode bump C L (scanHeaderEval s) hi hc
  have hMpres := unaryRows_extra scanRowsPorts .headerM (by decide) (by decide) (by decide)
    mode bump C L (scanHeaderEval s) hi hc
  have hKpres := unaryRows_extra scanRowsPorts .headerK (by decide) (by decide) (by decide)
    mode bump C L (scanHeaderEval s) hi hc
  have htemp : (unaryScanPrefixEval mode bump C s).stk (.inr .copyTemp) = [] := by
    rw [unaryScanPrefixEval, unaryRows_extra scanRowsPorts .copyTemp (by decide) (by decide) (by decide)
      mode bump C L (scanHeaderEval s) hi hc, scanHeader_extra s .copyTemp (by decide) (by decide) (by decide)]
    exact hs.empty .copyTemp (by simp [scanWorkExtras])
  rcases hfinal.1 with ⟨hnum, hobs, hswap, hres, hright⟩
  rcases hnum with ⟨hpay, hwork, hout, hcap, hsrc⟩
  change ((unaryRowsEval scanRowsPorts mode bump C (scanHeaderEval s)).stk (.inr .inner)).length ≤ L ∧
    ((unaryRowsEval scanRowsPorts mode bump C (scanHeaderEval s)).stk (.inr .outer)).length ≤ L ∧
    ((unaryRowsEval scanRowsPorts mode bump C (scanHeaderEval s)).stk (.inr .savedCount)).length ≤ L at hcounts
  have hn' : ((unaryScanPrefixEval mode bump C s).stk (.inr .headerN)).length ≤ L := by
    change ((unaryRowsEval scanRowsPorts mode bump C (scanHeaderEval s)).stk (.inr .headerN)).length ≤ L
    rw [hNpres]; exact hN
  have hm' : ((unaryScanPrefixEval mode bump C s).stk (.inr .headerM)).length ≤ L := by
    change ((unaryRowsEval scanRowsPorts mode bump C (scanHeaderEval s)).stk (.inr .headerM)).length ≤ L
    rw [hMpres]; exact hM
  have hk' : ((unaryScanPrefixEval mode bump C s).stk (.inr .headerK)).length ≤ L := by
    change ((unaryRowsEval scanRowsPorts mode bump C (scanHeaderEval s)).stk (.inr .headerK)).length ≤ L
    rw [hKpres]; exact hK
  simp only [cleanupMass, scanOwned, scanWorkExtras, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, htemp, hcap, List.length_replicate,
    show scanVisitPorts.m = UnaryScanPort.observed from rfl,
    show scanVisitPorts.t = UnaryScanPort.swapTemp from rfl,
    show scanVisitPorts.l = UnaryScanPort.residual from rfl,
    show scanVisitPorts.r = UnaryScanPort.right from rfl, hobs, hswap, hres, hright, List.length_nil]
  change _ ≤ C + 7 * L
  change ((unaryScanPrefixEval mode bump C s).stk (.inr .inner)).length ≤ L ∧
    ((unaryScanPrefixEval mode bump C s).stk (.inr .outer)).length ≤ L ∧
    ((unaryScanPrefixEval mode bump C s).stk (.inr .savedCount)).length ≤ L at hcounts
  omega

def unaryScanCleanRoutine (mode : UnaryVisitMode) (bump : F → Bool → F) :
    Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState F) :=
  RoutineComposition.seq (unaryScanCompleteRoutine mode bump) (clearManyRoutine scanOwned)

def unaryScanCleanEval (mode : UnaryVisitMode) (bump : F → Bool → F) (C : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) :=
  clearManyEval scanOwned (unaryScanCompleteEval mode bump C s)

def unaryScanCleanBound (C L : ℕ) := unaryScanPrefixBound C L + C + 7 * L + 15

theorem unaryScanClean_executes (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    ∃ n ≤ unaryScanCleanBound C L,
      (unaryScanCleanRoutine mode bump).Executes s (unaryScanCleanEval mode bump C s) n := by
  obtain ⟨n, hn, he⟩ := unaryScanComplete_executes mode bump C L s hs
  obtain ⟨m, hm, hclear⟩ := clearMany_executes scanOwned (unaryScanCompleteEval mode bump C s)
  have hmass : cleanupMass scanOwned (unaryScanCompleteEval mode bump C s) ≤ C + 7 * L :=
    scanPrefix_work_bound mode bump C L s hs
  have hlen : scanOwned.length = 13 := by simp [scanOwned, scanWorkExtras]
  rw [hlen] at hm
  exact ⟨n + m, by unfold unaryScanCleanBound; omega,
    RoutineComposition.seq_executes (unaryScanCompleteRoutine mode bump) (clearManyRoutine scanOwned) he hclear⟩

theorem unaryScanClean_observation (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    unaryScanCompleteObservation (unaryScanCleanEval mode bump C s) =
      (readNormalizedSource (s.stk (.inr .original))).map
        (fun R => R.rows.foldl (fun a row => row.foldl (unaryVisitStep mode bump C) a) s.state.1.1) := by
  have hstate := clearMany_state scanOwned (unaryScanCompleteEval mode bump C s)
  simpa only [unaryScanCleanEval, unaryScanCompleteObservation, hstate] using
    unaryScanComplete_observation mode bump C L s hs

theorem unaryScanClean_preserves (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    (unaryScanCleanEval mode bump C s).stk (.inr .original) = s.stk (.inr .original) ∧
      (unaryScanCleanEval mode bump C s).stk (.inr .queries) = s.stk (.inr .queries) := by
  constructor
  · rw [unaryScanCleanEval, clearMany_outside scanOwned (.inr .original) (by simp [scanOwned, scanWorkExtras])]
    exact unaryScanPrefix_record_preserved mode bump C L s hs
  · rw [unaryScanCleanEval, clearMany_outside scanOwned (.inr .queries) (by simp [scanOwned, scanWorkExtras])]
    exact unaryScanPrefix_queries_preserved mode bump C L s hs

theorem unaryScanClean_ready (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    UnaryScanReady 0 L (unaryScanCleanEval mode bump C s) := by
  obtain ⟨n, hn, he, hi⟩ := unaryScanPrefix_executes mode bump C L s hs
  have hmem : ∀ k ∈ scanOwned, (unaryScanCleanEval mode bump C s).stk k = [] :=
    fun k hk => clearMany_member scanOwned k hk (unaryScanCompleteEval mode bump C s)
  have hsrc := hmem (.inl .source) (by simp [scanOwned])
  have hcap := hmem (.inl .cap) (by simp [scanOwned])
  refine ⟨?_, hsrc, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, by simpa using hcap, by rw [hsrc]; simp⟩
    · rw [unaryScanCleanEval, clearMany_outside scanOwned (.inl .payload) (by simp [scanOwned, scanWorkExtras])]
      exact hi.1.1.1
    · rw [unaryScanCleanEval, clearMany_outside scanOwned (.inl .work) (by simp [scanOwned, scanWorkExtras])]
      exact hi.1.1.2.1
    · rw [unaryScanCleanEval, clearMany_outside scanOwned (.inl .output) (by simp [scanOwned, scanWorkExtras])]
      exact hi.1.1.2.2.1
  · intro k hk
    exact hmem (.inr k) (by simp [scanOwned, hk])
  · rw [(unaryScanClean_preserves mode bump C L s hs).1]
    exact hs.original_bound

/- Cleanup consumes the query cap. It preserves the exact finite syntax
and accumulator observation, and returns all scan work fresh for a later
actual replay. Only original/queries remain on extra data ports. This is
not yet the whole original range/coverage decision or constructor output.
-/

end PolytomyReductionModel
