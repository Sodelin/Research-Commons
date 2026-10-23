/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Failure-independent cleanup of the actual first count/range/syntax pass,
preserving its physical N query count and exact verdict for coverage.
-/
import PolytomyOriginalCountRangeCheck

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem guardedDeclaredCount_length_le {K : Type} [DecidableEq K]
    («left» «right» : K) (hne : «left» ≠ «right») (s : CountdownStore K Bool) (k : K) :
    ((guardedDeclaredCountEval «left» «right» s).stk k).length ≤ (s.stk k).length := by
  by_cases hkl : k = «left»
  · subst k; exact (guardedDeclaredCount_lengths «left» «right» hne s).1
  · by_cases hkr : k = «right»
    · subst k; exact (guardedDeclaredCount_lengths «left» «right» hne s).2
    · simpa only [guardedDeclaredCount_extra «left» «right» k hkl hkr s] using le_refl (s.stk k).length

theorem cleanupMass_mono {K F : Type} (ks : List K) (s t : CountdownStore K F)
    (h : ∀ k, (t.stk k).length ≤ (s.stk k).length) : cleanupMass ks t ≤ cleanupMass ks s := by
  induction ks with
  | nil => simp [cleanupMass]
  | cons k ks ih =>
      simp only [cleanupMass, List.map_cons, List.sum_cons] at *
      exact Nat.add_le_add (h k) ih

theorem originalRange_mass (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) (hq : s.stk (.inr .queries) = []) :
    cleanupMass scanOwned (originalRangeEval s) ≤ 8 * L := by
  obtain ⟨n, hn, he, ho, hsrc0, hN0, hM0, hK0⟩ := scanHeader_executes 0 L
    (rangeStartOp.apply s) (rangeStart_ready L s hs)
  obtain ⟨hN, hi, hc, hd, hz, hquery⟩ := validationPrepared_ready L s hs hq
  obtain ⟨m, hm, hrows, hfinal, hg, hclear⟩ := unaryRows_executes scanRowsPorts .less
    (fun a b => a && b) (validationN s) L (validationPrepared s) hi hc hd hz
  have hcounts := unaryRows_counter_bounds scanRowsPorts .less (fun a b => a && b)
    (validationN s) L (validationPrepared s) hi hc hd hz
  have hpres (k : UnaryScanPort) (hkc : k ≠ .inner) (hkd : k ≠ .outer)
      (hkz : k ≠ .savedCount) (hkq : k ≠ .queries) :
      (originalRangeEval s).stk (.inr k) = (validationHeader s).stk (.inr k) := by
    change (originalRangeRows s).stk (.inr k) = _
    rw [originalRangeRows, unaryRows_extra scanRowsPorts k hkc hkd hkz .less
      (fun a b => a && b) (validationN s) L (validationPrepared s) hi hc,
      validationPrepared_extra s k hkq]
  have hn' : ((originalRangeEval s).stk (.inr .headerN)).length ≤ L := by
    rw [hpres .headerN (by decide) (by decide) (by decide) (by decide)]; exact hN0
  have hm' : ((originalRangeEval s).stk (.inr .headerM)).length ≤ L := by
    rw [hpres .headerM (by decide) (by decide) (by decide) (by decide)]; exact hM0
  have hk' : ((originalRangeEval s).stk (.inr .headerK)).length ≤ L := by
    rw [hpres .headerK (by decide) (by decide) (by decide) (by decide)]; exact hK0
  have htemp : (originalRangeEval s).stk (.inr .copyTemp) = [] := by
    rw [hpres .copyTemp (by decide) (by decide) (by decide) (by decide), validationHeader,
      scanHeader_extra _ .copyTemp (by decide) (by decide) (by decide)]
    exact hs.empty .copyTemp (by simp [scanWorkExtras])
  rcases hfinal.1 with ⟨hnum, hobs, hswap, hres, hright⟩
  rcases hnum with ⟨hpay, hwork, hout, hcap, hsrc⟩
  change (originalRangeEval s).stk (.inr .observed) = [] at hobs
  change (originalRangeEval s).stk (.inr .swapTemp) = [] at hswap
  change (originalRangeEval s).stk (.inr .residual) = [] at hres
  change (originalRangeEval s).stk (.inr .right) = [] at hright
  change (originalRangeEval s).stk (.inl .cap) = List.replicate (validationN s) true at hcap
  change ((originalRangeEval s).stk (.inl .source)).length ≤ L at hsrc
  change ((originalRangeEval s).stk (.inr .inner)).length ≤ L ∧
    ((originalRangeEval s).stk (.inr .outer)).length ≤ L ∧
    ((originalRangeEval s).stk (.inr .savedCount)).length ≤ L at hcounts
  simp only [cleanupMass, scanOwned, scanWorkExtras, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, htemp, hobs, hswap, hres, hright,
    hcap, List.length_replicate, List.length_nil]
  omega

def firstValidationRoutine : Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState Bool) :=
  RoutineComposition.seq originalCountRangeRoutine (clearManyRoutine scanOwned)

def firstValidationEval (s : CountdownStore (NumericStack UnaryScanPort) Bool) :=
  clearManyEval scanOwned (originalCountRangeEval s)

def firstValidationBound (L : ℕ) := 17 * L ^ 3 + 27 * L ^ 2 + 40 * L + 51

theorem firstValidation_ready (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) (hq : s.stk (.inr .queries) = []) :
    CoverageInv L (firstValidationEval s) ∧
      (firstValidationEval s).stk (.inr .original) = s.stk (.inr .original) ∧
      (firstValidationEval s).stk (.inr .queries) = List.replicate (validationN s) true := by
  obtain ⟨hN, hi, hc, hd, hz, hqueries⟩ := validationPrepared_ready L s hs hq
  obtain ⟨m, hm, he, hrows, hg, hclear⟩ := unaryRows_executes scanRowsPorts .less
    (fun a b => a && b) (validationN s) L (validationPrepared s) hi hc hd hz
  have hpres := originalCountRange_preserves L s hs hq
  have horig : (firstValidationEval s).stk (.inr .original) = s.stk (.inr .original) := by
    rw [firstValidationEval, clearMany_outside scanOwned (.inr .original) (by simp [scanOwned, scanWorkExtras])]
    exact hpres.1
  have hquery : (firstValidationEval s).stk (.inr .queries) = List.replicate (validationN s) true := by
    rw [firstValidationEval, clearMany_outside scanOwned (.inr .queries) (by simp [scanOwned, scanWorkExtras])]
    exact hpres.2
  have hmem : ∀ k ∈ scanOwned, (firstValidationEval s).stk k = [] :=
    fun k hk => clearMany_member scanOwned k hk (originalCountRangeEval s)
  have hsrc := hmem (.inl .source) (by simp [scanOwned])
  have hcap := hmem (.inl .cap) (by simp [scanOwned])
  have hnumeric (port : NumericPort) (hp : port ∈ [NumericPort.payload, .work, .output]) :
      (firstValidationEval s).stk (.inl port) = (originalRangeRows s).stk (.inl port) := by
    have hnot : (Sum.inl port : NumericStack UnaryScanPort) ∉ scanOwned := by
      cases port <;> simp_all [scanOwned, scanWorkExtras]
    rw [firstValidationEval, clearMany_outside scanOwned (.inl port) hnot, originalCountRangeEval,
      guardedDeclaredCount_extra _ _ _ (by simp) (by simp)]
    rfl
  refine ⟨⟨⟨?_, hsrc, ?_, ?_⟩, ?_, ?_⟩, horig, hquery⟩
  · refine ⟨?_, ?_, ?_, by simpa using hcap, by rw [hsrc]; simp⟩
    · rw [hnumeric .payload (by simp)]; exact hrows.1.1.1
    · rw [hnumeric .work (by simp)]; exact hrows.1.1.2.1
    · rw [hnumeric .output (by simp)]; exact hrows.1.1.2.2.1
  · intro k hk; exact hmem (.inr k) (by simp [scanOwned, hk])
  · rw [horig]; exact hs.original_bound
  · simp [IsUnaryWord, hquery]
  · simpa [hquery] using hN

theorem firstValidation_executes (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) (hq : s.stk (.inr .queries) = []) :
    ∃ n ≤ firstValidationBound L, firstValidationRoutine.Executes s (firstValidationEval s) n := by
  obtain ⟨n, hn, hfirst⟩ := originalCountRange_executes L s hs hq
  obtain ⟨m, hm, hclear⟩ := clearMany_executes scanOwned (originalCountRangeEval s)
  have hmass := (cleanupMass_mono scanOwned (originalRangeEval s) (originalCountRangeEval s)
    (guardedDeclaredCount_length_le (.inr .headerM) (.inr .savedCount) (by decide) (originalRangeEval s))).trans
      (originalRange_mass L s hs hq)
  have hlen : scanOwned.length = 13 := by simp [scanOwned, scanWorkExtras]
  rw [hlen] at hm
  refine ⟨n + m, ?_, RoutineComposition.seq_executes originalCountRangeRoutine (clearManyRoutine scanOwned) hfirst hclear⟩
  unfold firstValidationBound originalRangeBound at *
  omega

theorem firstValidation_verdict (L : ℕ) (s : CountdownStore (NumericStack UnaryScanPort) Bool)
    (hs : UnaryScanReady 0 L s) (hq : s.stk (.inr .queries) = []) :
    (firstValidationEval s).state.2 = countRangeSpec (s.stk (.inr .original)) := by
  change (clearManyEval scanOwned (originalCountRangeEval s)).state.2 = _
  rw [clearMany_state]
  exact originalCountRange_verdict L s hs hq

end PolytomyReductionModel
