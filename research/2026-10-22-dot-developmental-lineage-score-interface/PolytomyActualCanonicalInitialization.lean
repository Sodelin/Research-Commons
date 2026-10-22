/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Complete actual physical global initialization from an ORIGINAL valid
preserved record: N,m,K extraction, multiplication, alphabet/threshold/
outer-counter construction, and all old arithmetic/source work cleanup.
-/
import PolytomyCanonicalScalarAssembly

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def canonicalInitializationOwned : List CanonicalGlobalStack :=
  [globalScanPort (.inl .source), globalScanPort (.inl .cap),
    globalScanPort (.inr .headerM), globalScanPort (.inr .savedCount)]

def canonicalGlobalsBeforeCleanup (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  canonicalScalarAssemblyEval (canonicalGlobalProductEval R.N R.declaredM (canonicalGlobalHeaderEval s))

def canonicalGlobalsEval (R : RawMSSCRecord) (s : CanonicalGlobalStore) :=
  clearManyEval canonicalInitializationOwned (canonicalGlobalsBeforeCleanup R s)

def canonicalGlobalsRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq canonicalGlobalHeaderRoutine
    (RoutineComposition.seq canonicalGlobalProductRoutine
      (RoutineComposition.seq canonicalScalarAssemblyRoutine (clearManyRoutine canonicalInitializationOwned)))

def canonicalGlobalsBound (L : ℕ) := 10 * L ^ 2 + 42 * L + 58

theorem canonicalGlobals_old_extra (R : RawMSSCRecord) (s : CanonicalGlobalStore)
    (k : NumericStack UnaryScanPort) (hsrc : k ≠ .inl .source) (hcap : k ≠ .inl .cap)
    (hM : k ≠ .inr .headerM) (hP : k ≠ .inr .savedCount) :
    (canonicalGlobalsEval R s).stk (globalScanPort k) = s.stk (globalScanPort k) := by
  rw [clearMany_outside _ _ (by simpa [canonicalInitializationOwned, globalScanPort] using
    And.intro hsrc (And.intro hcap (And.intro hM hP))) _]
  rw [canonicalScalarAssembly_extra _ _ (by simp [globalScanPort]) (by simp [globalScanPort]) (by simp [globalScanPort])]
  rw [canonicalGlobalProduct_extra _ _ _ _ (by simpa [globalScanPort] using hcap)
    (by simpa [globalScanPort] using hM) (by simpa [globalScanPort] using hP)]
  exact canonicalGlobalHeader_extra s _ (by simpa [globalScanPort] using hsrc)
    (by simp [globalScanPort]) (by simp [globalScanPort]) (by simp [globalScanPort])

theorem canonicalGlobals_filter_extra (R : RawMSSCRecord) (s : CanonicalGlobalStore) (k : CanonicalFilterPort) :
    (canonicalGlobalsEval R s).stk (globalFilterPort k) = s.stk (globalFilterPort k) := by
  rw [clearMany_outside _ _ (by simp [canonicalInitializationOwned, globalFilterPort, globalScanPort]) _]
  rw [canonicalScalarAssembly_extra _ _ (by simp [globalFilterPort]) (by simp [globalFilterPort]) (by simp [globalFilterPort])]
  rw [canonicalGlobalProduct_extra _ _ _ _ (by simp [globalFilterPort, globalScanPort])
    (by simp [globalFilterPort, globalScanPort]) (by simp [globalFilterPort, globalScanPort])]
  exact canonicalGlobalHeader_extra s _ (by simp [globalFilterPort, globalScanPort])
    (by simp [globalFilterPort]) (by simp [globalFilterPort]) (by simp [globalFilterPort])

theorem canonicalGlobals_ready (R : RawMSSCRecord) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s)) :
    UnaryScanReady 0 L (canonicalGlobalNumeric (canonicalGlobalsEval R s)) := by
  have hc : ∀ k ∈ canonicalInitializationOwned,
      (canonicalGlobalsEval R s).stk k = [] := by
    intro k hk; exact clearMany_member _ _ hk _
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [show (canonicalGlobalNumeric (canonicalGlobalsEval R s)).stk (.inl .payload) =
        (canonicalGlobalNumeric s).stk (.inl .payload) from
        canonicalGlobals_old_extra R s (.inl .payload) (by decide) (by decide) (by decide) (by decide)]
      exact hs.numeric.1
    · rw [show (canonicalGlobalNumeric (canonicalGlobalsEval R s)).stk (.inl .work) =
        (canonicalGlobalNumeric s).stk (.inl .work) from
        canonicalGlobals_old_extra R s (.inl .work) (by decide) (by decide) (by decide) (by decide)]
      exact hs.numeric.2.1
    · rw [show (canonicalGlobalNumeric (canonicalGlobalsEval R s)).stk (.inl .output) =
        (canonicalGlobalNumeric s).stk (.inl .output) from
        canonicalGlobals_old_extra R s (.inl .output) (by decide) (by decide) (by decide) (by decide)]
      exact hs.numeric.2.2.1
    · exact hc _ (by simp [canonicalInitializationOwned])
    · rw [show (canonicalGlobalNumeric (canonicalGlobalsEval R s)).stk (.inl .source) = [] from
        hc _ (by simp [canonicalInitializationOwned])]
      simp
  · exact hc _ (by simp [canonicalInitializationOwned])
  · intro k hk
    by_cases hM : k = .headerM
    · subst k; exact hc _ (by simp [canonicalInitializationOwned])
    by_cases hP : k = .savedCount
    · subst k; exact hc _ (by simp [canonicalInitializationOwned])
    rw [show (canonicalGlobalNumeric (canonicalGlobalsEval R s)).stk (.inr k) =
      (canonicalGlobalNumeric s).stk (.inr k) from
      canonicalGlobals_old_extra R s (.inr k) (by simp) (by simp)
        (by simpa using hM) (by simpa using hP)]
    exact hs.empty k hk
  · rw [show (canonicalGlobalNumeric (canonicalGlobalsEval R s)).stk (.inr .original) =
      (canonicalGlobalNumeric s).stk (.inr .original) from
      canonicalGlobals_old_extra R s (.inr .original) (by decide) (by decide) (by decide) (by decide)]
    exact hs.original_bound

theorem canonicalGlobals_executes (R : RawMSSCRecord) (hR : RawMSSCValid R) (L : ℕ)
    (s : CanonicalGlobalStore) (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = [])
    (hglobals : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = [])
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    ∃ n ≤ canonicalGlobalsBound L, canonicalGlobalsRoutine.Executes s (canonicalGlobalsEval R s) n ∧
      UnaryScanReady 0 L (canonicalGlobalNumeric (canonicalGlobalsEval R s)) ∧
      (canonicalGlobalsEval R s).stk (globalScanPort (.inr .queries)) = [] ∧
      (canonicalGlobalsEval R s).stk (globalScanPort (.inr .original)) = s.stk (globalScanPort (.inr .original)) ∧
      (canonicalGlobalsEval R s).stk (.inr .universe) = List.replicate R.N true ∧
      (canonicalGlobalsEval R s).stk (.inr .rowCount) = List.replicate R.rows.length true ∧
      (canonicalGlobalsEval R s).stk (.inr .budget) = List.replicate R.K true ∧
      (canonicalGlobalsEval R s).stk (.inr .alphabet) = List.replicate (rawRowAlphabet R) true ∧
      (canonicalGlobalsEval R s).stk (.inr .markerThreshold) = List.replicate (originalMarkerThreshold R) true ∧
      (canonicalGlobalsEval R s).stk (.inr .blockCounter) = List.replicate R.rows.length true ∧
      (∀ k, (canonicalGlobalsEval R s).stk (globalFilterPort k) = s.stk (globalFilterPort k)) ∧
      (canonicalGlobalsEval R s).state.2 = true := by
  let u := canonicalGlobalHeaderEval s
  let v := canonicalGlobalProductEval R.N R.declaredM u
  let w := canonicalScalarAssemblyEval v
  obtain ⟨a, ha, hea, hsrc, hNb, hMb, hKb⟩ := canonicalGlobalHeader_executes L s hs
    (hglobals .universe) (hglobals .rowCount) (hglobals .budget)
  obtain ⟨hf, hrows, hN, hM, hK⟩ := canonicalGlobalHeader_values L s hs
    (hglobals .universe) (hglobals .rowCount) (hglobals .budget) R hparse
  have huold : ∀ k : NumericStack UnaryScanPort, k ≠ .inl .source →
      u.stk (globalScanPort k) = s.stk (globalScanPort k) := by
    intro k hk
    exact canonicalGlobalHeader_extra s _ (by simpa [globalScanPort] using hk)
      (by simp [globalScanPort]) (by simp [globalScanPort]) (by simp [globalScanPort])
  have hun : NumericLoopInv 0 L (canonicalGlobalNumeric u) := by
    refine ⟨?_, ?_, ?_, ?_, hsrc⟩
    · rw [huold _ (by decide)]; exact hs.numeric.1
    · rw [huold _ (by decide)]; exact hs.numeric.2.1
    · rw [huold _ (by decide)]; exact hs.numeric.2.2.1
    · rw [huold _ (by decide)]; exact hs.numeric.2.2.2.1
  have hempty : ∀ k ∈ scanWorkExtras, u.stk (globalScanPort (.inr k)) = [] := by
    intro k hk; rw [huold _ (by simp)]; exact hs.empty k hk
  obtain ⟨b, hb, heb⟩ := canonicalGlobalProduct_executes R.N R.declaredM L u hun hf hN hM
    (hempty .copyTemp (by simp [scanWorkExtras])) (hempty .headerM (by simp [scanWorkExtras]))
    (hempty .swapTemp (by simp [scanWorkExtras])) (hempty .savedCount (by simp [scanWorkExtras]))
    (hempty .outer (by simp [scanWorkExtras]))
  have hvN : v.stk (.inr .universe) = List.replicate R.N true := by simpa [v, canonicalGlobalProductEval, globalScanPort] using hN
  have hvM : v.stk (.inr .rowCount) = List.replicate R.declaredM true := by simpa [v, canonicalGlobalProductEval, globalScanPort] using hM
  have hvP : v.stk (globalScanPort (.inr .savedCount)) = List.replicate (R.N * R.declaredM) true := by simp [v, canonicalGlobalProductEval]
  have hvt : v.stk (globalScanPort (.inr .copyTemp)) = [] := by
    simpa [v, canonicalGlobalProductEval, globalScanPort] using hempty .copyTemp (by simp [scanWorkExtras])
  have hec := canonicalScalarAssembly_executes R.N R.declaredM (R.N * R.declaredM) v hvN hvM hvP hvt
  have hvempty : ∀ k ∈ [CanonicalGlobalPort.alphabet, .markerThreshold, .blockCounter], v.stk (.inr k) = [] := by
    intro k hk
    have hkN : k ≠ .universe := by intro h; subst k; simp at hk
    have hkM : k ≠ .rowCount := by intro h; subst k; simp at hk
    have hkK : k ≠ .budget := by intro h; subst k; simp at hk
    rw [canonicalGlobalProduct_extra _ _ _ _ (by simp [globalScanPort]) (by simp [globalScanPort]) (by simp [globalScanPort])]
    rw [canonicalGlobalHeader_extra _ _ (by simp [globalScanPort])
      (by simpa using hkN) (by simpa using hkM) (by simpa using hkK)]
    exact hglobals k
  obtain ⟨hA, hT, hB⟩ := canonicalScalarAssembly_values R.N R.declaredM (R.N * R.declaredM) v hvN hvM hvP
    (hvempty .alphabet (by simp)) (hvempty .markerThreshold (by simp)) (hvempty .blockCounter (by simp))
  have hwold : ∀ k : NumericStack UnaryScanPort, w.stk (globalScanPort k) = v.stk (globalScanPort k) := by
    intro k; exact canonicalScalarAssembly_extra v _ (by simp [globalScanPort]) (by simp [globalScanPort]) (by simp [globalScanPort])
  have hmass : cleanupMass canonicalInitializationOwned w ≤ L + R.N + R.declaredM + R.N * R.declaredM := by
    have heq : cleanupMass canonicalInitializationOwned w =
        (u.stk (globalScanPort (.inl .source))).length + R.N + R.declaredM + R.N * R.declaredM := by
      simp only [cleanupMass, canonicalInitializationOwned, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hwold, hwold, hwold, hwold]
      simp [v, canonicalGlobalProductEval, globalScanPort, Nat.add_assoc]
    rw [heq]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hsrc R.N) R.declaredM) (R.N * R.declaredM)
  obtain ⟨d, hd, hed⟩ := clearMany_executes canonicalInitializationOwned w
  have hd' : d ≤ L + R.N + R.declaredM + R.N * R.declaredM + 5 := by
    have hk : canonicalInitializationOwned.length = 4 := rfl
    rw [hk] at hd; omega
  have hNd : R.N ≤ L := by simpa [hN] using hNb
  have hMd : R.declaredM ≤ L := by simpa [hM] using hMb
  have hprod := Nat.mul_le_mul hNd hMd
  have hall := RoutineComposition.seq_executes _ _ hea
    (RoutineComposition.seq_executes _ _ heb (RoutineComposition.seq_executes _ _ hec hed))
  have hglobal : ∀ k : CanonicalGlobalPort,
      (canonicalGlobalsEval R s).stk (.inr k) = w.stk (.inr k) := by
    intro k; exact clearMany_outside _ _ (by simp [canonicalInitializationOwned, globalScanPort]) _
  refine ⟨a + (b + ((6 * R.N + 6 * (R.N * R.declaredM) + 3 * R.declaredM + 19) + d)),
    ?_, hall, canonicalGlobals_ready R L s hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    canonicalGlobals_filter_extra R s, ?_⟩
  · unfold canonicalGlobalsBound; nlinarith
  · rw [canonicalGlobals_old_extra R s (.inr .queries) (by decide) (by decide) (by decide) (by decide)]; exact hq
  · exact canonicalGlobals_old_extra R s (.inr .original) (by decide) (by decide) (by decide) (by decide)
  · rw [hglobal, canonicalScalarAssembly_extra _ _ (by decide) (by decide) (by decide)]; exact hvN
  · rw [hglobal, canonicalScalarAssembly_extra _ _ (by decide) (by decide) (by decide)]
    simpa only [← hR.1] using hvM
  · rw [hglobal, canonicalScalarAssembly_extra _ _ (by decide) (by decide) (by decide)]
    simpa [v, canonicalGlobalProductEval, globalScanPort] using hK
  · rw [hglobal]
    simpa [rawRowAlphabet, privateCount, ← hR.1, Nat.mul_comm, Nat.add_assoc] using hA
  · rw [hglobal]
    simpa [originalMarkerThreshold, privateCount, ← hR.1, Nat.mul_comm, Nat.add_assoc] using hT
  · rw [hglobal]; simpa only [← hR.1] using hB
  · rfl

/- Global N,m,K, A=N+mN+3, marker=N+mN+1 and outer countdown m are
now created by actual transitions, not entry-word witnesses. This is only
the ORIGINAL VALID canonical branch's initializer; per-block preparation,
full ordering/controller, boundary branches, original budget/header
serializer and standalone caller control still remain. Independent target
verifier, closed encoded hardness and all dependency/kernel checks remain.
-/

end PolytomyReductionModel
