/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Whole original-constructor entry and complete invalid/fixed-target
terminal bounds. Entry contains only the original normalized word;
validity is NOT part of the entry assumptions.
-/
import PolytomyCanonicalLiteralBranch

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

structure OriginalConstructorEntry (L : ℕ) (s : CanonicalGlobalStore) : Prop where
  scan : UnaryScanReady 0 L (canonicalGlobalNumeric s)
  query_empty : s.stk (globalScanPort (.inr .queries)) = []
  globals_empty : ∀ k : CanonicalGlobalPort, s.stk (.inr k) = []
  filters_empty : ∀ k : CanonicalFilterPort, s.stk (globalFilterPort k) = []

theorem OriginalConstructorEntry.numeric_empty (L : ℕ) (s : CanonicalGlobalStore)
    (hs : OriginalConstructorEntry L s) (k : NumericPort) :
    s.stk (globalScanPort (.inl k)) = [] := by
  cases k with
  | source => exact hs.scan.source_empty
  | payload => exact hs.scan.numeric.1
  | cap => simpa using hs.scan.numeric.2.2.2.1
  | work => exact hs.scan.numeric.2.1
  | output => exact hs.scan.numeric.2.2.1

theorem OriginalConstructorEntry.empty (L : ℕ) (s : CanonicalGlobalStore)
    (hs : OriginalConstructorEntry L s) (k : CanonicalGlobalStack)
    (hk : k ≠ globalScanPort (.inr .original)) : s.stk k = [] := by
  rcases k with k | g
  · rcases k with k | f
    · rcases k with n | u
      · exact OriginalConstructorEntry.numeric_empty L s hs n
      · by_cases hq : u = .queries
        · subst u; exact hs.query_empty
        have ho : u ≠ .original := by simpa [globalScanPort] using hk
        have hm : u ∈ scanWorkExtras := by cases u <;> simp_all [scanWorkExtras]
        exact hs.scan.empty u hm
    · exact hs.filters_empty f
  · exact hs.globals_empty g

theorem originalConstructorEntry_of_only_original (L : ℕ) (s : CanonicalGlobalStore)
    (hclear : ∀ k : CanonicalGlobalStack, k ≠ globalScanPort (.inr .original) → s.stk k = [])
    (hL : (s.stk (globalScanPort (.inr .original))).length ≤ L) : OriginalConstructorEntry L s := by
  refine ⟨⟨?_, ?_, ?_, hL⟩, hclear _ (by decide), ?_, ?_⟩
  · refine ⟨hclear _ (by decide), hclear _ (by decide), hclear _ (by decide),
      hclear _ (by decide), ?_⟩
    rw [show (canonicalGlobalNumeric s).stk (.inl .source) = [] from hclear _ (by decide)]
    simp
  · exact hclear _ (by decide)
  · intro k hk
    have ho : k ≠ .original := by intro h; subst k; simp [scanWorkExtras] at hk
    exact hclear _ (by simpa [globalScanPort] using ho)
  · intro k; exact hclear _ (by simp [globalScanPort])
  · intro k; exact hclear _ (by simp [globalFilterPort, globalScanPort])

def originalConstructorInput (bits : List Bool) : CanonicalGlobalStore :=
  ⟨canonicalCleanState, Function.update (fun _ => []) (globalScanPort (.inr .original)) bits⟩

theorem originalConstructorInput_entry (bits : List Bool) :
    OriginalConstructorEntry bits.length (originalConstructorInput bits) := by
  apply originalConstructorEntry_of_only_original
  · intro k hk; simp [originalConstructorInput, hk]
  · simp [originalConstructorInput]

theorem originalConstructorEntry_mass (L : ℕ) (s : CanonicalGlobalStore)
    (hs : OriginalConstructorEntry L s) :
    cleanupMass canonicalCleanupOwned s = (s.stk (globalScanPort (.inr .original))).length := by
  have hn : ∀ k : NumericPort, s.stk (globalScanPort (.inl k)) = [] := OriginalConstructorEntry.numeric_empty L s hs
  have hu : ∀ k ∈ scanWorkExtras, s.stk (globalScanPort (.inr k)) = [] := hs.scan.empty
  simp [cleanupMass, canonicalCleanupOwned, hn, hu, scanWorkExtras,
    hs.query_empty, hs.globals_empty, hs.filters_empty]

theorem originalValidation_preserves_entry (L : ℕ) (s : CanonicalGlobalStore)
    (hs : OriginalConstructorEntry L s) : OriginalConstructorEntry L (globalOriginalValidationEval s) := by
  obtain ⟨n, hn, he, hr, hc, hp, hf⟩ := globalOriginalValidation_executes L s hs.scan hs.query_empty
  exact ⟨hr, hc, fun k => (globalOriginalValidation_global s k).trans (hs.globals_empty k),
    fun k => (globalOriginalValidation_filter s k).trans (hs.filters_empty k)⟩

theorem originalEntryLiteral_executes (bits : List Bool) (L : ℕ) (s : CanonicalGlobalStore)
    (hs : OriginalConstructorEntry L s) :
    ∃ n ≤ bits.length + L + 36, (canonicalLiteralRoutine bits).Executes s (canonicalCleanStore bits) n := by
  obtain ⟨n, hn, he⟩ := canonicalLiteral_executes bits s
  rw [hs.filters_empty .output, List.length_nil, zero_add, originalConstructorEntry_mass L s hs] at hn
  exact ⟨n, by have hL := hs.scan.original_bound; omega, he⟩

/- All malformed/tag-failed/count/range/coverage failures are handled
by the original validator BEFORE any N=0 shortcut. Its false branch can
now call this concrete original fixed-no terminal from the proved fresh
entry. This is still a component of the all-input constructor proof.
-/

end PolytomyReductionModel
