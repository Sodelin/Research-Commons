/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual classifier-to-constructor cleanup: clear all 31 work ports but
preserve the original record, final output and ALL finite branch flags.
The ordinary final cleanup still clears the original after output.
-/
import PolytomyOriginalConstructorEntry

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

def originalDispatchOwned : List CanonicalGlobalStack :=
  canonicalCleanupOwned.filter (fun k => decide (k ≠ globalScanPort (.inr .original)))

theorem originalDispatchOwned_complete (k : CanonicalGlobalStack) :
    k ∈ originalDispatchOwned ↔
      k ≠ globalFilterPort .output ∧ k ≠ globalScanPort (.inr .original) := by
  simp [originalDispatchOwned, canonicalCleanupOwned_complete]

theorem originalDispatchOwned_length : originalDispatchOwned.length = 31 := by decide

def originalDispatchCleanRoutine := clearManyRoutine (F := SelectedRowFrame) originalDispatchOwned
def originalDispatchCleanEval (s : CanonicalGlobalStore) := clearManyEval originalDispatchOwned s

theorem originalDispatchClean_state (s : CanonicalGlobalStore) :
    (originalDispatchCleanEval s).state = s.state := clearMany_state _ _

theorem originalDispatchClean_original (s : CanonicalGlobalStore) :
    (originalDispatchCleanEval s).stk (globalScanPort (.inr .original)) =
      s.stk (globalScanPort (.inr .original)) :=
  clearMany_outside _ _ (by rw [originalDispatchOwned_complete]; simp) _

theorem originalDispatchClean_output (s : CanonicalGlobalStore) :
    (originalDispatchCleanEval s).stk (globalFilterPort .output) = s.stk (globalFilterPort .output) :=
  clearMany_outside _ _ (by rw [originalDispatchOwned_complete]; simp) _

theorem originalDispatchClean_empty (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (ho : k ≠ globalFilterPort .output) (hr : k ≠ globalScanPort (.inr .original)) :
    (originalDispatchCleanEval s).stk k = [] :=
  clearMany_member _ _ ((originalDispatchOwned_complete k).mpr ⟨ho, hr⟩) _

theorem cleanupMass_filter_le {K F : Type} [DecidableEq K]
    (p : K → Bool) (ks : List K) (s : CountdownStore K F) :
    cleanupMass (ks.filter p) s ≤ cleanupMass ks s := by
  induction ks with
  | nil => simp [cleanupMass]
  | cons k ks ih =>
      cases hp : p k <;> simp [List.filter_cons, hp, cleanupMass] at * <;> omega

theorem originalDispatchClean_executes (s : CanonicalGlobalStore) :
    ∃ n ≤ cleanupMass canonicalCleanupOwned s + 32,
      originalDispatchCleanRoutine.Executes s (originalDispatchCleanEval s) n := by
  obtain ⟨n, hn, he⟩ := clearMany_executes originalDispatchOwned s
  have hm := cleanupMass_filter_le (fun k => decide (k ≠ globalScanPort (.inr .original))) canonicalCleanupOwned s
  change cleanupMass originalDispatchOwned s ≤ cleanupMass canonicalCleanupOwned s at hm
  rw [originalDispatchOwned_length] at hn
  exact ⟨n, by omega, he⟩

theorem originalDispatchClean_entry (L : ℕ) (s : CanonicalGlobalStore)
    (hL : (s.stk (globalScanPort (.inr .original))).length ≤ L)
    (hout : s.stk (globalFilterPort .output) = []) :
    OriginalConstructorEntry L (originalDispatchCleanEval s) := by
  apply originalConstructorEntry_of_only_original
  · intro k hk
    by_cases ho : k = globalFilterPort .output
    · subst k; exact (originalDispatchClean_output s).trans hout
    · exact originalDispatchClean_empty s k ho hk
  · rw [originalDispatchClean_original]; exact hL

/- This is unconditional cleanup, not a success-guarded countdown.
Branch flags intentionally survive; the canonical constructor accepts
arbitrary initial finite control and creates its own operational guards.
Every removed word is charged through the actual initial cleanup mass.
-/

end PolytomyReductionModel
