/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

All original words: real pipeline, charged ALL-PATH mass cleanup,
one-bit emission and exact reset. The fixed-code space lemma includes
malformed and early-rejected prefixes; no success-only tape bound is
silently used for them. The machine boundary is packaged separately.
-/
import PolytomyFixedCodeSpaceBound

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem restrictedInitial_stack_bound (bits : List Bool) :
    ∀ k, ((restrictedInitialStore bits).stk k).length ≤ bits.length := by
  intro k
  cases k with
  | inl n => cases n <;> simp [restrictedInitialStore, numericStore, numericStacks]
  | inr j => simp [restrictedInitialStore, numericStore, numericStacks]

noncomputable def restrictedPrefixPushCap : ℕ := codePushCap restrictedPrefixRoutine.code

def restrictedPrefixPolynomial : Polynomial ℕ :=
  14 * Polynomial.X ^ 3 + 110 * Polynomial.X ^ 2 + 447 * Polynomial.X + 603

theorem restrictedPrefixPolynomial_eval (L : ℕ) :
    restrictedPrefixPolynomial.eval L = restrictedPrefixBound L := by
  simp [restrictedPrefixPolynomial, restrictedPrefixBound_expansion]

theorem restrictedPrefix_stack_bound (bits : List Bool) :
    ∀ k, ((restrictedPrefixResult bits).stk k).length ≤
      bits.length + restrictedPrefixPushCap * restrictedPrefixBound bits.length := by
  obtain ⟨n, hn, he⟩ := restrictedPrefix_executes bits
  have hs := routine_executes_stack_bound restrictedPrefixRoutine (restrictedInitialStore bits)
    (restrictedPrefixResult bits) n bits.length he (restrictedInitial_stack_bound bits)
  intro k
  exact (hs k).trans (Nat.add_le_add_left (Nat.mul_le_mul_left restrictedPrefixPushCap hn) bits.length)

/-- Uniform on all original inputs. The fixed finite inventory may be
large, but its length and syntactic push cap are constants of this one
machine, not unbounded encoded header values or semantic oracle costs. -/
theorem restrictedPrefix_mass_bound (bits : List Bool) :
    cleanupMass restrictedCleanupOwned (restrictedPrefixResult bits) ≤
      restrictedCleanupOwned.length *
        (bits.length + restrictedPrefixPushCap * restrictedPrefixBound bits.length) :=
  cleanupMass_uniform_bound restrictedCleanupOwned (restrictedPrefixResult bits) _
    (restrictedPrefix_stack_bound bits)

noncomputable def restrictedCleanupPolynomial : Polynomial ℕ :=
  Polynomial.C restrictedCleanupOwned.length *
    (Polynomial.X + Polynomial.C restrictedPrefixPushCap * restrictedPrefixPolynomial) +
    Polynomial.C (restrictedCleanupOwned.length + 3)

noncomputable def restrictedVerifierPolynomial : Polynomial ℕ :=
  restrictedPipelinePolynomial + restrictedCleanupPolynomial

theorem restrictedVerifierPolynomial_eval (L : ℕ) :
    restrictedVerifierPolynomial.eval L = restrictedPipelinePolynomial.eval L +
      restrictedCleanupOwned.length * (L + restrictedPrefixPushCap * restrictedPrefixBound L) +
      restrictedCleanupOwned.length + 3 := by
  simp [restrictedVerifierPolynomial, restrictedCleanupPolynomial, restrictedPrefixPolynomial_eval]
  <;> ring

/-- The requested complete routine contract, as SOURCE ONLY. All actual
calls, failure skips, public cleanup, one-bit emission and public/private
control reset are included. The specification remains the exact original
restricted marked-star scanPairVerifier, not arbitrary Carta/DAG input. -/
theorem restrictedVerifier_all_words (bits : List Bool) :
    ∃ n ≤ restrictedVerifierPolynomial.eval bits.length,
      restrictedVerifierRoutine.Executes (restrictedInitialStore bits)
        (restrictedCleanStore (scanPairVerifier bits)) n := by
  obtain ⟨a, ha, hpipe, hstk⟩ := restrictedPipeline_executes bits
  obtain ⟨b, hb, hfinish⟩ := restrictedFinish_executes (restrictedPipelineResult bits)
  have hmass : cleanupMass restrictedCleanupOwned (restrictedPipelineResult bits) =
      cleanupMass restrictedCleanupOwned (restrictedPrefixResult bits) := by
    simp only [cleanupMass, hstk]
  have hm := restrictedPrefix_mass_bound bits
  rw [hmass] at hb
  rw [restrictedPipeline_original_bit] at hfinish
  refine ⟨a + b, ?_, RoutineComposition.seq_executes _ _ hpipe hfinish⟩
  rw [restrictedVerifierPolynomial_eval]
  omega

end PolytomyReductionModel.WholeVerifierController
