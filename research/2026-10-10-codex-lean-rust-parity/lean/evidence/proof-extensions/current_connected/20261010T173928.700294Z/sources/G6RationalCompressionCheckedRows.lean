import G6RationalCompressionCertificateFacts

/-!
# Listed finite checks supply certificates for every original population row

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Uses the pinned core `List.all_eq_true` and the accepted ground theorem for
the unchanged saved fixture. One generic list-membership proof supplies any
positive certificate to the already accepted rational-to-real source consumer.
No finite data, elimination algorithm, source recurrence or coefficient table
is introduced. This proof-only consumer is pending the sole scheduler's kernel
compilation and complete owned audit.

List membership is the exact premise binding the supplied typed data to the
saved checks. It does not establish general native parsing or RREF refinement,
resource bounds, calendar exponential representation or positive source
reconstruction. The source conclusion retains co-location and the live cap.
-/

namespace GProgram.G6.RationalCompressionCheckedRows

open GProgram.G6.RationalCompressionCertificate
open GProgram.G6.RationalCompressionCertificateFixture
open GProgram.G6.OriginalPopulationGeneratorBounds
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.SinglePopulationPolynomialKernel
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open scoped BigOperators

/-- Project any expected outcome from the one accepted kernel ground fact. -/
theorem listed_check_eq_expected (name : String) (actual expected : Bool)
    (hmem : (name, actual, expected) ∈ checks) : actual = expected := by
  have hall : checks.all (fun (_, actual, expected) => actual == expected) = true :=
    allChecksPass_true
  have h := (List.all_eq_true.mp hall) (name, actual, expected) hmem
  exact beq_iff_eq.mp h

/-- A listed positive check is a full exact rational moment certificate. -/
theorem listed_certificate {n r : ℕ} (M : ℕ) (z alpha : Fin n → ℚ)
    (atom : Fin r → Fin n) (beta : Fin r → ℚ) (name : String)
    (hmem : (name, checkCompression M z alpha atom beta, true) ∈ checks) :
    CertificateHolds M z alpha atom beta := by
  exact (checkCompression_correct M z alpha atom beta).mp
    (listed_check_eq_expected name _ true hmem)

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The same listed data and atom indices work for every original source row.
The destination remains the full inherited Code, including noncanonical codes. -/
theorem listed_uniform_original_population_compression {n r : ℕ} (M : ℕ)
    (z alpha : Fin n → ℚ) (atom : Fin r → Fin n) (beta : Fin r → ℚ)
    (name : String)
    (hmem : (name, checkCompression M z alpha atom beta, true) ∈ checks) :
    ∀ (N : RootedBinary V E X) (sample : Copy → X) (s d : Code N sample)
      (i : Option E), CoLocated N s i → liveCard s ≤ M →
      (∑ a, (alpha a : ℝ) * populationQuotient N M s d (z a : ℝ)) =
        ∑ b, (beta b : ℝ) * populationQuotient N M s d (z (atom b) : ℝ) := by
  exact checked_uniform_original_population_compression M z alpha atom beta
    (listed_check_eq_expected name _ true hmem)

#print axioms listed_check_eq_expected
#print axioms listed_certificate
#print axioms listed_uniform_original_population_compression

end GProgram.G6.RationalCompressionCheckedRows
