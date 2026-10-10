import G6PositiveGeneratorCompression
import G6RationalAffineWitness

/-!
# Exact rational atom certificates imply full original-row compression

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Consumes the accepted positive generator-compression theorem and existing
rational sum/cast identities. This checks supplied original atom indices and
weights; it contains no elimination, source coefficient or network engine.
The September 30 / October 1 elimination predecessors and the current exact
Fraction prototype are pinned in the dated legal-factor/extractor reuse audit.

The checker is executable over finite rational data. Its mathematical consumer
uses real source kernels. Successful certificates do not establish native
parser refinement, Gaussian-elimination completeness/resource bounds, arbitrary
real extraction, calendar exponential representations or positive source
reconstruction. Draft pending sole-scheduler kernel and complete owned audit.
-/

namespace GProgram.G6.RationalCompressionCertificate

open GProgram.G6.PositiveGeneratorCompression
open GProgram.G6.OriginalPopulationGeneratorBounds
open UnifiedLean.G6.RationalAffineWitness
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.SinglePopulationPolynomialKernel
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open scoped BigOperators

/-- The already-used geometric moment, computed with exact rational data. -/
def rationalGeometricSum (n : ℕ) (z : ℚ) : ℚ :=
  ∑ j ∈ Finset.range n, z ^ j

def rationalTailVector (M : ℕ) (z : ℚ) : Fin (M - 2) → ℚ :=
  fun j => rationalGeometricSum ((j.val + 3).choose 2) z

/-- `atom` retains the original index even when two supplied values coincide.
Mass supplies the omitted two-lineage coordinate. Zero total mass may use an
empty output; every retained output weight must be strictly positive. -/
def CertificateHolds {n r : ℕ} (M : ℕ) (z alpha : Fin n → ℚ)
    (atom : Fin r → Fin n) (beta : Fin r → ℚ) : Prop :=
  2 ≤ M ∧ (∀ a, 0 < z a ∧ z a < 1) ∧ (∀ a, 0 ≤ alpha a) ∧
    r ≤ M - 1 ∧ (∀ b, 0 < beta b) ∧ (∑ b, beta b) = ∑ a, alpha a ∧
    ∀ j : Fin (M - 2),
      (∑ a, alpha a * rationalTailVector M (z a) j) =
        ∑ b, beta b * rationalTailVector M (z (atom b)) j

instance certificateDecidable {n r : ℕ} (M : ℕ) (z alpha : Fin n → ℚ)
    (atom : Fin r → Fin n) (beta : Fin r → ℚ) :
    Decidable (CertificateHolds M z alpha atom beta) := by
  unfold CertificateHolds
  infer_instance

def checkCompression {n r : ℕ} (M : ℕ) (z alpha : Fin n → ℚ)
    (atom : Fin r → Fin n) (beta : Fin r → ℚ) : Bool :=
  decide (CertificateHolds M z alpha atom beta)

theorem checkCompression_correct {n r : ℕ} (M : ℕ) (z alpha : Fin n → ℚ)
    (atom : Fin r → Fin n) (beta : Fin r → ℚ) :
    checkCompression M z alpha atom beta = true ↔ CertificateHolds M z alpha atom beta := by
  simp only [checkCompression,decide_eq_true_eq]

theorem cast_rationalGeometricSum (n : ℕ) (z : ℚ) :
    (rationalGeometricSum n z : ℝ) = geometricSum n (z : ℝ) := by
  simp only [rationalGeometricSum,geometricSum,rat_cast_sum,Rat.cast_pow]

theorem cast_rationalTailVector (M : ℕ) (z : ℚ) (j : Fin (M - 2)) :
    (rationalTailVector M z j : ℝ) = tailVector M (z : ℝ) j := by
  exact cast_rationalGeometricSum ((j.val + 3).choose 2) z

/-- A supplied finite certificate becomes precisely the carrier-free premises
of the existing source transfer. No noncomputable atom choice is used. -/
theorem checked_real_moments {n r : ℕ} (M : ℕ) (z alpha : Fin n → ℚ)
    (atom : Fin r → Fin n) (beta : Fin r → ℚ)
    (h : checkCompression M z alpha atom beta = true) :
    2 ≤ M ∧ (∀ a, 0 < (z a : ℝ) ∧ (z a : ℝ) < 1) ∧
      (∀ a, 0 ≤ (alpha a : ℝ)) ∧ r ≤ M - 1 ∧
      (∀ b, 0 < (beta b : ℝ)) ∧ (∑ b, (beta b : ℝ)) = ∑ a, (alpha a : ℝ) ∧
      ∀ j : Fin (M - 2),
        (∑ a, (alpha a : ℝ) * tailVector M (z a : ℝ) j) =
          ∑ b, (beta b : ℝ) * tailVector M (z (atom b) : ℝ) j := by
  obtain ⟨hM,hz,ha,hr,hb,hm,ht⟩ :=
    (checkCompression_correct M z alpha atom beta).mp h
  refine ⟨hM,?_,?_,hr,?_,?_,?_⟩
  · intro a
    constructor
    · exact_mod_cast (hz a).1
    · exact_mod_cast (hz a).2
  · intro a
    exact_mod_cast ha a
  · intro b
    exact_mod_cast hb b
  · have hc := congrArg (fun q : ℚ => (q : ℝ)) hm
    simpa only [rat_cast_sum] using hc
  · intro j
    have hc := congrArg (fun q : ℚ => (q : ℝ)) (ht j)
    simpa only [rat_cast_sum,Rat.cast_mul,cast_rationalTailVector] using hc

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Every destination is the inherited original Code, including noncanonical
admitted representations. Co-location and live-count cap are source premises. -/
theorem checked_original_population_compression {n r : ℕ} (M : ℕ)
    (z alpha : Fin n → ℚ) (atom : Fin r → Fin n) (beta : Fin r → ℚ)
    (h : checkCompression M z alpha atom beta = true)
    (N : RootedBinary V E X) {sample : Copy → X} (s d : Code N sample)
    (i : Option E) (hs : CoLocated N s i) (hcap : liveCard s ≤ M) :
    (∑ a, (alpha a : ℝ) * populationQuotient N M s d (z a : ℝ)) =
      ∑ b, (beta b : ℝ) * populationQuotient N M s d (z (atom b) : ℝ) := by
  obtain ⟨hM,hz,_,_,_,hm,ht⟩ := checked_real_moments M z alpha atom beta h
  exact original_population_compression M hM
    (fun a => (z a : ℝ)) (fun a => (alpha a : ℝ)) atom (fun b => (beta b : ℝ))
    (fun a => (hz a).2) hm ht N s d i hs hcap

/-- The one supplied successful certificate precedes all source rows. -/
theorem checked_uniform_original_population_compression {n r : ℕ} (M : ℕ)
    (z alpha : Fin n → ℚ) (atom : Fin r → Fin n) (beta : Fin r → ℚ)
    (h : checkCompression M z alpha atom beta = true) :
    ∀ (N : RootedBinary V E X) (sample : Copy → X) (s d : Code N sample)
      (i : Option E), CoLocated N s i → liveCard s ≤ M →
      (∑ a, (alpha a : ℝ) * populationQuotient N M s d (z a : ℝ)) =
        ∑ b, (beta b : ℝ) * populationQuotient N M s d (z (atom b) : ℝ) := by
  intro N sample s d i hs hcap
  exact checked_original_population_compression M z alpha atom beta h N s d i hs hcap

#print axioms checkCompression_correct
#print axioms cast_rationalGeometricSum
#print axioms checked_real_moments
#print axioms checked_original_population_compression
#print axioms checked_uniform_original_population_compression

end GProgram.G6.RationalCompressionCertificate
