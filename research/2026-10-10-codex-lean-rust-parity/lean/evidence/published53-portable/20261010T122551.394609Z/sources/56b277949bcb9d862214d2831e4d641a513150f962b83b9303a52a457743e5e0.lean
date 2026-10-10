import UnifiedLean.G6.TaylorCertificate
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Cast.Order

/-!
UNCHECKED until an exact pinned compiler receipt is attached.
Internal Lean lane, CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026.
Computable rational normalized count coefficients and a terminating certificate
cutoff search. Correspondence is proved against the actual Poisson-prefix
coefficients, rather than assumed as an approximation field.
Scope: rational uniformization mean and positive rational error budget. General
real physical parameter enclosures, backend table evaluation, timed-bin menus,
and biological reconstruction remain separate obligations.
-/
namespace UnifiedLean.G6.RationalCertificate
open UnifiedLean.G6.SourcePrefix UnifiedLean.G6.TaylorCertificate
open Filter
open scoped BigOperators Topology NNReal

def rationalTerm (q : ℚ) (k : ℕ) : ℚ := q ^ k / (k.factorial : ℚ)

def rationalPrefix (q : ℚ) (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (K + 1), rationalTerm q k

def rationalError (q : ℚ) (K : ℕ) : ℚ :=
  2 * rationalTerm q (K + 1) /
    (rationalPrefix q K + 2 * rationalTerm q (K + 1))

def rationalCount (q : ℚ) (K k : ℕ) : ℚ :=
  if k ≤ K then rationalTerm q k / rationalPrefix q K else 0

lemma rationalTerm_real (q : ℚ) (k : ℕ) :
    (rationalTerm q k : ℝ) = taylorTerm (q : ℝ) k := by
  simp [rationalTerm, taylorTerm]

lemma rationalPrefix_real (q : ℚ) (K : ℕ) :
    (rationalPrefix q K : ℝ) = taylorPrefix (q : ℝ) K := by
  simp [rationalPrefix, taylorPrefix, rationalTerm_real]

lemma rationalError_real (q : ℚ) (K : ℕ) :
    (rationalError q K : ℝ) = errorBound (q : ℝ) K := by
  simp [rationalError, errorBound, rationalTerm_real, rationalPrefix_real]

lemma rationalTerm_nonneg {q : ℚ} (hq : 0 ≤ q) (k : ℕ) :
    0 ≤ rationalTerm q k := by
  unfold rationalTerm
  positivity

lemma rationalPrefix_one_le {q : ℚ} (hq : 0 ≤ q) (K : ℕ) :
    1 ≤ rationalPrefix q K := by
  have h := Finset.single_le_sum (f := rationalTerm q)
    (fun k (_ : k ∈ Finset.range (K + 1)) => rationalTerm_nonneg hq k)
    (Finset.mem_range.mpr (Nat.succ_pos K) : 0 ∈ Finset.range (K + 1))
  simpa [rationalTerm, rationalPrefix] using h

/-- The computable coefficients equal the actual normalized count PMF. -/
theorem rationalCount_actual (q : ℚ) (a : ℝ≥0) (ha : (a : ℝ) = (q : ℝ))
    (K k : ℕ) :
    (rationalCount q K k : ℝ) = (prefixCount a K k).toReal := by
  rw [prefixCount_real, ha]
  by_cases hk : k ≤ K <;>
    simp [rationalCount, hk, rationalTerm_real, rationalPrefix_real]

lemma certificate_le_twice_term {q : ℚ} (hq : 0 ≤ q) (K : ℕ) :
    errorBound (q : ℝ) K ≤ 2 * taylorTerm (q : ℝ) (K + 1) := by
  have hqreal : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hS : (1 : ℝ) ≤ taylorPrefix (q : ℝ) K := by
    rw [← rationalPrefix_real]
    exact_mod_cast rationalPrefix_one_le hq K
  have hT := taylorTerm_nonneg hqreal (K + 1)
  have hD : 0 < taylorPrefix (q : ℝ) K + 2 * taylorTerm (q : ℝ) (K + 1) := by
    linarith
  unfold errorBound
  apply (div_le_iff₀ hD).mpr
  have hD1 : 1 ≤ taylorPrefix (q : ℝ) K + 2 * taylorTerm (q : ℝ) (K + 1) := by
    linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hD1
    (show 0 ≤ 2 * taylorTerm (q : ℝ) (K + 1) by positivity)

/-- Entire predicate uses exact decidable rational arithmetic. -/
def accepts (q ε : ℚ) (K : ℕ) : Prop :=
  2 * q ≤ (K : ℚ) + 2 ∧ rationalError q K ≤ ε

instance acceptsDecidable (q ε : ℚ) : DecidablePred (accepts q ε) :=
  fun K => by unfold accepts; infer_instance

/-- Positive rational budgets eventually pass; no desired TV premise is supplied. -/
theorem certificate_exists (q ε : ℚ) (hq : 0 ≤ q) (hε : 0 < ε) :
    ∃ K : ℕ, accepts q ε K := by
  have hεreal : (0 : ℝ) < ε := by exact_mod_cast hε
  have ht : Tendsto (fun K : ℕ => taylorTerm (q : ℝ) (K + 1)) atTop (𝓝 0) :=
    (taylor_hasSum (q : ℝ)).summable.tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
  have hz : Tendsto (fun K : ℕ => 2 * taylorTerm (q : ℝ) (K + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul ht
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp (hz.eventually_lt_const hεreal)
  obtain ⟨K1, hK1⟩ := exists_nat_gt (2 * (q : ℝ))
  let K := max K0 K1
  have hlarge : 2 * (q : ℝ) ≤ (K : ℝ) + 2 := by
    have hcast : (K1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_max_right K0 K1
    linarith
  have hsmall : errorBound (q : ℝ) K ≤ (ε : ℝ) :=
    (certificate_le_twice_term hq K).trans (hK0 K (le_max_left K0 K1)).le
  refine ⟨K, ?_⟩
  unfold accepts
  constructor
  · exact_mod_cast hlarge
  · rw [← rationalError_real] at hsmall
    exact_mod_cast hsmall

/-- Executable least-cutoff search, justified by the proved termination bound. -/
def cutoff (q ε : ℚ) (hq : 0 ≤ q) (hε : 0 < ε) : ℕ :=
  Nat.find (certificate_exists q ε hq hε)

theorem cutoff_accepts (q ε : ℚ) (hq : 0 ≤ q) (hε : 0 < ε) :
    accepts q ε (cutoff q ε hq hε) :=
  Nat.find_spec (certificate_exists q ε hq hε)

theorem cutoff_minimal (q ε : ℚ) (hq : 0 ≤ q) (hε : 0 < ε) (K : ℕ)
    (hK : accepts q ε K) : cutoff q ε hq hε ≤ K :=
  Nat.find_min' (certificate_exists q ε hq hε) hK

theorem cutoff_prefix_deficit (q ε : ℚ) (hq : 0 ≤ q) (hε : 0 < ε)
    (a : ℝ≥0) (ha : (a : ℝ) = (q : ℝ)) :
    1 - prefixMass a (cutoff q ε hq hε) ≤ (ε : ℝ) := by
  have h := cutoff_accepts q ε hq hε
  have hratio : 2 * (a : ℝ) ≤ (cutoff q ε hq hε : ℝ) + 2 := by
    rw [ha]
    exact_mod_cast h.1
  have herror : errorBound (q : ℝ) (cutoff q ε hq hε) ≤ (ε : ℝ) := by
    rw [← rationalError_real]
    exact_mod_cast h.2
  have hbound := prefix_deficit_le_certificate a (cutoff q ε hq hε) hratio
  rw [ha] at hbound
  exact hbound.trans herror

#print axioms rationalCount_actual
#print axioms certificate_exists
#print axioms cutoff_accepts
#print axioms cutoff_minimal
#print axioms cutoff_prefix_deficit
end UnifiedLean.G6.RationalCertificate
