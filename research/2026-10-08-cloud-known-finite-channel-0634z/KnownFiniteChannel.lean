import UnifiedLean.G6.CorruptionClasses
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
CLOUD-G6-SOL-ULTRA-20261007. Compiler UNCHECKED; outside179.
A known finite observation channel is ONE fixed stochastic kernel for all
sources and all compared laws. Its actual PMF bind is used throughout.
No biological measurement channel, inverse or effective table is assumed.
-/
namespace UnifiedLean.G6.KnownFiniteChannel

open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open UnifiedLean.G6.CorruptionClasses
open scoped BigOperators Classical
variable {A B : Type*} [Fintype A] [Fintype B]

theorem bind_real (p : PMF A) (K : A → PMF B) (b : B) :
    (p.bind K b).toReal = ∑ a, (p a).toReal * (K a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype (L := SummationFilter.unconditional A),
    ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top
      (p.apply_ne_top a) ((K a).apply_ne_top b))]
  simp only [ENNReal.toReal_mul]

/-- Data processing for the SAME actual finite stochastic channel. -/
theorem pmfTV_bind_contraction (p q : PMF A) (K : A → PMF B) :
    pmfTV (p.bind K) (q.bind K) ≤ pmfTV p q := by
  have hpoint (b : B) :
      |(p.bind K b).toReal - (q.bind K b).toReal| ≤
        ∑ a, |(p a).toReal - (q a).toReal| * (K a b).toReal := by
    rw [bind_real, bind_real, ← Finset.sum_sub_distrib]
    have heq : (∑ a, (p a).toReal * (K a b).toReal -
        (q a).toReal * (K a b).toReal) =
        ∑ a, ((p a).toReal - (q a).toReal) * (K a b).toReal := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [heq]
    simpa only [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg] using
      Finset.abs_sum_le_sum_abs
        (fun a => ((p a).toReal - (q a).toReal) * (K a b).toReal) Finset.univ
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hpoint b)
  have hcollapse : (∑ b, ∑ a,
      |(p a).toReal - (q a).toReal| * (K a b).toReal) =
      ∑ a, |(p a).toReal - (q a).toReal| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum, pmf_sum_real, mul_one]
  rw [hcollapse] at hsum
  unfold pmfTV tv
  linarith

def channelImage (K : A → PMF B) (laws : Set (PMF A)) : Set (PMF B) :=
  (fun p => p.bind K) '' laws

/-- Limiting input laws push to limiting output laws, using contraction;
the limit need not be the law of an actual biological source. -/
theorem bind_mem_tvClosure (K : A → PMF B) (laws : Set (PMF A))
    (q : PMF A) (hq : q ∈ tvClosure laws) :
    q.bind K ∈ tvClosure (channelImage K laws) := by
  intro epsilon hepsilon
  obtain ⟨r, hr, hqr⟩ := hq epsilon hepsilon
  exact ⟨r.bind K, ⟨r, hr, rfl⟩,
    lt_of_le_of_lt (pmfTV_bind_contraction q r K) hqr⟩

/-- Pushing a pre-channel corruption gives a permitted post-channel
corruption. This is inclusion, not equality of those two error models. -/
theorem channel_expanded_subset (K : A → PMF B)
    (laws : Set (PMF A)) (beta : ℝ) :
    channelImage K (expanded laws beta) ⊆
      expanded (channelImage K laws) beta := by
  rintro z ⟨r, ⟨q, hq, hqr⟩, rfl⟩
  exact ⟨q.bind K, ⟨q, hq, rfl⟩,
    le_trans (pmfTV_bind_contraction q r K) hqr⟩

/-- A wrong-closure law within the clean two-radius boundary remains
within that boundary after any one fixed known finite channel. -/
theorem wrong_closure_boundary_pushes (K : A → PMF B)
    (p : PMF A) (laws : Set (PMF A)) (beta : ℝ)
    (hboundary : ∃ q ∈ tvClosure laws, pmfTV p q ≤ 2 * beta) :
    ∃ q ∈ tvClosure (channelImage K laws), pmfTV (p.bind K) q ≤ 2 * beta := by
  obtain ⟨q, hq, hpq⟩ := hboundary
  exact ⟨q.bind K, bind_mem_tvClosure K laws q hq,
    le_trans (pmfTV_bind_contraction p q K) hpq⟩

/-- Output robust separation requires input robust separation at the
same TV radius. A known channel alone cannot create that separation. -/
theorem channel_separation_requires_clean_separation (K : A → PMF B)
    (p : PMF A) (laws : Set (PMF A)) (beta : ℝ)
    (houtput : allCorruptionsSeparated (p.bind K)
      (tvClosure (channelImage K laws)) beta) :
    allCorruptionsSeparated p (tvClosure laws) beta := by
  rw [all_corruptions_separated_iff] at houtput ⊢
  intro q hq
  exact lt_of_lt_of_le
    (houtput (q.bind K) (bind_mem_tvClosure K laws q hq))
    (pmfTV_bind_contraction p q K)

#print axioms bind_real
#print axioms pmfTV_bind_contraction
#print axioms bind_mem_tvClosure
#print axioms channel_expanded_subset
#print axioms wrong_closure_boundary_pushes
#print axioms channel_separation_requires_clean_separation

end UnifiedLean.G6.KnownFiniteChannel
