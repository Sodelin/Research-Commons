import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite common-subprobability and scaled-domination bounds.
Codex, CLOUD-G6-SOL-ULTRA-20261007, 2026-10-07.
Classical finite probability algebra; translates Astra's count/source handoff.
No biological source approximation is assumed or claimed by this module.
-/
namespace UnifiedLean.G6.FiniteProbability
open scoped BigOperators

noncomputable def tv {A : Type*} [Fintype A] (p q : A → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

theorem common_subprobability_tv {A : Type*} [Fintype A]
    (p q c : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1)
    (hcp : ∀ a, c a ≤ p a) (hcq : ∀ a, c a ≤ q a) :
    tv p q ≤ 1 - ∑ a, c a := by
  have hpoint (a : A) : |p a - q a| ≤ (p a - c a) + (q a - c a) := by
    apply abs_le.mpr
    constructor <;> linarith [hcp a, hcq a]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp, hq] at hsum
  unfold tv
  linarith

theorem common_subprobability_mass {A : Type*} [Fintype A]
    (p c : A → ℝ) (hp : ∑ a, p a = 1)
    (hc : ∀ a, 0 ≤ c a) (hcp : ∀ a, c a ≤ p a) :
    0 ≤ ∑ a, c a ∧ (∑ a, c a) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => hc a)
  · simpa only [hp] using Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hcp a)

theorem common_subprobability_event {A : Type*} [Fintype A]
    (p q c : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1)
    (hcp : ∀ a, c a ≤ p a) (hcq : ∀ a, c a ≤ q a) (event : Finset A) :
    |(∑ a ∈ event, p a) - ∑ a ∈ event, q a| ≤ 1 - ∑ a, c a := by
  have bounds (v : A → ℝ) (hv : ∑ a, v a = 1) (hcv : ∀ a, c a ≤ v a) :
      0 ≤ ∑ a ∈ event, (v a - c a) ∧
        (∑ a ∈ event, (v a - c a)) ≤ 1 - ∑ a, c a := by
    constructor
    · exact Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (hcv a))
    · have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ event)
          (fun a _ _ => sub_nonneg.mpr (hcv a))
      simpa only [Finset.sum_sub_distrib, hv] using h
  have bp := bounds p hp hcp
  have bq := bounds q hq hcq
  have heq : (∑ a ∈ event, p a) - ∑ a ∈ event, q a =
      (∑ a ∈ event, (p a - c a)) - ∑ a ∈ event, (q a - c a) := by
    simp only [Finset.sum_sub_distrib]
    ring
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith

theorem scaled_domination_tv {A : Type*} [Fintype A]
    (p q : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1)
    (hq0 : ∀ a, 0 ≤ q a) (mu : ℝ) (hmu : mu ≤ 1)
    (hdom : ∀ a, mu * q a ≤ p a) : tv p q ≤ 1 - mu := by
  have hsum : (∑ a, mu * q a) = mu := by rw [← Finset.mul_sum, hq, mul_one]
  simpa only [hsum] using common_subprobability_tv p q (fun a => mu * q a) hp hq
    hdom (fun a => by simpa using mul_le_mul_of_nonneg_right hmu (hq0 a))

lemma pmf_sum_real {A : Type*} [Fintype A] (p : PMF A) :
    (∑ a, (p a).toReal) = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a), ← tsum_fintype, p.tsum_coe]
  simp

noncomputable def pmfTV {A : Type*} [Fintype A] (p q : PMF A) : ℝ :=
  tv (fun a => (p a).toReal) (fun a => (q a).toReal)

theorem pmf_scaled_domination_tv {A : Type*} [Fintype A]
    (p q : PMF A) (mu : ℝ) (hmu : mu ≤ 1)
    (hdom : ∀ a, mu * (q a).toReal ≤ (p a).toReal) : pmfTV p q ≤ 1 - mu :=
  scaled_domination_tv _ _ (pmf_sum_real p) (pmf_sum_real q)
    (fun a => ENNReal.toReal_nonneg) mu hmu hdom

theorem pmf_scaled_domination_event {A : Type*} [Fintype A]
    (p q : PMF A) (mu : ℝ) (hmu : mu ≤ 1)
    (hdom : ∀ a, mu * (q a).toReal ≤ (p a).toReal) (event : Finset A) :
    |(∑ a ∈ event, (p a).toReal) - ∑ a ∈ event, (q a).toReal| ≤ 1 - mu := by
  have hsum : (∑ a, mu * (q a).toReal) = mu := by
    rw [← Finset.mul_sum, pmf_sum_real, mul_one]
  simpa only [hsum] using common_subprobability_event _ _ (fun a => mu * (q a).toReal)
    (pmf_sum_real p) (pmf_sum_real q) hdom
    (fun a => by simpa using mul_le_mul_of_nonneg_right hmu ENNReal.toReal_nonneg) event

#print axioms common_subprobability_tv
#print axioms common_subprobability_mass
#print axioms common_subprobability_event
#print axioms scaled_domination_tv
#print axioms pmf_sum_real
#print axioms pmf_scaled_domination_tv
#print axioms pmf_scaled_domination_event

end UnifiedLean.G6.FiniteProbability
