import UnifiedLean.G6.FiniteProbability

/-!
Verified PMF conditioning supplies domination, subsequently instantiated at
the unchanged actual countPMF and sourceIteration. No approximation hypothesis
is a field of a source model. Classical conditioning alone is not an effective
rational coefficient algorithm.
-/
namespace UnifiedLean.G6.Conditioning
open scoped BigOperators ENNReal
open UnifiedLean.G6.FiniteProbability

noncomputable def retainedMass {A : Type*} (p : PMF A) (s : Set A) : ℝ≥0∞ :=
  ∑' a, s.indicator p a

lemma retainedMass_ne_zero {A : Type*} (p : PMF A) (s : Set A)
    (h : ∃ a ∈ s, a ∈ p.support) : retainedMass p s ≠ 0 := by
  simpa [retainedMass] using h

lemma retainedMass_ne_top {A : Type*} (p : PMF A) (s : Set A) :
    retainedMass p s ≠ ⊤ := p.tsum_coe_indicator_ne_top s

lemma retainedMass_le_one {A : Type*} (p : PMF A) (s : Set A) :
    retainedMass p s ≤ 1 := by
  calc
    retainedMass p s ≤ ∑' a, p a :=
      ENNReal.tsum_le_tsum (fun a => Set.indicator_apply_le (fun _ => le_rfl))
    _ = 1 := p.tsum_coe

lemma filter_scaled {A : Type*} (p : PMF A) (s : Set A)
    (h : ∃ a ∈ s, a ∈ p.support) (a : A) :
    retainedMass p s * (p.filter s h) a = s.indicator p a := by
  rw [PMF.filter_apply]
  change retainedMass p s * (s.indicator p a * (retainedMass p s)⁻¹) = _
  calc
    _ = s.indicator p a * (retainedMass p s * (retainedMass p s)⁻¹) := by ac_rfl
    _ = s.indicator p a := by
      rw [ENNReal.mul_inv_cancel (retainedMass_ne_zero p s h) (retainedMass_ne_top p s), mul_one]

theorem filtered_bind_domination {A B : Type*} (p : PMF A) (s : Set A)
    (h : ∃ a ∈ s, a ∈ p.support) (f : A → PMF B) (b : B) :
    retainedMass p s * ((p.filter s h).bind f) b ≤ (p.bind f) b := by
  calc
    _ = ∑' a, retainedMass p s * ((p.filter s h) a * f a b) := by
      rw [PMF.bind_apply, ENNReal.tsum_mul_left]
    _ = ∑' a, s.indicator p a * f a b := by
      apply tsum_congr
      intro a
      rw [← mul_assoc, filter_scaled]
    _ ≤ ∑' a, p a * f a b := by
      apply ENNReal.tsum_le_tsum
      intro a
      exact mul_le_mul' (Set.indicator_apply_le (fun _ => le_rfl)) le_rfl
    _ = _ := (PMF.bind_apply p f b).symm

theorem filtered_bind_domination_real {A B : Type*} (p : PMF A) (s : Set A)
    (h : ∃ a ∈ s, a ∈ p.support) (f : A → PMF B) (b : B) :
    (retainedMass p s).toReal * (((p.filter s h).bind f) b).toReal ≤
      ((p.bind f) b).toReal := by
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (PMF.apply_ne_top (p.bind f) b)
    (filtered_bind_domination p s h f b)

lemma retainedMass_real_bounds {A : Type*} (p : PMF A) (s : Set A) :
    0 ≤ (retainedMass p s).toReal ∧ (retainedMass p s).toReal ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top (retainedMass_le_one p s)

lemma retainedMass_finset {A : Type*} (p : PMF A) (s : Finset A) :
    retainedMass p (s : Set A) = ∑ a ∈ s, p a := by
  classical
  unfold retainedMass
  rw [tsum_eq_sum (s := s) (fun a ha => by simp [ha])]
  exact Finset.sum_congr rfl (fun a ha => Set.indicator_of_mem ha p)

theorem conditioned_mixture_tv {A B : Type*} [Fintype B]
    (p : PMF A) (s : Set A) (h : ∃ a ∈ s, a ∈ p.support) (f : A → PMF B) :
    pmfTV (p.bind f) ((p.filter s h).bind f) ≤ 1 - (retainedMass p s).toReal :=
  pmf_scaled_domination_tv _ _ _ (retainedMass_real_bounds p s).2
    (filtered_bind_domination_real p s h f)

theorem conditioned_joint_observation_tv {A B O : Type*} [Fintype O]
    (p : PMF A) (s : Set A) (h : ∃ a ∈ s, a ∈ p.support)
    (f : A → PMF B) (readout : B → O) :
    pmfTV ((p.bind f).map readout) (((p.filter s h).bind f).map readout) ≤
      1 - (retainedMass p s).toReal := by
  rw [PMF.map_bind, PMF.map_bind]
  exact conditioned_mixture_tv p s h (fun a => (f a).map readout)

theorem conditioned_joint_observation_event {A B O : Type*} [Fintype O]
    (p : PMF A) (s : Set A) (h : ∃ a ∈ s, a ∈ p.support)
    (f : A → PMF B) (readout : B → O) (event : Finset O) :
    |(∑ o ∈ event, (((p.bind f).map readout) o).toReal) -
      ∑ o ∈ event, ((((p.filter s h).bind f).map readout) o).toReal| ≤
      1 - (retainedMass p s).toReal := by
  rw [PMF.map_bind, PMF.map_bind]
  exact pmf_scaled_domination_event _ _ _ (retainedMass_real_bounds p s).2
    (filtered_bind_domination_real p s h (fun a => (f a).map readout)) event

#print axioms filter_scaled
#print axioms filtered_bind_domination
#print axioms filtered_bind_domination_real
#print axioms conditioned_mixture_tv
#print axioms conditioned_joint_observation_tv
#print axioms conditioned_joint_observation_event
end UnifiedLean.G6.Conditioning
