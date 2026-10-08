import UnifiedLean.G6.MeanEnclosure

/-!
CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026.
UNCHECKED source draft. Classical finite-simplex midpoint argument from the
accepted G6 hand proof, not a new scientific result. Full target-image closure,
closest wrong-law attainment and finite-read impossibility remain separate.
-/
namespace UnifiedLean.G6.FiniteCorruptionBoundary

open UnifiedLean.G6.FiniteProbability
open scoped BigOperators Classical

theorem pmfTV_symm {A : Type*} [Fintype A] (p q : PMF A) :
    pmfTV p q = pmfTV q p := by
  simp only [pmfTV, tv, abs_sub_comm]

theorem pmfTV_triangle {A : Type*} [Fintype A] (p q r : PMF A) :
    pmfTV p r ≤ pmfTV p q + pmfTV q r := by
  exact UnifiedLean.G6.MeanEnclosure.tv_triangle
    (fun a => (p a).toReal) (fun a => (q a).toReal) (fun a => (r a).toReal)

/-- An actual probability law; no zero-mass normalization or source matrix
is assumed. This is an allowed observed corruption, not a biological source. -/
noncomputable def midpointPMF {A : Type*} [Fintype A] (p q : PMF A) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (((p a).toReal + (q a).toReal) / 2)) (by
    have h0 (a : A) : 0 ≤ ((p a).toReal + (q a).toReal) / 2 :=
      div_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (by norm_num)
    have hsum : ENNReal.ofReal (∑ a, ((p a).toReal + (q a).toReal) / 2) =
        ∑ a, ENNReal.ofReal (((p a).toReal + (q a).toReal) / 2) :=
      ENNReal.ofReal_sum_of_nonneg (fun a _ => h0 a)
    rw [← hsum, Finset.sum_div, Finset.sum_add_distrib, pmf_sum_real, pmf_sum_real]
    norm_num)

theorem midpointPMF_real {A : Type*} [Fintype A] (p q : PMF A) (a : A) :
    (midpointPMF p q a).toReal = ((p a).toReal + (q a).toReal) / 2 := by
  change (ENNReal.ofReal (((p a).toReal + (q a).toReal) / 2)).toReal = _
  exact ENNReal.toReal_ofReal
    (div_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (by norm_num))

theorem midpointPMF_comm {A : Type*} [Fintype A] (p q : PMF A) :
    midpointPMF p q = midpointPMF q p := by
  ext a : 1
  change ENNReal.ofReal (((p a).toReal + (q a).toReal) / 2) =
    ENNReal.ofReal (((q a).toReal + (p a).toReal) / 2)
  rw [add_comm]

theorem midpointPMF_left_distance {A : Type*} [Fintype A] (p q : PMF A) :
    pmfTV p (midpointPMF p q) = pmfTV p q / 2 := by
  unfold pmfTV tv
  simp_rw [midpointPMF_real]
  have hpoint (a : A) :
      |(p a).toReal - ((p a).toReal + (q a).toReal) / 2| =
        |(p a).toReal - (q a).toReal| / 2 := by
    have he : (p a).toReal - ((p a).toReal + (q a).toReal) / 2 =
        ((p a).toReal - (q a).toReal) / 2 := by ring
    rw [he, abs_div]
    norm_num
  simp_rw [hpoint]
  rw [Finset.sum_div]

theorem midpointPMF_right_distance {A : Type*} [Fintype A] (p q : PMF A) :
    pmfTV q (midpointPMF p q) = pmfTV p q / 2 := by
  rw [midpointPMF_comm p q, midpointPMF_left_distance, pmfTV_symm q p]

/-- Closed TV balls overlap exactly at or below the sharp two-radius bound.
In particular equality belongs to the shared-observation side. -/
theorem shared_corruption_iff {A : Type*} [Fintype A]
    (p q : PMF A) (beta : ℝ) :
    (∃ z : PMF A, pmfTV p z ≤ beta ∧ pmfTV q z ≤ beta) ↔
      pmfTV p q ≤ 2 * beta := by
  constructor
  · rintro ⟨z, hp, hq⟩
    have ht := pmfTV_triangle p z q
    rw [pmfTV_symm z q] at ht
    linarith
  · intro h
    refine ⟨midpointPMF p q, ?_, ?_⟩
    · rw [midpointPMF_left_distance]
      linarith
    · rw [midpointPMF_right_distance]
      linarith

theorem no_shared_corruption_iff {A : Type*} [Fintype A]
    (p q : PMF A) (beta : ℝ) :
    (¬ ∃ z : PMF A, pmfTV p z ≤ beta ∧ pmfTV q z ≤ beta) ↔
      2 * beta < pmfTV p q := by
  rw [shared_corruption_iff, not_le]

/-- A useful sufficient certificate from two validated approximate vectors.
The approximation bounds are explicit inputs, not assumed source laws. -/
theorem certified_no_shared_corruption {A : Type*} [Fintype A]
    (p q phat qhat : PMF A) (beta ep eq : ℝ)
    (hp : pmfTV p phat ≤ ep) (hq : pmfTV q qhat ≤ eq)
    (hmargin : 2 * beta + ep + eq < pmfTV phat qhat) :
    ¬ ∃ z : PMF A, pmfTV p z ≤ beta ∧ pmfTV q z ≤ beta := by
  apply (no_shared_corruption_iff p q beta).mpr
  have h1 := pmfTV_triangle phat p qhat
  have h2 := pmfTV_triangle p q qhat
  rw [pmfTV_symm phat p] at h1
  linarith

#print axioms pmfTV_symm
#print axioms pmfTV_triangle
#print axioms midpointPMF_real
#print axioms midpointPMF_comm
#print axioms midpointPMF_left_distance
#print axioms midpointPMF_right_distance
#print axioms shared_corruption_iff
#print axioms no_shared_corruption_iff
#print axioms certified_no_shared_corruption

end UnifiedLean.G6.FiniteCorruptionBoundary
