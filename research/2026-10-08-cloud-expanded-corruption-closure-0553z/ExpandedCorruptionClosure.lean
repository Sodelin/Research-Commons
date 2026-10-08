import CoordinateTVClosure

/-!
CLOUD-G6-SOL-ULTRA-20261007. Additive source candidate, compiler UNCHECKED.
Closed corruption expansion commutes with finite-law closure. The radial
correction is an OBSERVED probability law, not an admitted biological source.
No positive hidden-parameter floor, evaluator or statistical master is added.
-/
namespace UnifiedLean.G6.ExpandedCorruptionClosure

open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open UnifiedLean.G6.CorruptionClasses UnifiedLean.G6.FiniteSimplexAttainment
open UnifiedLean.G6.CoordinateTVClosure
open scoped BigOperators Classical
variable {A : Type*} [Fintype A]

/-- A segment inside the actual finite probability simplex. -/
noncomputable def segmentPMF (p q : PMF A) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : PMF A :=
  coordinatePMF (fun x => (1 - a) * realLaw p x + a * realLaw q x) (by
    constructor
    · intro x
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr ha1) ENNReal.toReal_nonneg)
        (mul_nonneg ha0 ENNReal.toReal_nonneg)
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      change (1 - a) * (∑ x, (p x).toReal) + a * (∑ x, (q x).toReal) = 1
      rw [pmf_sum_real, pmf_sum_real]
      ring)

theorem segmentPMF_real (p q : PMF A) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (x : A) :
    (segmentPMF p q a ha0 ha1 x).toReal =
      (1 - a) * (p x).toReal + a * (q x).toReal := by
  unfold segmentPMF
  exact coordinatePMF_real _ _ x

theorem segmentPMF_left_distance (p q : PMF A) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    pmfTV p (segmentPMF p q a ha0 ha1) = a * pmfTV p q := by
  unfold pmfTV tv
  simp_rw [segmentPMF_real]
  have hpoint (x : A) :
      |(p x).toReal - ((1 - a) * (p x).toReal + a * (q x).toReal)| =
        a * |(p x).toReal - (q x).toReal| := by
    have he : (p x).toReal - ((1 - a) * (p x).toReal + a * (q x).toReal) =
        a * ((p x).toReal - (q x).toReal) := by ring
    rw [he, abs_mul, abs_of_nonneg ha0]
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  ring

theorem segmentPMF_right_distance (p q : PMF A) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    pmfTV q (segmentPMF p q a ha0 ha1) = (1 - a) * pmfTV q p := by
  unfold pmfTV tv
  simp_rw [segmentPMF_real]
  have hpoint (x : A) :
      |(q x).toReal - ((1 - a) * (p x).toReal + a * (q x).toReal)| =
        (1 - a) * |(q x).toReal - (p x).toReal| := by
    have he : (q x).toReal - ((1 - a) * (p x).toReal + a * (q x).toReal) =
        (1 - a) * ((q x).toReal - (p x).toReal) := by ring
    rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr ha1)]
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  ring

/-- A nearby clean law can be repaired into its allowed observed TV ball.
The same formula handles beta=0; denominator positivity comes from delta. -/
theorem radial_repair (r z : PMF A) (beta delta : ℝ)
    (hb : 0 ≤ beta) (hd : 0 < delta) (hrz : pmfTV r z ≤ beta + delta) :
    ∃ w : PMF A, pmfTV r w ≤ beta ∧ pmfTV z w ≤ delta := by
  have hden : 0 < beta + delta := by linarith
  have ha0 : 0 ≤ beta / (beta + delta) := div_nonneg hb hden.le
  have ha1 : beta / (beta + delta) ≤ 1 := (div_le_one hden).mpr (by linarith)
  let w := segmentPMF r z (beta / (beta + delta)) ha0 ha1
  refine ⟨w, ?_, ?_⟩
  · change pmfTV r (segmentPMF r z (beta / (beta + delta)) ha0 ha1) ≤ beta
    rw [segmentPMF_left_distance]
    calc
      _ ≤ (beta / (beta + delta)) * (beta + delta) :=
        mul_le_mul_of_nonneg_left hrz ha0
      _ = beta := div_mul_cancel₀ beta (ne_of_gt hden)
  · change pmfTV z (segmentPMF r z (beta / (beta + delta)) ha0 ha1) ≤ delta
    rw [segmentPMF_right_distance, pmfTV_symm z r]
    have hweight : 1 - beta / (beta + delta) = delta / (beta + delta) := by
      field_simp [ne_of_gt hden] <;> ring
    rw [hweight]
    calc
      _ ≤ (delta / (beta + delta)) * (beta + delta) :=
        mul_le_mul_of_nonneg_left hrz (div_nonneg hd.le hden.le)
      _ = delta := div_mul_cancel₀ delta (ne_of_gt hden)

theorem expanded_closure_subset_closure_expanded (laws : Set (PMF A))
    (beta : ℝ) (hb : 0 ≤ beta) :
    expanded (tvClosure laws) beta ⊆ tvClosure (expanded laws beta) := by
  rintro z ⟨q, hq, hqz⟩ epsilon hepsilon
  obtain ⟨r, hr, hqr⟩ := hq (epsilon / 2) (by linarith)
  have hrz : pmfTV r z ≤ beta + epsilon / 2 := by
    have ht := pmfTV_triangle r q z
    rw [pmfTV_symm r q] at ht
    linarith
  obtain ⟨w, hrw, hzw⟩ := radial_repair r z beta (epsilon / 2) hb
    (by linarith) hrz
  exact ⟨w, ⟨r, hr, hrw⟩, lt_of_le_of_lt hzw (by linarith)⟩

/-- Compact closest-law attainment gives the other inclusion. The minimizer
is derived from the entire clean-law image; it is never a source field. -/
theorem closure_expanded_subset_expanded_closure (laws : Set (PMF A))
    (beta : ℝ) :
    tvClosure (expanded laws beta) ⊆ expanded (tvClosure laws) beta := by
  intro z hz
  obtain ⟨y, ⟨r, hr, _⟩, _⟩ := hz 1 (by norm_num)
  obtain ⟨q, hq, hmin⟩ := exists_closest_tv_closure z laws ⟨r, hr⟩
  have hbound : pmfTV z q ≤ beta := by
    by_contra hbad
    have hgap : 0 < (pmfTV z q - beta) / 2 := by linarith
    obtain ⟨w, ⟨s, hs, hsw⟩, hzw⟩ := hz ((pmfTV z q - beta) / 2) hgap
    have hclosest := hmin s (mem_tvClosure hs)
    have ht := pmfTV_triangle z w s
    rw [pmfTV_symm w s] at ht
    linarith
  exact ⟨q, hq, by simpa only [pmfTV_symm q z] using hbound⟩

/-- Exact observed-image closure identity, including beta=0 and empty laws. -/
theorem closure_expanded_eq_expanded_closure (laws : Set (PMF A))
    (beta : ℝ) (hb : 0 ≤ beta) :
    tvClosure (expanded laws beta) = expanded (tvClosure laws) beta :=
  Set.Subset.antisymm (closure_expanded_subset_expanded_closure laws beta)
    (expanded_closure_subset_closure_expanded laws beta hb)

#print axioms segmentPMF_real
#print axioms segmentPMF_left_distance
#print axioms segmentPMF_right_distance
#print axioms radial_repair
#print axioms expanded_closure_subset_closure_expanded
#print axioms closure_expanded_subset_expanded_closure
#print axioms closure_expanded_eq_expanded_closure

end UnifiedLean.G6.ExpandedCorruptionClosure
