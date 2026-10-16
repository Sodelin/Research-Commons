import Semi.Diffraction.CyclicGrid
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Ring

/-!
Counting-measure DFT and N^-2 intensity on a nonempty cyclic binary grid.
SOURCE CANDIDATE. Parseval is assembled from the actual pinned Mathlib DFT
inversion theorem; it is not introduced as an assumption or normalization by
an unspecified total power. No Poisson experiment is defined here.
-/

namespace Semi.Diffraction

open Finset
variable {N : ℕ} [NeZero N]

lemma conjugate_stdAddChar (t : ZMod N) :
    starRingEnd ℂ (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
    (ZMod.toCircle.map_neg_eq_inv t), Circle.coe_inv_eq_conj]

lemma conjugate_dft (f : ZMod N → ℂ) (k : ZMod N) :
    starRingEnd ℂ (ZMod.dft f k) =
      ZMod.dft (fun i => starRingEnd ℂ (f i)) (-k) := by
  simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul,
    conjugate_stdAddChar, mul_neg, neg_neg]

lemma dft_bilinear_swap (f g : ZMod N → ℂ) :
    (∑ k, ZMod.dft f k * g k) = ∑ i, f i * ZMod.dft g i := by
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm k i]
  ring

lemma dft_conjugate_dft (f : ZMod N → ℂ) (i : ZMod N) :
    ZMod.dft (fun k => starRingEnd ℂ (ZMod.dft f k)) i =
      (N : ℂ) * starRingEnd ℂ (f i) := by
  have h : (fun k => starRingEnd ℂ (ZMod.dft f k)) =
      (fun k => ZMod.dft (fun j => starRingEnd ℂ (f j)) (-k)) :=
    funext (conjugate_dft f)
  rw [h, ZMod.dft_comp_neg, ZMod.dft_dft]
  simp only [neg_neg, smul_eq_mul]

theorem dft_parseval_complex (f : ZMod N → ℂ) :
    (∑ k, ZMod.dft f k * starRingEnd ℂ (ZMod.dft f k)) =
      (N : ℂ) * ∑ i, f i * starRingEnd ℂ (f i) := by
  rw [dft_bilinear_swap]
  simp only [dft_conjugate_dft, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def amplitude (x : Configuration N) : Grid N → ℂ :=
  ZMod.dft (fun i => complexSpin (x i))

noncomputable def intensity (x : Configuration N) (k : Grid N) : ℝ :=
  Complex.normSq (amplitude x k) / (N : ℝ) ^ 2

theorem intensity_nonneg (x : Configuration N) (k : Grid N) :
    0 ≤ intensity x k := div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

theorem amplitude_total_power_complex (x : Configuration N) :
    (∑ k, amplitude x k * starRingEnd ℂ (amplitude x k)) = (N : ℂ) ^ 2 := by
  simpa only [amplitude, complexSpin_mul_conj, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, mul_one, pow_two] using
      dft_parseval_complex (fun i => complexSpin (x i))

theorem amplitude_total_power (x : Configuration N) :
    (∑ k, Complex.normSq (amplitude x k)) = (N : ℝ) ^ 2 := by
  have h := amplitude_total_power_complex x
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_natCast]
  simpa only [Complex.mul_conj] using h

theorem intensity_sum_one (x : Configuration N) : ∑ k, intensity x k = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [intensity, ← Finset.sum_div, amplitude_total_power]
  exact div_self (pow_ne_zero 2 hN)

lemma amplitude_translate (t : Grid N) (x : Configuration N) (k : Grid N) :
    amplitude (translate t x) k = ZMod.stdAddChar (t * k) * amplitude x k := by
  let f : Grid N → ℂ := fun j => ZMod.stdAddChar (-(j * k)) * complexSpin (x j)
  calc
    amplitude (translate t x) k =
        ∑ j, ZMod.stdAddChar (t * k) * f (shiftSite t j) := by
      change (∑ j, ZMod.stdAddChar (-(j * k)) * complexSpin (x (j + t))) = _
      apply Finset.sum_congr rfl
      intro j _
      change ZMod.stdAddChar (-(j * k)) * complexSpin (x (j + t)) =
        ZMod.stdAddChar (t * k) *
          (ZMod.stdAddChar (-((j + t) * k)) * complexSpin (x (j + t)))
      have he : t * k + -((j + t) * k) = -(j * k) := by ring
      rw [← mul_assoc, ← AddChar.map_add_eq_mul, he]
    _ = ZMod.stdAddChar (t * k) * ∑ j, f (shiftSite t j) := by rw [Finset.mul_sum]
    _ = ZMod.stdAddChar (t * k) * ∑ j, f j := by
      exact congrArg (fun z : ℂ => ZMod.stdAddChar (t * k) * z)
        (Fintype.sum_equiv (shiftSite t) (fun j => f (shiftSite t j)) f (fun _ => rfl))
    _ = ZMod.stdAddChar (t * k) * amplitude x k := by
      simp only [f, amplitude, ZMod.dft_apply, smul_eq_mul]

lemma amplitude_invert (x : Configuration N) (k : Grid N) :
    amplitude (invert x) k = starRingEnd ℂ (amplitude x k) := by
  have hc : (fun i => starRingEnd ℂ (complexSpin (x i))) =
      (fun i => complexSpin (x i)) := by funext i; simp
  change ZMod.dft (fun i => complexSpin (x (-i))) k =
    starRingEnd ℂ (ZMod.dft (fun i => complexSpin (x i)) k)
  rw [conjugate_dft, hc]
  exact congrFun (ZMod.dft_comp_neg (fun i => complexSpin (x i))) k

lemma amplitude_globalSign (x : Configuration N) (k : Grid N) :
    amplitude (globalSign x) k = -amplitude x k := by
  simp [amplitude, ZMod.dft_apply, globalSign, smul_eq_mul, Finset.sum_neg_distrib]

theorem intensity_translate (t : Grid N) (x : Configuration N) :
    intensity (translate t x) = intensity x := by
  funext k
  simp [intensity, amplitude_translate, Complex.normSq_mul, ZMod.stdAddChar_apply]

theorem intensity_invert (x : Configuration N) : intensity (invert x) = intensity x := by
  funext k
  simp [intensity, amplitude_invert]

theorem intensity_globalSign (x : Configuration N) :
    intensity (globalSign x) = intensity x := by
  funext k
  simp [intensity, amplitude_globalSign]

def intensityStabilizer (N : ℕ) [NeZero N] : Subgroup (Equiv.Perm (Configuration N)) where
  carrier := {g | ∀ x, intensity (g x) = intensity x}
  one_mem' := by intro x; rfl
  mul_mem' := by intro g h hg hh x; exact (hg (h x)).trans (hh x)
  inv_mem' := by intro g hg x; simpa using (hg (g⁻¹ x)).symm

theorem intensity_symmetry (g : symmetries N) (x : Configuration N) :
    intensity (g.1 x) = intensity x := by
  have hsub : symmetries N ≤ intensityStabilizer N := by
    apply (Subgroup.closure_le (K := intensityStabilizer N)).mpr
    intro g hg
    rcases hg with ⟨t, rfl⟩ | rfl | rfl
    · exact intensity_translate t
    · exact intensity_invert
    · exact intensity_globalSign
  exact hsub g.2 x

end Semi.Diffraction
