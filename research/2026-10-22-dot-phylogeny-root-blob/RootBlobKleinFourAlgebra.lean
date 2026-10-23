import RootBlobReversiblePaths

/-!
# Literal Klein-four transition algebra

Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY; no execution or formal-verification claim.
Mathlib source baseline: 0df444a360eaa60ab8c11dca51a86af692955474.

The original NucleotideTransition predicates are used unchanged: entries
may vanish; all three nontrivial Fourier eigenvalues lie strictly in (0,1).
In particular strict entry positivity is proved for a PRODUCT of two such
matrices, not assumed for each edge or inferred from a different open model.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobReversiblePaths
namespace RootBlobKleinFourAlgebra

def g1 : DNA := (1, 0)
def g2 : DNA := (0, 1)
def g3 : DNA := (1, 1)

theorem sum_four (f : DNA → ℝ) :
    (∑ x, f x) = f 0 + f g1 + f g2 + f g3 := by
  classical
  have hu : (Finset.univ : Finset DNA) = {0, g1, g2, g3} := by decide
  rw [hu]
  simp [g1, g2, g3]
  <;> ring

theorem dna_cases (x : DNA) : x = 0 ∨ x = g1 ∨ x = g2 ∨ x = g3 := by
  rcases x with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;> decide

theorem sub_symmetric (i j : DNA) : i - j = j - i := by
  rcases dna_cases i with rfl | rfl | rfl | rfl <;>
    rcases dna_cases j with rfl | rfl | rfl | rfl <;> decide

theorem shifted_sum (p : DNA → ℝ) (i : DNA) :
    (∑ j, p (j - i)) = ∑ j, p j := by
  rcases dna_cases i with rfl | rfl | rfl | rfl <;>
    simp only [sum_four] <;> norm_num [g1, g2, g3] <;> ring

theorem fourier_zero (p : DNA → ℝ) : fourier p 0 = ∑ x, p x := by
  simp [fourier, character]

theorem fourier_g1 (p : DNA → ℝ) :
    fourier p g1 = p 0 - p g1 + p g2 - p g3 := by
  rw [fourier, sum_four]
  norm_num [character, g1, g2, g3]
  ring

theorem fourier_g2 (p : DNA → ℝ) :
    fourier p g2 = p 0 + p g1 - p g2 - p g3 := by
  rw [fourier, sum_four]
  norm_num [character, g1, g2, g3]
  ring

theorem fourier_g3 (p : DNA → ℝ) :
    fourier p g3 = p 0 - p g1 - p g2 + p g3 := by
  rw [fourier, sum_four]
  norm_num [character, g1, g2, g3]
  ring

theorem fourier_inverse_zero (p : DNA → ℝ) (hp : (∑ x, p x) = 1) :
    p 0 = (1 + fourier p g1 + fourier p g2 + fourier p g3) / 4 := by
  rw [sum_four] at hp
  rw [fourier_g1, fourier_g2, fourier_g3]
  linarith

def kernel (p : DNA → ℝ) : Mat DNA := fun i j => p (j - i)

noncomputable def convolution (p q : DNA → ℝ) (z : DNA) : ℝ :=
  ∑ x, p x * q (z - x)

theorem kernel_mul (p q : DNA → ℝ) :
    matMul (kernel p) (kernel q) = kernel (convolution p q) := by
  funext i j
  rcases dna_cases i with rfl | rfl | rfl | rfl <;>
    rcases dna_cases j with rfl | rfl | rfl | rfl
  all_goals simp only [matMul, kernel, convolution, sum_four]
  all_goals norm_num [g1, g2, g3]
  all_goals ring

theorem convolution_total (p q : DNA → ℝ) :
    (∑ z, convolution p q z) = (∑ x, p x) * ∑ y, q y := by
  simp only [sum_four, convolution]
  simp only [sum_four]
  norm_num [g1, g2, g3]
  ring

theorem convolution_fourier (p q : DNA → ℝ) (g : DNA) :
    fourier (convolution p q) g = fourier p g * fourier q g := by
  rcases dna_cases g with rfl | rfl | rfl | rfl
  all_goals simp only [fourier, convolution, sum_four]
  all_goals norm_num [character, g1, g2, g3]
  all_goals ring

theorem nucleotide_nonnegative {m : NucleotideModel} {M : Mat DNA}
    (hM : NucleotideTransition m M) : ∀ i j, 0 ≤ M i j := by
  rcases hM with ⟨p, hp, hform, hλ, hmodel⟩
  intro i j
  rw [hform]
  exact hp.1 _

theorem nucleotide_rows {m : NucleotideModel} {M : Mat DNA}
    (hM : NucleotideTransition m M) : RowNormalized M := by
  rcases hM with ⟨p, hp, hform, hλ, hmodel⟩
  intro i
  simp_rw [hform]
  rw [shifted_sum, hp.2]

theorem nucleotide_symmetric {m : NucleotideModel} {M : Mat DNA}
    (hM : NucleotideTransition m M) : ∀ i j, M i j = M j i := by
  rcases hM with ⟨p, hp, hform, hλ, hmodel⟩
  intro i j
  rw [hform, hform, sub_symmetric]

theorem nucleotide_reversible {m : NucleotideModel} {M : Mat DNA}
    (hM : NucleotideTransition m M) : Reversible (fun _ => (1 : ℝ) / 4) M := by
  intro i j
  rw [nucleotide_symmetric hM i j]

theorem nucleotide_eigen {m : NucleotideModel} {M : Mat DNA}
    (hM : NucleotideTransition m M) (g : DNA) (hg : g ≠ 0) :
    0 < eigen M g ∧ eigen M g < 1 := by
  rcases hM with ⟨p, hp, hform, hλ, hmodel⟩
  simpa [eigen, hform] using hλ g hg

theorem nucleotide_mul {m : NucleotideModel} {A B : Mat DNA}
    (hA : NucleotideTransition m A) (hB : NucleotideTransition m B) :
    NucleotideTransition m (matMul A B) := by
  rcases hA with ⟨p, hp, hAp, hpλ, hpm⟩
  rcases hB with ⟨q, hq, hBq, hqλ, hqm⟩
  have hAf : A = kernel p := funext fun i => funext (hAp i)
  have hBf : B = kernel q := funext fun i => funext (hBq i)
  refine ⟨convolution p q, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro z
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp.1 x) (hq.1 _))
  · rw [convolution_total, hp.2, hq.2, one_mul]
  · rw [hAf, hBf, kernel_mul]
    intro i j; rfl
  · intro g hg
    rw [convolution_fourier]
    have hp' := hpλ g hg
    have hq' := hqλ g hg
    constructor
    · exact mul_pos hp'.1 hq'.1
    · nlinarith [mul_pos (sub_pos.mpr hp'.2) hq'.1]
  · cases m with
    | jc =>
      intro g hg
      rw [convolution_fourier, convolution_fourier, hpm g hg, hqm g hg]
    | k2p =>
      change fourier (convolution p q) g1 = fourier (convolution p q) g2
      rw [convolution_fourier, convolution_fourier]
      change fourier p g1 = fourier p g2 at hpm
      change fourier q g1 = fourier q g2 at hqm
      rw [hpm, hqm]
    | k3p => trivial

theorem eigen_mul {A B : Mat DNA} {m : NucleotideModel}
    (hA : NucleotideTransition m A) (hB : NucleotideTransition m B) (g : DNA) :
    eigen (matMul A B) g = eigen A g * eigen B g := by
  rcases hA with ⟨p, hp, hAp, hpλ, hpm⟩
  rcases hB with ⟨q, hq, hBq, hqλ, hqm⟩
  have hAf : A = kernel p := funext fun i => funext (hAp i)
  have hBf : B = kernel q := funext fun i => funext (hBq i)
  rw [hAf, hBf, kernel_mul]
  simpa [eigen, kernel] using convolution_fourier p q g

/-- Exact coordinate version of the support-at-least-three lemma: identity
mass is positive and each pair of nonidentity masses has positive total.
Hence at most one entry can vanish. This uses ALL three strict eigenvalues. -/
theorem support_constraints (p : DNA → ℝ) (hp : Probability p)
    (hλ : ∀ g, g ≠ 0 → 0 < fourier p g ∧ fourier p g < 1) :
    0 < p 0 ∧ 0 < p g1 + p g2 ∧ 0 < p g1 + p g3 ∧ 0 < p g2 + p g3 := by
  have h1 := hλ g1 (by decide)
  have h2 := hλ g2 (by decide)
  have h3 := hλ g3 (by decide)
  have hi := fourier_inverse_zero p hp.2
  have ht := hp.2
  rw [sum_four] at ht
  rw [fourier_g1] at h1
  rw [fourier_g2] at h2
  rw [fourier_g3] at h3
  rw [fourier_g1, fourier_g2, fourier_g3] at hi
  constructor
  · linarith
  · exact ⟨by linarith, by linarith, by linarith⟩

theorem cross_sum_positive (p q r s a b c d : ℝ)
    (hp : 0 < p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hrs : 0 < r + s) (hbc : 0 < b + c) (hbd : 0 < b + d) :
    0 < p * b + q * a + r * d + s * c := by
  have hqa := mul_nonneg hq ha
  have hrd := mul_nonneg hr hd
  have hsc := mul_nonneg hs hc
  by_cases hbpos : 0 < b
  · have hpb := mul_pos hp hbpos
    linarith
  · have hbzero : b = 0 := le_antisymm (le_of_not_gt hbpos) hb
    have hcpos : 0 < c := by linarith
    have hdpos : 0 < d := by linarith
    by_cases hrpos : 0 < r
    · have hrdpos := mul_pos hrpos hdpos
      have hpb := mul_nonneg (le_of_lt hp) hb
      linarith
    · have hspos : 0 < s := by linarith
      have hscpos := mul_pos hspos hcpos
      have hpb := mul_nonneg (le_of_lt hp) hb
      linarith

theorem convolution_positive (p q : DNA → ℝ) (hp : Probability p) (hq : Probability q)
    (hpλ : ∀ g, g ≠ 0 → 0 < fourier p g ∧ fourier p g < 1)
    (hqλ : ∀ g, g ≠ 0 → 0 < fourier q g ∧ fourier q g < 1) :
    ∀ z, 0 < convolution p q z := by
  obtain ⟨hp0, hp12, hp13, hp23⟩ := support_constraints p hp hpλ
  obtain ⟨hq0, hq12, hq13, hq23⟩ := support_constraints q hq hqλ
  intro z
  rcases dna_cases z with rfl | rfl | rfl | rfl
  · have ht := mul_pos hp0 hq0
    have h1 := mul_nonneg (hp.1 g1) (hq.1 g1)
    have h2 := mul_nonneg (hp.1 g2) (hq.1 g2)
    have h3 := mul_nonneg (hp.1 g3) (hq.1 g3)
    simp only [convolution, sum_four]
    norm_num [g1, g2, g3] at *
    linarith
  · have h := cross_sum_positive (p 0) (p g1) (p g2) (p g3)
      (q 0) (q g1) (q g2) (q g3) hp0 (hp.1 _) (hp.1 _) (hp.1 _)
      (hq.1 _) (hq.1 _) (hq.1 _) (hq.1 _) hp23 hq12 hq13
    simpa [convolution, sum_four, g1, g2, g3] using h
  · have h := cross_sum_positive (p 0) (p g2) (p g1) (p g3)
      (q 0) (q g2) (q g1) (q g3) hp0 (hp.1 _) (hp.1 _) (hp.1 _)
      (hq.1 _) (hq.1 _) (hq.1 _) (hq.1 _) hp13 (by linarith) hq23
    convert h using 1 <;> simp [convolution, sum_four, g1, g2, g3] <;> ring
  · have h := cross_sum_positive (p 0) (p g3) (p g1) (p g2)
      (q 0) (q g3) (q g1) (q g2) hp0 (hp.1 _) (hp.1 _) (hp.1 _)
      (hq.1 _) (hq.1 _) (hq.1 _) (hq.1 _) hp12 (by linarith) (by linarith)
    convert h using 1 <;> simp [convolution, sum_four, g1, g2, g3] <;> ring

theorem nucleotide_two_positive {m : NucleotideModel} {A B : Mat DNA}
    (hA : NucleotideTransition m A) (hB : NucleotideTransition m B) :
    PositiveMatrix (matMul A B) := by
  rcases hA with ⟨p, hp, hAp, hpλ, hpm⟩
  rcases hB with ⟨q, hq, hBq, hqλ, hqm⟩
  have hAf : A = kernel p := funext fun i => funext (hAp i)
  have hBf : B = kernel q := funext fun i => funext (hBq i)
  rw [hAf, hBf, kernel_mul]
  intro i j
  exact convolution_positive p q hp hq hpλ hqλ (j - i)

theorem product_nucleotide {m : NucleotideModel} (L : List (Mat DNA))
    (hne : L ≠ []) (hL : ∀ A ∈ L, NucleotideTransition m A) :
    NucleotideTransition m (product L) := by
  revert hne hL
  induction L with
  | nil => intro hne hL; exact (hne rfl).elim
  | cons A L ih =>
    intro hne hL
    by_cases htail : L = []
    · subst L
      rw [product_singleton]
      exact hL A (by simp)
    · exact nucleotide_mul (hL A (by simp))
        (ih htail (fun B hB => hL B (by simp [hB])))

theorem product_two_positive {m : NucleotideModel} (L : List (Mat DNA))
    (hlen : 2 ≤ L.length) (hL : ∀ A ∈ L, NucleotideTransition m A) :
    PositiveMatrix (product L) := by
  cases L with
  | nil => simp at hlen
  | cons A L =>
    have hne : L ≠ [] := by intro he; simp [he] at hlen
    exact nucleotide_two_positive (hL A (by simp))
      (product_nucleotide L hne (fun B hB => hL B (by simp [hB])))

section Mixtures
variable {I : Type*} [Fintype I]

theorem weighted_strict_positive (w f : I → ℝ)
    (hw : ∀ r, 0 ≤ w r) (hwt : (∑ r, w r) = 1) (hf : ∀ r, 0 < f r) :
    0 < ∑ r, w r * f r := by
  classical
  have hex : ∃ r, 0 < w r := by
    by_contra h
    push_neg at h
    have hz : ∀ r, w r = 0 := fun r => le_antisymm (h r) (hw r)
    simp_rw [hz] at hwt
    simp at hwt
  obtain ⟨r, hr⟩ := hex
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg (hw s) (le_of_lt (hf s))
  · exact ⟨r, Finset.mem_univ r, mul_pos hr (hf r)⟩

theorem weighted_open_unit (w f : I → ℝ)
    (hw : ∀ r, 0 ≤ w r) (hwt : (∑ r, w r) = 1)
    (hf : ∀ r, 0 < f r ∧ f r < 1) :
    0 < ∑ r, w r * f r ∧ (∑ r, w r * f r) < 1 := by
  refine ⟨weighted_strict_positive w f hw hwt (fun r => (hf r).1), ?_⟩
  have h := weighted_strict_positive w (fun r => 1 - f r) hw hwt
    (fun r => sub_pos.mpr (hf r).2)
  have he : (∑ r, w r * (1 - f r)) = 1 - ∑ r, w r * f r := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hwt]
  rw [he] at h
  linarith

noncomputable def mixture (w : I → ℝ) (M : I → Mat DNA) : Mat DNA :=
  fun i j => ∑ r, w r * M r i j

theorem fourier_mixture (w : I → ℝ) (p : I → DNA → ℝ) (g : DNA) :
    fourier (fun x => ∑ r, w r * p r x) g = ∑ r, w r * fourier (p r) g := by
  unfold fourier
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem eigen_mixture (w : I → ℝ) (M : I → Mat DNA) (g : DNA) :
    eigen (mixture w M) g = ∑ r, w r * eigen (M r) g :=
  fourier_mixture w (fun r x => M r 0 x) g

theorem nucleotide_mixture {m : NucleotideModel} (w : I → ℝ) (M : I → Mat DNA)
    (hw : ∀ r, 0 ≤ w r) (hwt : (∑ r, w r) = 1)
    (hM : ∀ r, NucleotideTransition m (M r)) :
    NucleotideTransition m (mixture w M) := by
  classical
  choose p hp hform hλ hmodel using hM
  refine ⟨fun x => ∑ r, w r * p r x, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x
    exact Finset.sum_nonneg (fun r _ => mul_nonneg (hw r) ((hp r).1 x))
  · rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, fun r => (hp r).2, mul_one]
    exact hwt
  · intro i j
    simp only [mixture, hform]
  · intro g hg
    rw [fourier_mixture]
    exact weighted_open_unit w (fun r => fourier (p r) g) hw hwt (fun r => hλ r g hg)
  · cases m with
    | jc =>
      intro g hg
      simp_rw [fourier_mixture, fun r => hmodel r g hg]
    | k2p =>
      simp_rw [fourier_mixture, hmodel]
    | k3p => trivial

theorem mixture_positive_of_one {m : NucleotideModel}
    (w : I → ℝ) (M : I → Mat DNA) (hw : ∀ r, 0 ≤ w r)
    (hM : ∀ r, NucleotideTransition m (M r))
    (r : I) (hr : 0 < w r) (hpos : PositiveMatrix (M r)) :
    PositiveMatrix (mixture w M) := by
  intro i j
  apply Finset.sum_pos'
  · intro s _
    exact mul_nonneg (hw s) (nucleotide_nonnegative (hM s) i j)
  · exact ⟨r, Finset.mem_univ r, mul_pos hr (hpos i j)⟩

end Mixtures

noncomputable def raised (p : DNA → ℝ) (c : ℝ) : DNA → ℝ :=
  fun x => (p x - (1 - c) / 4) / c

theorem raised_total (p : DNA → ℝ) (hp : (∑ x, p x) = 1) {c : ℝ} (hc : c ≠ 0) :
    (∑ x, raised p c x) = 1 := by
  rw [sum_four] at hp ⊢
  unfold raised
  field_simp
  nlinarith

theorem raised_fourier (p : DNA → ℝ) (c : ℝ) (g : DNA) (hg : g ≠ 0) :
    fourier (raised p c) g = fourier p g / c := by
  rcases dna_cases g with h | rfl | rfl | rfl
  · exact (hg h).elim
  · rw [fourier_g1, fourier_g1]
    unfold raised
    ring
  · rw [fourier_g2, fourier_g2]
    unfold raised
    ring
  · rw [fourier_g3, fourier_g3]
    unfold raised
    ring

theorem nucleotide_compensate {m : NucleotideModel} {M : Mat DNA}
    (hM : NucleotideTransition m M) {c : ℝ} (hc : 0 < c)
    (hλ : ∀ g, g ≠ 0 → eigen M g < c)
    (hpos : ∀ i j, 0 < M i j - (1 - c) / 4) :
    NucleotideTransition m (RootBlobOpenProof.compensate M (fun _ => 1 / 4) c) := by
  rcases hM with ⟨p, hp, hform, hpλ, hmodel⟩
  have hλp : ∀ g, g ≠ 0 → fourier p g < c := by
    intro g hg
    simpa [eigen, hform] using hλ g hg
  have hpp : ∀ x, 0 < p x - (1 - c) / 4 := by
    intro x
    simpa [hform] using hpos 0 x
  refine ⟨raised p c, ⟨?_, raised_total p hp.2 (ne_of_gt hc)⟩, ?_, ?_, ?_⟩
  · intro x
    exact le_of_lt (div_pos (hpp x) hc)
  · intro i j
    simp [RootBlobOpenProof.compensate, raised, hform, div_eq_mul_inv]
  · intro g hg
    rw [raised_fourier p c g hg]
    exact ⟨div_pos (hpλ g hg).1 hc, (div_lt_one hc).mpr (hλp g hg)⟩
  · cases m with
    | jc =>
      intro g hg
      rw [raised_fourier p c g hg, raised_fourier p c (1, 0) (by decide), hmodel g hg]
    | k2p =>
      rw [raised_fourier p c (1, 0) (by decide),
        raised_fourier p c (0, 1) (by decide), hmodel]
    | k3p => trivial

def uniform : DNA → ℝ := fun _ => 1 / 4

theorem uniform_total : (∑ i, uniform i) = 1 := by
  rw [sum_four]
  norm_num [uniform]

theorem equalInput_nucleotide (m : NucleotideModel) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    NucleotideTransition m (RootBlobOpenProof.equalInput uniform t) := by
  classical
  let p : DNA → ℝ := fun x => if x = 0 then t + (1 - t) / 4 else (1 - t) / 4
  have hp : Probability p := by
    constructor
    · intro x
      dsimp [p]
      split_ifs <;> linarith
    · rw [sum_four]
      norm_num [p, g1, g2, g3]
      ring
  have hλ : ∀ g, g ≠ 0 → fourier p g = t := by
    intro g hg
    rcases dna_cases g with h | rfl | rfl | rfl
    · exact (hg h).elim
    all_goals simp only [fourier, sum_four]
    all_goals norm_num [p, character, g1, g2, g3]
    all_goals ring
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · intro i j
    by_cases he : i = j
    · subst j
      simp [RootBlobOpenProof.equalInput, uniform, p]
    · have hn : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
      simp [RootBlobOpenProof.equalInput, uniform, p, he, hn, div_eq_mul_inv]
  · intro g hg
    rw [hλ g hg]
    exact ⟨ht0, ht1⟩
  · cases m with
    | jc =>
      intro g hg
      rw [hλ g hg, hλ (1, 0) (by decide)]
    | k2p => rw [hλ (1, 0) (by decide), hλ (0, 1) (by decide)]
    | k3p => trivial

end RootBlobKleinFourAlgebra

end RootBlobKleinFourAlgebra
