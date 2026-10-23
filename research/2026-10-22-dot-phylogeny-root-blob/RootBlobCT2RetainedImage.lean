import RootBlobRestrictedRetainedEndpoint

/-!
# Strict CT-K2P spectral-cone retained-port join

Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No compiler, runtime or kernel verification.

CT2Strict is the ORIGINAL interface predicate: literal K2P plus x^2 < y.
This module proves exact pair/full-image equality in that cone. The separate
RootBlobCT2GeneratorBridge module supplies source proof terms identifying it
with the exponential of an independently parameterized positive-rate K2P
generator. That analytic dependency is not hidden by the name CT2Strict, and
it remains just as unelaborated as the present source.

No CT-K3P mixture closure and no zero-rate boundary equality is asserted.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof RootBlobReversiblePaths
open RootBlobKleinFourAlgebra RootBlobRetainedPortSemantics
open RootBlobNucleotideRetainedImage RootBlobRestrictedRetainedEndpoint
namespace RootBlobCT2RetainedImage

theorem ct2_positive {M : Mat DNA} (hM : CT2Strict M) : PositiveMatrix M := by
  rcases hM with ⟨⟨p, hp, hform, hλ, hmodel⟩, hcone⟩
  have h1 := hλ g1 (by decide)
  have h2 := hλ g2 (by decide)
  have h3 := hλ g3 (by decide)
  have he : fourier p g1 = fourier p g2 := hmodel
  have hc : (fourier p g1)^2 < fourier p g3 := by
    simpa [eigen, hform, g1, g3] using hcone
  have ht := hp.2
  rw [sum_four] at ht
  have hp0 := fourier_inverse_zero p hp.2
  have hp1 : p g1 = (1 - fourier p g1 + fourier p g2 - fourier p g3) / 4 := by
    rw [fourier_g1, fourier_g2, fourier_g3]
    linarith
  have hp2 : p g2 = (1 + fourier p g1 - fourier p g2 - fourier p g3) / 4 := by
    rw [fourier_g1, fourier_g2, fourier_g3]
    linarith
  have hp3 : p g3 = (1 - fourier p g1 - fourier p g2 + fourier p g3) / 4 := by
    rw [fourier_g1, fourier_g2, fourier_g3]
    linarith
  intro i j
  rw [hform]
  rcases dna_cases (j - i) with hz | hz | hz | hz
  · rw [hz, hp0]
    linarith
  · rw [hz, hp1]
    linarith
  · rw [hz, hp2]
    linarith
  · rw [hz, hp3]
    nlinarith [sq_nonneg (1 - fourier p g1)]

theorem ct2_mul {A B : Mat DNA} (hA : CT2Strict A) (hB : CT2Strict B) :
    CT2Strict (matMul A B) := by
  refine ⟨nucleotide_mul hA.1 hB.1, ?_⟩
  rw [eigen_mul hA.1 hB.1, eigen_mul hA.1 hB.1]
  have hyB := (nucleotide_eigen hB.1 (1, 1) (by decide)).1
  have hxA := (nucleotide_eigen hA.1 (1, 0) (by decide)).1
  have hleft := mul_lt_mul_of_pos_right hA.2 hyB
  have hright := mul_lt_mul_of_pos_left hB.2 (sq_pos_of_pos hxA)
  nlinarith

theorem product_ct2 (L : List (Mat DNA)) (hne : L ≠ [])
    (hL : ∀ A ∈ L, CT2Strict A) : CT2Strict (product L) := by
  revert hne hL
  induction L with
  | nil => intro hne hL; exact (hne rfl).elim
  | cons A L ih =>
    intro hne hL
    by_cases htail : L = []
    · subst L
      rw [product_singleton]
      exact hL A (by simp)
    · exact ct2_mul (hL A (by simp)) (ih htail (fun B hB => hL B (by simp [hB])))

theorem weighted_square_le {I : Type*} [Fintype I]
    (w x : I → ℝ) (hw : ∀ r, 0 ≤ w r) (hwt : (∑ r, w r) = 1) :
    (∑ r, w r * x r)^2 ≤ ∑ r, w r * (x r)^2 := by
  let a := ∑ r, w r * x r
  have hn : 0 ≤ ∑ r, w r * (x r - a)^2 :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (hw r) (sq_nonneg _))
  have he : (∑ r, w r * (x r - a)^2) = (∑ r, w r * (x r)^2) - a^2 := by
    calc
      (∑ r, w r * (x r - a)^2) =
          ∑ r, (w r * (x r)^2 - 2 * a * (w r * x r) + a^2 * w r) := by
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = (∑ r, w r * (x r)^2) - 2 * a * (∑ r, w r * x r) + a^2 * (∑ r, w r) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [hwt]; change _ - 2 * a * a + a^2 * 1 = _; ring
  rw [he] at hn
  change a^2 ≤ _
  linarith

theorem ct2_mixture {I : Type*} [Fintype I] (w : I → ℝ) (M : I → Mat DNA)
    (hw : ∀ r, 0 ≤ w r) (hwt : (∑ r, w r) = 1) (hM : ∀ r, CT2Strict (M r)) :
    CT2Strict (mixture w M) := by
  refine ⟨nucleotide_mixture w M hw hwt (fun r => (hM r).1), ?_⟩
  rw [eigen_mixture, eigen_mixture]
  have hv := weighted_square_le w (fun r => eigen (M r) (1, 0)) hw hwt
  have hs := weighted_strict_positive w
    (fun r => eigen (M r) (1, 1) - eigen (M r) (1, 0)^2) hw hwt
    (fun r => sub_pos.mpr (hM r).2)
  have he : (∑ r, w r * (eigen (M r) (1, 1) - eigen (M r) (1, 0)^2)) =
      (∑ r, w r * eigen (M r) (1, 1)) - ∑ r, w r * eigen (M r) (1, 0)^2 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [he] at hs
  linarith

theorem eigen_compensate (M : Mat DNA) (c : ℝ) (g : DNA) (hg : g ≠ 0) :
    eigen (compensate M uniform c) g = eigen M g / c := by
  have h := raised_fourier (fun x => M 0 x) c g hg
  simpa [eigen, compensate, uniform, raised, div_eq_mul_inv] using h

theorem ct2_compensate {M : Mat DNA} (hM : CT2Strict M) {c : ℝ} (hc : 0 < c)
    (hλ : ∀ g, g ≠ 0 → eigen M g < c)
    (hpos : ∀ i j, 0 < M i j - (1 - c) / 4)
    (hbound : eigen M (1, 0)^2 / eigen M (1, 1) < c) :
    CT2Strict (compensate M uniform c) := by
  refine ⟨nucleotide_compensate hM.1 hc hλ hpos, ?_⟩
  rw [eigen_compensate _ _ (1, 0) (by decide), eigen_compensate _ _ (1, 1) (by decide)]
  have hy := (nucleotide_eigen hM.1 (1, 1) (by decide)).1
  have hnum := (div_lt_iff₀ hy).mp hbound
  rw [div_pow]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hc) hc).mpr
  nlinarith [mul_pos hc (sub_pos.mpr hnum)]

theorem equalInput_eigen (t : ℝ) (g : DNA) (hg : g ≠ 0) :
    eigen (equalInput uniform t) g = t := by
  rcases dna_cases g with h | rfl | rfl | rfl
  · exact (hg h).elim
  all_goals simp only [eigen, fourier, sum_four]
  all_goals norm_num [equalInput, uniform, character, g1, g2, g3]
  all_goals ring

theorem equalInput_ct2 {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    CT2Strict (equalInput uniform t) := by
  refine ⟨equalInput_nucleotide .k2p ht0 ht1, ?_⟩
  rw [equalInput_eigen _ (1, 0) (by decide), equalInput_eigen _ (1, 1) (by decide)]
  nlinarith [mul_pos ht0 (sub_pos.mpr ht1)]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2))

theorem ct2_realize (hN : PortAdmitted N) (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W) {K : Mat DNA} (hK : CT2Strict K) :
    K ∈ RootBlobNucleotideRetainedImage.effectiveImage N W CT2Strict := by
  classical
  let w := RootBlobSwitching.weight N W
  let k := pathExponent (S := DNA) N hN
  have hy := (nucleotide_eigen hK.1 (1, 1) (by decide)).1
  have hlower : eigen K (1, 0)^2 / eigen K (1, 1) < 1 := (div_lt_one hy).mpr hK.2
  obtain ⟨t, ht0, ht1, hbound, hc0, hcλ, hcpos⟩ := exists_nucleotide_parameter
    w k (RootBlobSwitching.weight_total N W hW) hK.1 (ct2_positive hK)
    (eigen K (1, 0)^2 / eigen K (1, 1)) hlower
  let c := coefficient w k t
  let A := compensate K uniform c
  have hA : CT2Strict A := ct2_compensate hK hc0 hcλ hcpos hbound
  let M := RootBlobOpenProof.Edge.terminalAssignment N A (equalInput uniform t)
  refine ⟨M, ?_, ?_⟩
  · intro e
    dsimp [M, RootBlobOpenProof.Edge.terminalAssignment]
    split_ifs
    · exact hA
    · exact equalInput_ct2 ht0 ht1
  · rw [pair_formula N hN W hW uniform uniform_total t A]
    exact compensation_pair hK.1 (ne_of_gt hc0)

theorem ct2_sound (hN : PortAdmitted N) (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W) {K : Mat DNA}
    (hK : K ∈ RootBlobNucleotideRetainedImage.effectiveImage N W CT2Strict) : CT2Strict K := by
  classical
  obtain ⟨M, hM, heq⟩ := hK
  let w := RootBlobSwitching.weight N W
  let P := pathKernel N hN M
  have hP : ∀ σ, CT2Strict (P σ) := by
    intro σ
    apply product_ct2
    · simpa using RootBlobReversiblePaths.Network.portEdges_nonempty (S := DNA) N hN σ
    · intro A hA
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hA
      exact hM e
  have hmix : K = mixture w P := by
    have h := RootBlobReversiblePaths.Network.pairLaw_path_mixture N hN W uniform M
      (fun e => nucleotide_rows (hM e).1) (fun e => nucleotide_reversible (hM e).1)
    rw [heq] at h
    funext i j
    have hij := congrFun (congrFun h i) j
    change K i j / 4 = (1 / 4 : ℝ) * mixture w P i j at hij
    linarith
  rw [hmix]
  exact ct2_mixture w P (fun σ => le_of_lt (RootBlobSwitching.weight_positive N W hW σ))
    (RootBlobSwitching.weight_total N W hW) hP

theorem ct2_image (hN : PortAdmitted N) (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W) :
    RootBlobNucleotideRetainedImage.effectiveImage N W CT2Strict = {K | CT2Strict K} := by
  ext K
  exact ⟨ct2_sound N hN W hW, ct2_realize N hN W hW⟩

section MaximalSource
open RootBlobEdgeIndexed RootBlobBoundaryGraph RootBlobMaximalSource RootBlobBinaryReplacement
open RootBlobRetainedPortGraph RootBlobRetainedPortModel RootBlobRetainedMaximal
open RootBlobRetainedAdmission
variable [DecidableEq E]
variable {O : Type*} [Fintype O]
variable {G : RootBlobEdgeIndexed.Network V E O}

/-- Full fixed-exterior endpoint for the ORIGINAL CT2Strict spectral cone.
The explicit analytic identification with positive generator rates remains
separate; no CT-K3P or zero-rate boundary result is inferred from this. -/
theorem maximal_ct2_fixed_exterior_admitted
    (B : MaximalRootTwoBlob G) (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    (hNP : NoParallel G) (hLSA : RootLSA G)
    (W : E → ℝ) (hW : WeightsAdmitted G W)
    (MX : (B.component hG hB).OuterEdge → Mat DNA) (_hMX : ∀ e, CT2Strict (MX e)) :
    let R := B.component hG hB
    GraphAdmitted (R.retainedFork hG) ∧ NoParallel (R.retainedFork hG) ∧
    RootLSA (R.retainedFork hG) ∧
    WeightsAdmitted (R.retainedFork hG) (R.retainedWeights W) ∧
    RootBlobRestrictedRetainedEndpoint.fixedImage R W MX CT2Strict =
      RootBlobRestrictedRetainedEndpoint.retainedImage R hG W MX CT2Strict := by
  let R := B.component hG hB
  have hI := ct2_image R.interior (R.interior_admitted hG)
    (R.insideWeights W) (R.insideWeights_admitted hG W hW)
  have hF := ct2_image RootBlobEdgeIndexed.rootedFork
    (portAdmitted_of_graph _ RootBlobTreeMarginals.rootedFork_graph)
    RootBlobEdgeIndexed.forkWeights RootBlobTreeMarginals.rootedFork_weights
  refine ⟨R.retainedFork_admitted hG, R.retainedFork_noParallel hG hNP,
    R.retainedFork_rootLSA hG hLSA, R.retainedWeights_admitted hG W hW, ?_⟩
  exact R.fixed_eq_retained_of_pairImage hG W MX CT2Strict (hI.trans hF.symm)

end MaximalSource

end RootBlobCT2RetainedImage
