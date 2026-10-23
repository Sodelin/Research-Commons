import RootBlobKleinFourAlgebra
import RootBlobRetainedAdmission

/-!
# Exact literal nucleotide retained-port image

Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No compiler or scientific runtime was run.

The root is FIXED UNIFORM. Every old edge satisfies the original literal
JC/K2P/K3P predicate, which allows zero entries. The forward path mixture is
derived from the actual DAG state sum and a shared original assignment.
The reverse construction uses one common reset parameter, the old fixed W,
and a terminal compensation on every incoming edge of the first port.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof RootBlobReversiblePaths
open RootBlobKleinFourAlgebra RootBlobRetainedPortSemantics
namespace RootBlobNucleotideRetainedImage
universe v w

/-- One exact parameter below one satisfies ALL finite spectral and entry
constraints. The extra lower bound is retained for the separate CT-K2P join.
Neither a limit point nor an all-positive-exponents premise is substituted. -/
theorem exists_nucleotide_parameter {I : Type*} [Fintype I]
    (w : I → ℝ) (k : I → ℕ) (hwt : (∑ r, w r) = 1)
    {m : NucleotideModel} {M : Mat DNA} (hM : NucleotideTransition m M)
    (hpos : PositiveMatrix M) (lower : ℝ) (hlower : lower < 1) :
    ∃ t, 0 < t ∧ t < 1 ∧ lower < coefficient w k t ∧
      0 < coefficient w k t ∧
      (∀ g, g ≠ 0 → eigen M g < coefficient w k t) ∧
      ∀ i j, 0 < M i j - (1 - coefficient w k t) / 4 := by
  have hc := coefficient_continuous w k
  have hc1 := coefficient_one k hwt
  have he0 : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < coefficient w k t := by
    apply hc.continuousAt.eventually
    exact isOpen_Ioi.mem_nhds (by rw [hc1]; norm_num)
  have helow : ∀ᶠ t in 𝓝 (1 : ℝ), lower < coefficient w k t := by
    apply hc.continuousAt.eventually
    exact isOpen_Ioi.mem_nhds (by simpa [hc1] using hlower)
  have helambda : ∀ g, ∀ᶠ t in 𝓝 (1 : ℝ), g ≠ 0 → eigen M g < coefficient w k t := by
    intro g
    by_cases hg : g = 0
    · exact Filter.Eventually.of_forall (by intro t h; exact (h hg).elim)
    · have he : ∀ᶠ t in 𝓝 (1 : ℝ), eigen M g < coefficient w k t := by
        apply hc.continuousAt.eventually
        exact isOpen_Ioi.mem_nhds (by simpa [hc1] using (nucleotide_eigen hM g hg).2)
      exact he.mono (fun t ht _ => ht)
  have hepos : ∀ i j, ∀ᶠ t in 𝓝 (1 : ℝ),
      0 < M i j - (1 - coefficient w k t) / 4 := by
    intro i j
    have hf : Continuous (fun t : ℝ => M i j - (1 - coefficient w k t) / 4) := by fun_prop
    apply hf.continuousAt.eventually
    apply isOpen_Ioi.mem_nhds
    simpa [hc1] using hpos i j
  have halllambda := Filter.eventually_all.mpr helambda
  have hallpos : ∀ᶠ t in 𝓝 (1 : ℝ), ∀ i j,
      0 < M i j - (1 - coefficient w k t) / 4 :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hepos i))
  exact exists_left_of_eventually (helow.and (he0.and (halllambda.and hallpos)))

theorem uniform_stationary {m : NucleotideModel} {M : Mat DNA}
    (hM : NucleotideTransition m M) : rowAction uniform M = uniform := by
  funext j
  exact stationary_of_reversible uniform M (nucleotide_rows hM) (nucleotide_reversible hM) j

theorem compensation_pair {m : NucleotideModel} {M : Mat DNA}
    (hM : NucleotideTransition m M) {c : ℝ} (hc : c ≠ 0) :
    blendPair uniform c (compensate M uniform c) = fun i j => M i j / 4 := by
  have hst := uniform_stationary hM
  have hh := compensate_blend (μ := uniform) (M := M) uniform_total hc
  rw [hst] at hh
  rw [hh]
  funext i j
  rw [nucleotide_symmetric hM j i]
  simp [uniform, div_eq_mul_inv, mul_comm]

variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2))

noncomputable def effectiveImage (W : E → ℝ) (T : Mat DNA → Prop) : Set (Mat DNA) :=
  {K | ∃ M : E → Mat DNA, (∀ e, T (M e)) ∧
    RootBlobEdgeIndexed.pairLaw N uniform W M = fun i j => K i j / 4}

theorem nucleotide_realize (hN : PortAdmitted N) (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    {m : NucleotideModel} {K : Mat DNA}
    (hK : NucleotideTransition m K) (hpos : PositiveMatrix K) :
    K ∈ effectiveImage N W (NucleotideTransition m) := by
  classical
  let w := RootBlobSwitching.weight N W
  let k := pathExponent (S := DNA) N hN
  obtain ⟨t, ht0, ht1, _, hc0, hcλ, hcpos⟩ := exists_nucleotide_parameter
    w k (RootBlobSwitching.weight_total N W hW) hK hpos 0 (by norm_num)
  let c := coefficient w k t
  let A := compensate K uniform c
  have hA : NucleotideTransition m A :=
    nucleotide_compensate hK hc0 hcλ hcpos
  let M := RootBlobOpenProof.Edge.terminalAssignment N A (equalInput uniform t)
  refine ⟨M, ?_, ?_⟩
  · intro e
    dsimp [M, RootBlobOpenProof.Edge.terminalAssignment]
    split_ifs
    · exact hA
    · exact equalInput_nucleotide m ht0 ht1
  · rw [pair_formula N hN W hW uniform uniform_total t A]
    exact compensation_pair hK (ne_of_gt hc0)

noncomputable def pathKernel (hN : PortAdmitted N) (M : E → Mat DNA)
    (σ : RootBlobSwitching.Switching N) : Mat DNA :=
  product ((RootBlobReversiblePaths.Network.portEdges (S := DNA) N hN σ).map M)

theorem pathKernel_nucleotide (hN : PortAdmitted N) {m : NucleotideModel}
    (M : E → Mat DNA) (hM : ∀ e, NucleotideTransition m (M e))
    (σ : RootBlobSwitching.Switching N) : NucleotideTransition m (pathKernel N hN M σ) := by
  apply product_nucleotide
  · simpa using RootBlobReversiblePaths.Network.portEdges_nonempty (S := DNA) N hN σ
  · intro A hA
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hA
    exact hM e

theorem pathKernel_positive (hN : PortAdmitted N) {m : NucleotideModel}
    (M : E → Mat DNA) (hM : ∀ e, NucleotideTransition m (M e))
    (σ : RootBlobSwitching.Switching N)
    (hlen : 2 ≤ (RootBlobReversiblePaths.Network.portEdges (S := DNA) N hN σ).length) :
    PositiveMatrix (pathKernel N hN M σ) := by
  apply product_two_positive
  · simpa using hlen
  · intro A hA
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hA
    exact hM e

theorem nucleotide_sound (hN : PortAdmitted N) (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hlong : ∃ σ : RootBlobSwitching.Switching N,
      2 ≤ (RootBlobReversiblePaths.Network.portEdges (S := DNA) N hN σ).length)
    {m : NucleotideModel} {K : Mat DNA}
    (hK : K ∈ effectiveImage N W (NucleotideTransition m)) :
    NucleotideTransition m K ∧ PositiveMatrix K := by
  classical
  obtain ⟨M, hM, heq⟩ := hK
  let w := RootBlobSwitching.weight N W
  let P := pathKernel N hN M
  have hP : ∀ σ, NucleotideTransition m (P σ) := pathKernel_nucleotide N hN M hM
  have hw : ∀ σ, 0 ≤ w σ := fun σ => le_of_lt (RootBlobSwitching.weight_positive N W hW σ)
  have hwt : (∑ σ, w σ) = 1 := RootBlobSwitching.weight_total N W hW
  have hmix : K = mixture w P := by
    have h := RootBlobReversiblePaths.Network.pairLaw_path_mixture N hN W uniform M
      (fun e => nucleotide_rows (hM e)) (fun e => nucleotide_reversible (hM e))
    rw [heq] at h
    funext i j
    have hij := congrFun (congrFun h i) j
    change K i j / 4 = (1 / 4 : ℝ) * mixture w P i j at hij
    linarith
  rw [hmix]
  obtain ⟨σ, hσ⟩ := hlong
  exact ⟨nucleotide_mixture w P hw hwt hP,
    mixture_positive_of_one w P hw hP σ (RootBlobSwitching.weight_positive N W hW σ)
      (pathKernel_positive N hN M hM σ hσ)⟩

theorem nucleotide_image (hN : PortAdmitted N) (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hlong : ∃ σ : RootBlobSwitching.Switching N,
      2 ≤ (RootBlobReversiblePaths.Network.portEdges (S := DNA) N hN σ).length)
    (m : NucleotideModel) :
    effectiveImage N W (NucleotideTransition m) =
      {K | NucleotideTransition m K ∧ PositiveMatrix K} := by
  ext K
  constructor
  · exact nucleotide_sound N hN W hW hlong
  · rintro ⟨hK, hp⟩
    exact nucleotide_realize N hN W hW hK hp

end RootBlobNucleotideRetainedImage
