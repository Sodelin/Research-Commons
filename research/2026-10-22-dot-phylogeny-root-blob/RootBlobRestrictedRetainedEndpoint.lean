import RootBlobNucleotideRetainedImage

/-!
# Restricted-domain fixed-exterior source-to-source endpoint

Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No body/transitive/kernel certification.

Both images below use the actual full-network observedLaw at a FIXED
uniform root. The source and target share the exact same MX on every
original outside-target edge, including both original cut-edge matrices.
The target retains degree-two ports and is not asserted binary. The original
source is binary, simple, root-LSA, with a maximal two-exit root blob.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobEdgeIndexed RootBlobCutFactorization
open RootBlobContextGlue RootBlobBoundaryGraph RootBlobMaximalSource
open RootBlobBinaryReplacement RootBlobRetainedPortGraph RootBlobRetainedPortModel
open RootBlobRetainedMaximal RootBlobRetainedAdmission
open RootBlobRetainedPortSemantics RootBlobKleinFourAlgebra
open RootBlobNucleotideRetainedImage
namespace RootBlobRestrictedRetainedEndpoint
universe v w x
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]
variable {G : Network V E O} (R : PortComponent G)

noncomputable def fixedImage (W : E → ℝ) (MX : R.OuterEdge → Mat DNA)
    (T : Mat DNA → Prop) : Set ((O → DNA) → ℝ) :=
  {L | ∃ MI : R.InnerEdge → Mat DNA, (∀ e, T (MI e)) ∧
    observedLaw G uniform W (R.assembledMatrices MI MX) = L}

noncomputable def retainedImage (hG : GraphAdmitted G) (W : E → ℝ)
    (MX : R.OuterEdge → Mat DNA) (T : Mat DNA → Prop) : Set ((O → DNA) → ℝ) :=
  {L | ∃ MF : Fin 2 → Mat DNA, (∀ e, T (MF e)) ∧
    observedLaw (R.retainedFork hG) uniform (R.retainedWeights W) (Sum.elim MF MX) = L}

/-- The definitions genuinely parameterize all original admissible points
with these prescribed exterior matrices, rather than just a subset. -/
theorem fixedImage_iff_original (W : E → ℝ) (MX : R.OuterEdge → Mat DNA)
    (T : Mat DNA → Prop) (hMX : ∀ e, T (MX e)) (L : (O → DNA) → ℝ) :
    L ∈ fixedImage R W MX T ↔
      ∃ M : E → Mat DNA, (∀ e, T (M e)) ∧
        (∀ e : R.OuterEdge, M e.val = MX e) ∧ observedLaw G uniform W M = L := by
  constructor
  · rintro ⟨MI, hMI, hL⟩
    refine ⟨R.assembledMatrices MI MX, ?_, R.assembled_on_outer MI MX, hL⟩
    intro e
    unfold RootBlobRetainedPortModel.assembledMatrices
    cases R.edgeEquiv e with
    | inl e => exact hMI e
    | inr e => exact hMX e
  · rintro ⟨M, hM, hX, hL⟩
    refine ⟨fun e : R.InnerEdge => M e.val, fun e => hM e.val, ?_⟩
    rw [R.assembled_complete M MX hX]
    exact hL

/-- Actual full observed-law factorization on the retained-port target. -/
theorem retained_observedLaw (hG : GraphAdmitted G) (W : E → ℝ)
    (MX : R.OuterEdge → Mat DNA) (MF : Fin 2 → Mat DNA) :
    observedLaw (R.retainedFork hG) uniform (R.retainedWeights W) (Sum.elim MF MX) =
      context (pairLaw RootBlobEdgeIndexed.rootedFork uniform RootBlobEdgeIndexed.forkWeights MF)
        (exteriorKernel (exteriorMass (R.exterior hG) (R.outsideWeights W) MX)
          (deterministicReadout (readout R.labels))) :=
  observedLaw_cut RootBlobEdgeIndexed.rootedFork (R.exterior hG) R.labels R.forkRank uniform
    RootBlobEdgeIndexed.forkWeights (R.outsideWeights W) MF MX

/-- Both exact image directions with no change to ANY MX parameter. A
restricted-domain pair-image equality, rather than open-H membership, is
the only mathematical input to this generic semantic composition. -/
theorem fixed_eq_retained_of_pairImage (hG : GraphAdmitted G) (W : E → ℝ)
    (MX : R.OuterEdge → Mat DNA) (T : Mat DNA → Prop)
    (himage : RootBlobNucleotideRetainedImage.effectiveImage R.interior (R.insideWeights W) T =
      RootBlobNucleotideRetainedImage.effectiveImage RootBlobEdgeIndexed.rootedFork
        RootBlobEdgeIndexed.forkWeights T) :
    fixedImage R W MX T = retainedImage R hG W MX T := by
  ext L
  constructor
  · rintro ⟨MI, hMI, hL⟩
    let K : Mat DNA := fun i j => 4 * pairLaw R.interior uniform (R.insideWeights W) MI i j
    have hK : K ∈ RootBlobNucleotideRetainedImage.effectiveImage R.interior
        (R.insideWeights W) T := by
      refine ⟨MI, hMI, ?_⟩
      funext i j
      dsimp [K]
      ring
    rw [himage] at hK
    obtain ⟨MF, hMF, hpair⟩ := hK
    refine ⟨MF, hMF, ?_⟩
    rw [R.retained_observedLaw hG W MX MF, hpair]
    have hscaled : (fun i j => K i j / 4) =
        pairLaw R.interior uniform (R.insideWeights W) MI := by
      funext i j; dsimp [K]; ring
    rw [hscaled]
    exact (R.original_observedLaw hG W uniform MI MX).symm.trans hL
  · rintro ⟨MF, hMF, hL⟩
    let K : Mat DNA := fun i j => 4 * pairLaw RootBlobEdgeIndexed.rootedFork uniform
      RootBlobEdgeIndexed.forkWeights MF i j
    have hK : K ∈ RootBlobNucleotideRetainedImage.effectiveImage RootBlobEdgeIndexed.rootedFork
        RootBlobEdgeIndexed.forkWeights T := by
      refine ⟨MF, hMF, ?_⟩
      funext i j; dsimp [K]; ring
    rw [← himage] at hK
    obtain ⟨MI, hMI, hpair⟩ := hK
    refine ⟨MI, hMI, ?_⟩
    rw [R.original_observedLaw hG W uniform MI MX, hpair]
    have hscaled : (fun i j => K i j / 4) =
        pairLaw RootBlobEdgeIndexed.rootedFork uniform RootBlobEdgeIndexed.forkWeights MF := by
      funext i j; dsimp [K]; ring
    rw [hscaled]
    exact (R.retained_observedLaw hG W MX MF).symm.trans hL

theorem fork_long :
    ∃ σ : RootBlobSwitching.Switching RootBlobEdgeIndexed.rootedFork,
      2 ≤ (RootBlobReversiblePaths.Network.portEdges (S := DNA) RootBlobEdgeIndexed.rootedFork
        (portAdmitted_of_graph _ RootBlobTreeMarginals.rootedFork_graph) σ).length := by
  have hN := portAdmitted_of_graph RootBlobEdgeIndexed.rootedFork RootBlobTreeMarginals.rootedFork_graph
  obtain ⟨σ, hσ⟩ := exists_positive_pathExponent (S := DNA) RootBlobEdgeIndexed.rootedFork hN
    (0 : Fin 2) (by rfl) (by decide)
  exact ⟨σ, RootBlobReversiblePaths.Network.long_of_positive_exponent _ hN σ hσ⟩

/-- Full source-to-source proposal for EACH literal JC/K2P/K3P domain.
The conclusion includes target graph/weight/simple/root-LSA admission, but
NOT target binary admission, nor a collapsed semidirected single-edge image.
No factorization of a zero-entry exterior matrix is required. -/
theorem maximal_nucleotide_fixed_exterior_admitted
    (B : MaximalRootTwoBlob G) (hG : GraphAdmitted G) (hB : BinaryAdmission G)
    (hNP : NoParallel G) (hLSA : RootLSA G)
    (W : E → ℝ) (hW : WeightsAdmitted G W) (m : NucleotideModel)
    (MX : (B.component hG hB).OuterEdge → Mat DNA)
    (_hMX : ∀ e, NucleotideTransition m (MX e)) :
    let R := B.component hG hB
    GraphAdmitted (R.retainedFork hG) ∧ NoParallel (R.retainedFork hG) ∧
    RootLSA (R.retainedFork hG) ∧
    WeightsAdmitted (R.retainedFork hG) (R.retainedWeights W) ∧
    fixedImage R W MX (NucleotideTransition m) = retainedImage R hG W MX (NucleotideTransition m) := by
  let R := B.component hG hB
  have hN := R.interior_admitted hG
  have hWI := R.insideWeights_admitted hG W hW
  obtain ⟨σ, _, hσ⟩ := B.positive_long_resolution (S := DNA) hG hB hNP W hW
  have hlong : ∃ σ : RootBlobSwitching.Switching R.interior,
      2 ≤ (RootBlobReversiblePaths.Network.portEdges (S := DNA) R.interior hN σ).length :=
    ⟨σ, RootBlobReversiblePaths.Network.long_of_positive_exponent R.interior hN σ hσ⟩
  have hI := nucleotide_image R.interior hN (R.insideWeights W) hWI hlong m
  have hF := nucleotide_image RootBlobEdgeIndexed.rootedFork
    (portAdmitted_of_graph _ RootBlobTreeMarginals.rootedFork_graph)
    RootBlobEdgeIndexed.forkWeights RootBlobTreeMarginals.rootedFork_weights fork_long m
  refine ⟨R.retainedFork_admitted hG, R.retainedFork_noParallel hG hNP,
    R.retainedFork_rootLSA hG hLSA, R.retainedWeights_admitted hG W hW, ?_⟩
  exact R.fixed_eq_retained_of_pairImage hG W MX (NucleotideTransition m) (hI.trans hF.symm)

end RootBlobRestrictedRetainedEndpoint
