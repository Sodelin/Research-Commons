import RootBlobRetainedPortGraph

/-!
# Full original observed-law equality with fixed original exterior matrices
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No runtime/compiler/kernel certification.

Both original cut-edge occurrences belong to OuterEdge. Their matrices are
fixed in MX in BOTH image directions; there is no subdivision, multiplication
or reparameterization of an exterior matrix. Deleted internal inheritance
is used unchanged when realizing the original graph. New fork edges have
weight one. Equality is for the original finite assignment-sum observed law.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobEdgeIndexed RootBlobContextGlue
open RootBlobCutFactorization RootBlobRelabeling RootBlobRetainedPortSemantics
open RootBlobRetainedPortGraph
namespace RootBlobRetainedPortModel
universe u v w x
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E]
variable {O : Type x} [Fintype O]
variable {G : Network V E O} (R : PortComponent G)

def assembledMatrices (MI : R.InnerEdge → Mat S) (MX : R.OuterEdge → Mat S) : E → Mat S :=
  fun e => Sum.elim MI MX (R.edgeEquiv e)

theorem assembled_on_outer (MI : R.InnerEdge → Mat S) (MX : R.OuterEdge → Mat S)
    (e : R.OuterEdge) : R.assembledMatrices MI MX e.val = MX e := by
  have he := R.edgeEquiv.apply_symm_apply (Sum.inr e)
  rw [R.edgeEquiv_symm_inr] at he
  simp [assembledMatrices, he]

theorem assembled_on_inner (MI : R.InnerEdge → Mat S) (MX : R.OuterEdge → Mat S)
    (e : R.InnerEdge) : R.assembledMatrices MI MX e.val = MI e := by
  have he := R.edgeEquiv.apply_symm_apply (Sum.inl e)
  rw [R.edgeEquiv_symm_inl] at he
  simp [assembledMatrices, he]

/-- Every original parameter point with the prescribed exterior appears in
the assembled image. Thus fixedImage is not a smaller surrogate model. -/
theorem assembled_complete (M : E → Mat S) (MX : R.OuterEdge → Mat S)
    (hX : ∀ e : R.OuterEdge, M e.val = MX e) :
    R.assembledMatrices (fun e : R.InnerEdge => M e.val) MX = M := by
  funext e
  have h := R.edgeEquiv.symm_apply_apply e
  cases he : R.edgeEquiv e with
  | inl i =>
    have hei : i.val = e := by simpa [he, R.edgeEquiv_symm_inl] using h
    simp [assembledMatrices, he, hei]
  | inr x =>
    have hex : x.val = e := by simpa [he, R.edgeEquiv_symm_inr] using h
    simp [assembledMatrices, he, ← hX x, hex]

theorem weights_split (W : E → ℝ) :
    (fun e => W (R.edgeEquiv.symm e)) =
      Sum.elim (R.insideWeights W) (R.outsideWeights W) := by
  funext e
  cases e with
  | inl e => rw [R.edgeEquiv_symm_inl]; rfl
  | inr e => rw [R.edgeEquiv_symm_inr]; rfl

theorem matrices_split (MI : R.InnerEdge → Mat S) (MX : R.OuterEdge → Mat S) :
    (fun e => R.assembledMatrices MI MX (R.edgeEquiv.symm e)) =
      Sum.elim MI MX := by
  funext e
  simp [assembledMatrices]

theorem cutWeights_admitted (hG : GraphAdmitted G) (W : E → ℝ)
    (hW : WeightsAdmitted G W) :
    WeightsAdmitted (cutNetwork R.interior (R.exterior hG) R.labels R.fullRank)
      (Sum.elim (R.insideWeights W) (R.outsideWeights W)) := by
  have h := weights_admission_relabel G R.vertexEquiv R.edgeEquiv W hW
  rw [R.graph_partition hG, R.weights_split W] at h
  exact h

theorem insideWeights_admitted (hG : GraphAdmitted G) (W : E → ℝ)
    (hW : WeightsAdmitted G W) :
    WeightsAdmitted R.interior (R.insideWeights W) := by
  classical
  constructor
  · intro e
    exact hW.1 e.val
  · intro v hv
    have hn : Sum.inl v ≠
        (cutNetwork R.interior (R.exterior hG) R.labels R.fullRank).root := by
      simpa [cutNetwork] using hv
    have h := (R.cutWeights_admitted hG W hW).2 (Sum.inl v) hn
    simpa [cutNetwork, Fintype.sum_sum_type] using h

theorem outsideWeights_normalized (hG : GraphAdmitted G) (W : E → ℝ)
    (hW : WeightsAdmitted G W) (v : R.Outside) :
    (∑ e, if (R.exterior hG).target e = v then R.outsideWeights W e else 0) = 1 := by
  classical
  have hn : Sum.inr v ≠
      (cutNetwork R.interior (R.exterior hG) R.labels R.fullRank).root := by
    simp [cutNetwork]
  have h := (R.cutWeights_admitted hG W hW).2 (Sum.inr v) hn
  simpa [cutNetwork, Fintype.sum_sum_type] using h

theorem retainedWeights_admitted (hG : GraphAdmitted G) (W : E → ℝ)
    (hW : WeightsAdmitted G W) :
    WeightsAdmitted (R.retainedFork hG) (R.retainedWeights W) := by
  classical
  constructor
  · intro e
    cases e with
    | inl e => norm_num [retainedWeights, forkWeights]
    | inr e => exact hW.1 e.val
  · intro v hv
    cases v with
    | inl v =>
      have hn : v ≠ rootedFork.root := by intro he; exact hv (congrArg Sum.inl he)
      have h := RootBlobTreeMarginals.rootedFork_weights.2 v hn
      simpa [retainedFork, cutNetwork, retainedWeights, Fintype.sum_sum_type] using h
    | inr v =>
      simpa [retainedFork, cutNetwork, retainedWeights, Fintype.sum_sum_type] using
        R.outsideWeights_normalized hG W hW v

theorem original_observedLaw (hG : GraphAdmitted G) (W : E → ℝ)
    (π : S → ℝ) (MI : R.InnerEdge → Mat S) (MX : R.OuterEdge → Mat S) :
    observedLaw G π W (R.assembledMatrices MI MX) =
      context (pairLaw R.interior π (R.insideWeights W) MI)
        (exteriorKernel (exteriorMass (R.exterior hG) (R.outsideWeights W) MX)
          (deterministicReadout (readout R.labels))) := by
  calc
    observedLaw G π W (R.assembledMatrices MI MX) =
      observedLaw (relabel G R.vertexEquiv R.edgeEquiv) π
        (fun e => W (R.edgeEquiv.symm e))
        (fun e => R.assembledMatrices MI MX (R.edgeEquiv.symm e)) :=
      (observedLaw_relabel G R.vertexEquiv R.edgeEquiv W π
        (R.assembledMatrices MI MX)).symm
    _ = observedLaw (cutNetwork R.interior (R.exterior hG) R.labels R.fullRank) π
        (Sum.elim (R.insideWeights W) (R.outsideWeights W))
        (Sum.elim MI MX) := by
      rw [R.graph_partition hG, R.weights_split W, R.matrices_split MI MX]
    _ = _ := observedLaw_cut R.interior (R.exterior hG) R.labels R.fullRank π
      (R.insideWeights W) (R.outsideWeights W) MI MX

noncomputable def fixedImage (W : E → ℝ) (MX : R.OuterEdge → Mat S)
    (H : Subgroup (Equiv.Perm S)) : Set ((O → S) → ℝ) :=
  {L | ∃ (π : S → ℝ) (MI : R.InnerEdge → Mat S),
    RootAdmitted H π ∧ (∀ e, OpenTransition H (MI e)) ∧
    observedLaw G π W (R.assembledMatrices MI MX) = L}

theorem fixedImage_eq_context (hG : GraphAdmitted G) (W : E → ℝ)
    (MX : R.OuterEdge → Mat S) (H : Subgroup (Equiv.Perm S)) :
    R.fixedImage W MX H =
      Set.image (fun P => context P
        (exteriorKernel (exteriorMass (R.exterior hG) (R.outsideWeights W) MX)
          (deterministicReadout (readout R.labels))))
        (openImage R.interior (R.insideWeights W) H) := by
  apply Set.ext
  intro L
  constructor
  · rintro ⟨π, MI, hπ, hM, heq⟩
    refine ⟨pairLaw R.interior π (R.insideWeights W) MI,
      ⟨π, MI, hπ, hM, rfl⟩, ?_⟩
    exact (R.original_observedLaw hG W π MI MX).symm.trans heq
  · rintro ⟨P, ⟨π, MI, hπ, hM, hP⟩, hL⟩
    refine ⟨π, MI, hπ, hM, ?_⟩
    rw [R.original_observedLaw hG, hP]
    exact hL

/-- Full direct image equality, with both original cut matrices included in
the SAME fixed MX. The actual graph and weight admission are conclusions,
not silently supplied by rank-free image algebra. This is the open-H
domain only: it does NOT formally establish nucleotide or rate subclasses. -/
theorem fixed_exterior_full [Nonempty S] (hG : GraphAdmitted G)
    (W : E → ℝ) (hW : WeightsAdmitted G W)
    (MX : R.OuterEdge → Mat S) (H : Subgroup (Equiv.Perm S))
    (_hMX : ∀ e, OpenTransition H (MX e)) :
    GraphAdmitted (R.retainedFork hG) ∧
    WeightsAdmitted (R.retainedFork hG) (R.retainedWeights W) ∧
    R.fixedImage W MX H =
      cutImage rootedFork (R.exterior hG) R.labels R.forkRank
        forkWeights (R.outsideWeights W) MX H := by
  refine ⟨R.retainedFork_admitted hG, R.retainedWeights_admitted hG W hW, ?_⟩
  rw [R.fixedImage_eq_context hG, cutImage_eq_context,
    RootBlobRetainedPortSemantics.openImage_eq R.interior (R.interior_admitted hG)
      (R.insideWeights W) (R.insideWeights_admitted hG W hW) H,
    RootBlobRetainedPortSemantics.openImage_eq rootedFork
      (portAdmitted_of_graph rootedFork RootBlobTreeMarginals.rootedFork_graph)
      forkWeights RootBlobTreeMarginals.rootedFork_weights H]

end RootBlobRetainedPortModel
