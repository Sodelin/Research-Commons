import RootBlobRelabeling

/-!
# Source-faithful graph-cut adapter for the original observed law

Author: dot (OpenAI), 22 October 2026.
UNELABORATED proof terms. No runtime, Lean verification or novelty claim.
The input certificate contains only structural graph data and equalities,
not a stochastic-law, normalization or image-equality assumption.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobContextGlue RootBlobCutFactorization RootBlobRelabeling
namespace RootBlobSourceCut
universe u v w x y z r
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E]
variable {O : Type x} [Fintype O]
variable {A : Type y} [Fintype A] [DecidableEq A]
variable {B : Type z} [Fintype B] [DecidableEq B]
variable {EI EX : Type r} [Fintype EI] [Fintype EX]

/-- Structural adapter for the root component. All global observed variables
remain outside the hidden blob, as in the cited root-2-blob obligation. -/
structure SourceCut (G : RootBlobEdgeIndexed.Network V E O) where
  interior : RootBlobEdgeIndexed.Network A EI (Fin 2)
  exterior : ExteriorDAG B EX
  labels : O → Sum (Fin 2) B
  rank : Sum A B → ℕ
  vertices : V ≃ Sum A B
  edges : E ≃ Sum EI EX
  graph_eq : relabel G vertices edges = cutNetwork interior exterior labels rank
  interior_admitted : RootBlobEdgeIndexed.GraphAdmitted interior
  hidden_blob : ∀ o, ∃ b, labels o = Sum.inr b

variable {G : RootBlobEdgeIndexed.Network V E O}
variable (C : SourceCut (A := A) (B := B) (EI := EI) (EX := EX) G)

def insideWeights (W : E → ℝ) : EI → ℝ := fun e => W (C.edges.symm (Sum.inl e))
def outsideWeights (W : E → ℝ) : EX → ℝ := fun e => W (C.edges.symm (Sum.inr e))
def assembledMatrices (MI : EI → Mat S) (MX : EX → Mat S) : E → Mat S :=
  fun e => Sum.elim MI MX (C.edges e)

theorem weights_split (W : E → ℝ) :
    (fun e => W (C.edges.symm e)) = Sum.elim (C.insideWeights W) (C.outsideWeights W) := by
  funext e
  cases e <;> rfl

theorem matrices_split (MI : EI → Mat S) (MX : EX → Mat S) :
    (fun e => C.assembledMatrices MI MX (C.edges.symm e)) = Sum.elim MI MX := by
  funext e
  simp [assembledMatrices]

theorem cutWeights_admitted (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted G W) :
    RootBlobEdgeIndexed.WeightsAdmitted
      (cutNetwork C.interior C.exterior C.labels C.rank)
      (Sum.elim (C.insideWeights W) (C.outsideWeights W)) := by
  have h := weights_admission_relabel G C.vertices C.edges W hW
  rw [C.graph_eq, C.weights_split] at h
  exact h

theorem insideWeights_admitted (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted G W) :
    RootBlobEdgeIndexed.WeightsAdmitted C.interior (C.insideWeights W) := by
  classical
  constructor
  · intro e
    exact hW.1 (C.edges.symm (Sum.inl e))
  · intro v hv
    have hn : Sum.inl v ≠ (cutNetwork C.interior C.exterior C.labels C.rank).root := by
      simpa [cutNetwork] using hv
    have h := (C.cutWeights_admitted W hW).2 (Sum.inl v) hn
    simpa [cutNetwork, Fintype.sum_sum_type] using h

theorem outsideWeights_positive (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted G W) :
    ∀ e, 0 < C.outsideWeights W e :=
  fun e => hW.1 (C.edges.symm (Sum.inr e))

theorem outsideWeights_normalized (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted G W) (v : B) :
    (∑ e, if C.exterior.target e = v then C.outsideWeights W e else 0) = 1 := by
  classical
  have hn : Sum.inr v ≠ (cutNetwork C.interior C.exterior C.labels C.rank).root := by
    simp [cutNetwork]
  have h := (C.cutWeights_admitted W hW).2 (Sum.inr v) hn
  simpa [cutNetwork, Fintype.sum_sum_type] using h

/-- Actual full original law, before any vertex or edge relabeling. -/
theorem original_observedLaw (W : E → ℝ) (π : S → ℝ)
    (MI : EI → Mat S) (MX : EX → Mat S) :
    RootBlobEdgeIndexed.observedLaw G π W (C.assembledMatrices MI MX) =
    context (RootBlobEdgeIndexed.pairLaw C.interior π (C.insideWeights W) MI)
      (exteriorKernel (exteriorMass C.exterior (C.outsideWeights W) MX)
        (deterministicReadout (readout C.labels))) := by
  calc
    RootBlobEdgeIndexed.observedLaw G π W (C.assembledMatrices MI MX) =
      RootBlobEdgeIndexed.observedLaw (relabel G C.vertices C.edges) π
        (fun e => W (C.edges.symm e))
        (fun e => C.assembledMatrices MI MX (C.edges.symm e)) :=
      (observedLaw_relabel G C.vertices C.edges W π (C.assembledMatrices MI MX)).symm
    _ = RootBlobEdgeIndexed.observedLaw
        (cutNetwork C.interior C.exterior C.labels C.rank) π
        (Sum.elim (C.insideWeights W) (C.outsideWeights W))
        (Sum.elim MI MX) := by
      rw [C.graph_eq, C.weights_split, C.matrices_split]
    _ = _ := observedLaw_cut C.interior C.exterior C.labels C.rank π
      (C.insideWeights W) (C.outsideWeights W) MI MX

noncomputable def originalImage (W : E → ℝ) (MX : EX → Mat S)
    (H : Subgroup (Equiv.Perm S)) : Set ((O → S) → ℝ) :=
  {L | ∃ (π : S → ℝ) (MI : EI → Mat S),
    RootAdmitted H π ∧ (∀ e, OpenTransition H (MI e)) ∧
    RootBlobEdgeIndexed.observedLaw G π W (C.assembledMatrices MI MX) = L}

theorem originalImage_eq_context (W : E → ℝ) (MX : EX → Mat S)
    (H : Subgroup (Equiv.Perm S)) :
    C.originalImage W MX H =
      Set.image (fun P => context P
        (exteriorKernel (exteriorMass C.exterior (C.outsideWeights W) MX)
          (deterministicReadout (readout C.labels))))
        (RootBlobEdgeIndexed.openImage C.interior (C.insideWeights W) H) := by
  apply Set.ext
  intro L
  constructor
  · rintro ⟨π, MI, hπ, hM, heq⟩
    refine ⟨RootBlobEdgeIndexed.pairLaw C.interior π (C.insideWeights W) MI,
      ⟨π, MI, hπ, hM, rfl⟩, ?_⟩
    exact (C.original_observedLaw W π MI MX).symm.trans heq
  · rintro ⟨P, ⟨π, MI, hπ, hM, hP⟩, hL⟩
    refine ⟨π, MI, hπ, hM, ?_⟩
    rw [C.original_observedLaw, hP]
    exact hL

/-- Source-graph endpoint. Fixed original weights and fixed exterior matrices
are transported bijectively, never copied independently across resolutions.
The source admission is retained even though the polynomial identity is
stronger and does not itself require every one of those graph hypotheses. -/
theorem originalImage_eq_rootedFork [Nonempty S]
    (W : E → ℝ) (MX : EX → Mat S) (H : Subgroup (Equiv.Perm S))
    (forkRank : Sum (Fin 3) B → ℕ)
    (hS : 1 < Fintype.card S)
    (hG : RootBlobEdgeIndexed.GraphAdmitted G)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted G W)
    (hMX : ∀ e, OpenTransition H (MX e)) :
    C.originalImage W MX H =
      cutImage RootBlobEdgeIndexed.rootedFork C.exterior C.labels forkRank
        RootBlobEdgeIndexed.forkWeights (C.outsideWeights W) MX H := by
  calc
    C.originalImage W MX H =
      cutImage C.interior C.exterior C.labels C.rank
        (C.insideWeights W) (C.outsideWeights W) MX H := by
      rw [C.originalImage_eq_context, cutImage_eq_context]
    _ = _ := cutImage_eq_rootedFork C.interior C.exterior C.labels C.rank forkRank
      (C.insideWeights W) (C.outsideWeights W) MX H hS C.interior_admitted
      (C.insideWeights_admitted W hW) (C.outsideWeights_positive W hW)
      (C.outsideWeights_normalized W hW) hMX

end RootBlobSourceCut
