import RootBlobComponentConstructor

/-!
# Complete original observed-law model image equality

Author: dot (OpenAI), 22 October 2026.
UNELABORATED source only. No execution or verification.
This final assembly also quantifies over all admitted exterior matrices.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobContextGlue RootBlobCutFactorization
open RootBlobSourceCut RootBlobComponentConstructor
namespace RootBlobFullModel
universe u v w x y z r
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E]
variable {O : Type x} [Fintype O]

/-- The full original model, with all admitted original edge matrices and
the freely varying invariant root; the original inheritance W is fixed. -/
noncomputable def modelImage (G : RootBlobEdgeIndexed.Network V E O)
    (W : E → ℝ) (H : Subgroup (Equiv.Perm S)) : Set ((O → S) → ℝ) :=
  {L | ∃ (π : S → ℝ) (M : E → Mat S),
    RootAdmitted H π ∧ (∀ e, OpenTransition H (M e)) ∧
    RootBlobEdgeIndexed.observedLaw G π W M = L}

variable {A : Type y} [Fintype A] [DecidableEq A]
variable {B : Type z} [Fintype B] [DecidableEq B]
variable {EI EX : Type r} [Fintype EI] [Fintype EX]
variable {G : RootBlobEdgeIndexed.Network V E O}
variable (C : SourceCut (A := A) (B := B) (EI := EI) (EX := EX) G)

theorem original_model_split (W : E → ℝ) (H : Subgroup (Equiv.Perm S))
    (L : (O → S) → ℝ) :
    L ∈ modelImage G W H ↔
      ∃ MX : EX → Mat S, (∀ e, OpenTransition H (MX e)) ∧
        L ∈ C.originalImage W MX H := by
  constructor
  · rintro ⟨π, M, hπ, hM, hL⟩
    let MI : EI → Mat S := fun e => M (C.edges.symm (Sum.inl e))
    let MX : EX → Mat S := fun e => M (C.edges.symm (Sum.inr e))
    have ha : C.assembledMatrices MI MX = M := by
      funext e
      calc
        C.assembledMatrices MI MX e = M (C.edges.symm (C.edges e)) := by
          unfold RootBlobSourceCut.assembledMatrices
          cases C.edges e <;> rfl
        _ = M e := by rw [C.edges.symm_apply_apply]
    refine ⟨MX, (fun e => hM _), π, MI, hπ, (fun e => hM _), ?_⟩
    rw [ha]
    exact hL
  · rintro ⟨MX, hMX, π, MI, hπ, hMI, hL⟩
    refine ⟨π, C.assembledMatrices MI MX, hπ, ?_, hL⟩
    intro e
    cases he : C.edges e with
    | inl i => simpa [RootBlobSourceCut.assembledMatrices, he] using hMI i
    | inr x => simpa [RootBlobSourceCut.assembledMatrices, he] using hMX x

/-- The analogous parameter split for the literal cut network. No graph or
probability factorization hypothesis is needed for this bijection of parameters. -/
theorem cut_model_split {I : Type*} [Fintype I]
    (N : RootBlobEdgeIndexed.Network A I (Fin 2)) (D : ExteriorDAG B EX)
    (labels : O → Sum (Fin 2) B) (rank : Sum A B → ℕ)
    (WI : I → ℝ) (WX : EX → ℝ) (H : Subgroup (Equiv.Perm S))
    (L : (O → S) → ℝ) :
    L ∈ modelImage (cutNetwork N D labels rank) (Sum.elim WI WX) H ↔
      ∃ MX : EX → Mat S, (∀ e, OpenTransition H (MX e)) ∧
        L ∈ cutImage N D labels rank WI WX MX H := by
  constructor
  · rintro ⟨π, M, hπ, hM, hL⟩
    let MI : I → Mat S := fun e => M (Sum.inl e)
    let MX : EX → Mat S := fun e => M (Sum.inr e)
    have ha : Sum.elim MI MX = M := by
      funext e
      cases e <;> rfl
    refine ⟨MX, (fun e => hM _), π, MI, hπ, (fun e => hM _), ?_⟩
    rw [ha]
    exact hL
  · rintro ⟨MX, hMX, π, MI, hπ, hMI, hL⟩
    refine ⟨π, Sum.elim MI MX, hπ, ?_, hL⟩
    intro e
    cases e with
    | inl i => exact hMI i
    | inr x => exact hMX x

theorem source_model_eq_rootedFork [Nonempty S]
    (W : E → ℝ) (H : Subgroup (Equiv.Perm S))
    (forkRank : Sum (Fin 3) B → ℕ)
    (hS : 1 < Fintype.card S)
    (hG : RootBlobEdgeIndexed.GraphAdmitted G)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted G W) :
    modelImage G W H =
      modelImage (cutNetwork RootBlobEdgeIndexed.rootedFork C.exterior C.labels forkRank)
        (Sum.elim RootBlobEdgeIndexed.forkWeights (C.outsideWeights W)) H := by
  apply Set.ext
  intro L
  rw [C.original_model_split, cut_model_split]
  constructor
  · rintro ⟨MX, hMX, hL⟩
    refine ⟨MX, hMX, ?_⟩
    rw [← C.originalImage_eq_rootedFork W MX H forkRank hS hG hW hMX]
    exact hL
  · rintro ⟨MX, hMX, hL⟩
    refine ⟨MX, hMX, ?_⟩
    rw [C.originalImage_eq_rootedFork W MX H forkRank hS hG hW hMX]
    exact hL

/-- The whole selected original-class open-equivariant theorem. The graph
adapter is constructed from the component properties, and every original
edge parameter is included in the model image. -/
theorem rootComponent_model_eq_rootedFork [Nonempty S]
    (R : RootComponent G)
    (hG : RootBlobEdgeIndexed.GraphAdmitted G)
    (W : E → ℝ) (hW : RootBlobEdgeIndexed.WeightsAdmitted G W)
    (H : Subgroup (Equiv.Perm S))
    (forkRank : Sum (Fin 3) R.Outside → ℕ)
    (hS : 1 < Fintype.card S) :
    modelImage G W H =
      modelImage
        (cutNetwork RootBlobEdgeIndexed.rootedFork (R.exterior hG) R.labels forkRank)
        (Sum.elim RootBlobEdgeIndexed.forkWeights
          ((R.sourceCut hG).outsideWeights W)) H :=
  source_model_eq_rootedFork (R.sourceCut hG) W H forkRank hS hG hW

end RootBlobFullModel
