import RootBlobDAGNormalization

/-!
# Edge-faithful switching expansion

Author: dot (OpenAI), 22 October 2026.
SOURCE-ONLY UNELABORATED proof terms. No compiler or runtime was run.
Mathlib API reference: 0df444a360eaa60ab8c11dca51a86af692955474.

Every selector chooses an ORIGINAL edge occurrence. Parallel edges remain
distinct. Transition matrices and inheritance weights are shared exactly
as in the original assignmentMass, not copied independently by resolution.
The remaining tree/path matrix marginalization is explicitly separate.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof RootBlobDAGNormalization
namespace RootBlobSwitching
universe u v w
variable {S : Type u} [Fintype S]
variable {V : Type v} {E : Type w}
variable [Fintype V] [DecidableEq V] [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2)) (W : E → ℝ)

abbrev NonRoot := {v : V // v ≠ N.root}
abbrev Incoming (v : NonRoot N) := {e : E // N.target e = v.val}
abbrev Switching := (v : NonRoot N) → Incoming N v

noncomputable def weight (σ : Switching N) : ℝ :=
  ∏ v : NonRoot N, W (σ v).val

noncomputable def resolvedMass (π : S → ℝ) (M : E → Mat S)
    (σ : Switching N) (a : V → S) : ℝ :=
  π (a N.root) *
    ∏ v : NonRoot N, M (σ v).val (a (N.source (σ v).val)) (a v.val)

noncomputable def resolvedPair (π : S → ℝ) (M : E → Mat S)
    (σ : Switching N) : Mat S := by
  classical
  exact fun i j => ∑ a : V → S,
    if (∀ o : Fin 2, a (N.observed o) = if o = 0 then i else j)
    then resolvedMass N π M σ a else 0

theorem incoming_sum (v : NonRoot N) (f : E → ℝ) :
    (∑ e : Incoming N v, f e.val) =
      ∑ e, if N.target e = v.val then f e else 0 := by
  classical
  calc
    (∑ e : Incoming N v, f e.val) =
        ∑ e ∈ Finset.univ.filter (fun e => N.target e = v.val), f e :=
      (Finset.sum_subtype (Finset.univ.filter (fun e => N.target e = v.val))
        (by intro e; simp) f).symm
    _ = ∑ e, if N.target e = v.val then f e else 0 := by
      rw [Finset.sum_filter]

theorem weight_positive
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W) (σ : Switching N) :
    0 < weight N W σ := by
  exact Finset.prod_pos (fun v _ => hW.1 (σ v).val)

theorem weight_total
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W) :
    (∑ σ : Switching N, weight N W σ) = 1 := by
  classical
  unfold weight
  rw [← Fintype.prod_sum]
  have hlocal : ∀ v : NonRoot N, (∑ e : Incoming N v, W e.val) = 1 := by
    intro v
    rw [incoming_sum]
    exact hW.2 v.val v.property
  simp_rw [hlocal]
  simp

theorem assignmentMass_expansion (π : S → ℝ) (M : E → Mat S) (a : V → S) :
    RootBlobEdgeIndexed.assignmentMass N π W M a =
      ∑ σ : Switching N, weight N W σ * resolvedMass N π M σ a := by
  classical
  have hprod :
      (Finset.univ.erase N.root).prod (fun v => ∑ e,
        if N.target e = v then W e * M e (a (N.source e)) (a v) else 0) =
      ∏ v : NonRoot N, ∑ e : Incoming N v,
        W e.val * M e.val (a (N.source e.val)) (a v.val) := by
    rw [Finset.prod_subtype (Finset.univ.erase N.root) (by intro v; simp)]
    apply Finset.prod_congr rfl
    intro v _
    exact (incoming_sum N v (fun e => W e * M e (a (N.source e)) (a v.val))).symm
  unfold RootBlobEdgeIndexed.assignmentMass
  rw [hprod, Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib]
  unfold weight resolvedMass
  ring

theorem pairLaw_expansion (π : S → ℝ) (M : E → Mat S) :
    RootBlobEdgeIndexed.pairLaw N π W M =
      fun i j => ∑ σ : Switching N, weight N W σ * resolvedPair N π M σ i j := by
  classical
  funext i j
  unfold RootBlobEdgeIndexed.pairLaw RootBlobEdgeIndexed.observedLaw
  simp_rw [assignmentMass_expansion N W π M]
  calc
    (∑ a : V → S,
      if (∀ o : Fin 2, a (N.observed o) = if o = 0 then i else j)
      then ∑ σ : Switching N, weight N W σ * resolvedMass N π M σ a else 0) =
      ∑ a : V → S, ∑ σ : Switching N, weight N W σ *
        (if (∀ o : Fin 2, a (N.observed o) = if o = 0 then i else j)
         then resolvedMass N π M σ a else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = ∑ σ : Switching N, weight N W σ * resolvedPair N π M σ i j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      rw [← Finset.mul_sum]
      rfl

def parent (σ : Switching N) (v : NonRoot N) : V :=
  N.source (σ v).val

theorem parent_rank (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : Switching N) (v : NonRoot N) :
    N.rank (parent N σ v) < N.rank v.val := by
  have h := hG.2.2.1 (σ v).val
  simpa only [parent, (σ v).property] using h

/-- Recursion on the original strict rank gives the selected edge chain
from v back to the root. No graph or inheritance parameter is altered. -/
noncomputable def ancestralEdges (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : Switching N) (v : V) : List E :=
  if h : v = N.root then [] else
    (σ ⟨v, h⟩).val :: ancestralEdges N hG σ (parent N σ ⟨v, h⟩)
termination_by N.rank v
decreasing_by exact parent_rank N hG σ ⟨v, h⟩

theorem ancestralEdges_root (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : Switching N) : ancestralEdges N hG σ N.root = [] := by
  rw [ancestralEdges]
  simp

theorem ancestralEdges_nonroot (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : Switching N) (v : NonRoot N) :
    ancestralEdges N hG σ v.val =
      (σ v).val :: ancestralEdges N hG σ (parent N σ v) := by
  rw [ancestralEdges]
  simp only [v.property, if_false]

/-- Each selected outgoing-to-parent step strictly decreases rank, so an
observed sink cannot be the parent of any selected nonroot vertex. -/
theorem observed_not_parent (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (σ : Switching N) (o : Fin 2) (v : NonRoot N) :
    N.observed o ≠ parent N σ v := by
  have hsink : ∀ e, N.source e ≠ N.observed o :=
    (hG.2.2.2.2.2 (N.observed o)).mpr ⟨o, rfl⟩
  exact Ne.symm (hsink (σ v).val)

/-- Averaging the resolved pair formula is algebraic, including its constant
term; it uses normalized ORIGINAL switching weights. -/
theorem blendPair_average {R : Type*} [Fintype R]
    (w : R → ℝ) (hw : (∑ r, w r) = 1)
    (μ : S → ℝ) (A : Mat S) (c : R → ℝ) :
    (fun i j => ∑ r, w r * blendPair μ (c r) A i j) =
      blendPair μ (∑ r, w r * c r) A := by
  funext i j
  have ht : ∀ r, w r * blendPair μ (c r) A i j =
      (w r * c r) * (μ j * A j i - μ j * rowAction μ A i) +
        w r * (μ j * rowAction μ A i) := by
    intro r
    unfold blendPair
    ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hw]
  unfold blendPair
  ring

/-- The only remaining mathematical input in this module is the resolved
tree/path formula. This record is a proof obligation, not an axiom or proof.
Its exponent must come from the original selected path, not from a target. -/
structure ResolvedPathFormula (H : Subgroup (Equiv.Perm S)) where
  exponent : Switching N → ℕ
  exponent_pos : ∀ σ, 0 < exponent σ
  formula : ∀ (σ : Switching N) (μ : S → ℝ) (A : Mat S) (t : ℝ),
    RootAdmitted H μ → (∀ i, 0 < μ i) → OpenTransition H A →
    0 < t → t < 1 →
    resolvedPair N μ (RootBlobOpenProof.Edge.terminalAssignment N A
      (equalInput μ t)) σ = blendPair μ (t ^ exponent σ) A

noncomputable def resolutionCertificate
    (H : Subgroup (Equiv.Perm S))
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (T : ResolvedPathFormula N H) :
    RootBlobOpenProof.Edge.ResolutionCertificate N W H (Switching N) where
  weight := weight N W
  exponent := T.exponent
  weight_pos := weight_positive N W hW
  weight_total := weight_total N W hW
  exponent_pos := T.exponent_pos
  formula := by
    intro μ A t hμ hμpos hA ht0 ht1
    rw [pairLaw_expansion]
    have hres : ∀ σ : Switching N,
        resolvedPair N μ (RootBlobOpenProof.Edge.terminalAssignment N A
          (equalInput μ t)) σ = blendPair μ (t ^ T.exponent σ) A :=
      fun σ => T.formula σ μ A t hμ hμpos hA ht0 ht1
    simp_rw [hres]
    exact blendPair_average (weight N W) (weight_total N W hW) μ A
      (fun σ => t ^ T.exponent σ)

theorem openImageClaim_of_resolvedPaths [Nonempty S]
    (H : Subgroup (Equiv.Perm S))
    (hpaths : RootBlobEdgeIndexed.GraphAdmitted N → ResolvedPathFormula N H) :
    RootBlobEdgeIndexed.OpenImageClaim N W H := by
  apply RootBlobDAGNormalization.Edge.openImageClaim_of_resolution N W H
  intro hG hW
  exact resolutionCertificate N W H hW (hpaths hG)

end RootBlobSwitching
