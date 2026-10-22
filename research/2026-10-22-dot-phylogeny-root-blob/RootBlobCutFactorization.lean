import RootBlobContextGlue

/-!
# Literal graph-cut factorization of the original edge-indexed law

Author: dot (OpenAI), 22 October 2026.
UNELABORATED source only. No formal execution or verification.
This module proves the state-sum adapter for a literal vertex/edge partition.
It does not assume that a published semidirected block has been so partitioned.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof RootBlobDAGNormalization
open RootBlobContextGlue
namespace RootBlobCutFactorization
universe u v w x y z
variable {S : Type u} [Fintype S]
variable {A : Type v} [Fintype A] [DecidableEq A]
variable {B : Type w} [Fintype B] [DecidableEq B]
variable {EI : Type x} [Fintype EI]
variable {EX : Type y} [Fintype EX]
variable {O : Type z} [Fintype O]
variable (N : RootBlobEdgeIndexed.Network A EI (Fin 2))
variable (D : ExteriorDAG B EX)


/-- The normalization module's local-factor identity generalized only in
its observation type. Observation coordinates do not enter assignmentMass. -/
noncomputable def vertexFactor {V E I : Type*} [Fintype E]
    (G : RootBlobEdgeIndexed.Network V E I) (W : E → ℝ)
    (π : S → ℝ) (M : E → Mat S) (v : V) (a : V → S) : ℝ := by
  classical
  exact if v = G.root then π (a G.root) else
    ∑ e, if G.target e = v then W e * M e (a (G.source e)) (a v) else 0

theorem product_vertexFactor {V E I : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : RootBlobEdgeIndexed.Network V E I) (W : E → ℝ)
    (π : S → ℝ) (M : E → Mat S) (a : V → S) :
    (∏ v, vertexFactor G W π M v a) =
      RootBlobEdgeIndexed.assignmentMass G π W M a := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun v => vertexFactor G W π M v a) (Finset.mem_univ G.root)]
  unfold RootBlobEdgeIndexed.assignmentMass
  simp only [vertexFactor, if_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  exact if_neg (Finset.mem_erase.mp hv).1

def boundarySource : Sum (Fin 2) B → Sum A B :=
  Sum.elim (fun o => Sum.inl (N.observed o)) Sum.inr

/-- The full graph keeps a disjoint union of the ORIGINAL edge occurrences.
The given full rank is metadata here; its source admission is separate. -/
def cutNetwork (labels : O → Sum (Fin 2) B) (rank : Sum A B → ℕ) :
    RootBlobEdgeIndexed.Network (Sum A B) (Sum EI EX) O where
  root := Sum.inl N.root
  observed := fun o => boundarySource N (labels o)
  source := Sum.elim (fun e => Sum.inl (N.source e))
    (fun e => boundarySource N (D.source e))
  target := Sum.elim (fun e => Sum.inl (N.target e)) (fun e => Sum.inr (D.target e))
  rank := rank

noncomputable def exteriorMass (W : EX → ℝ) (M : EX → Mat S)
    (i j : S) (b : B → S) : ℝ := ∏ v, D.factor W M i j v b

noncomputable def readout (labels : O → Sum (Fin 2) B)
    (i j : S) (b : B → S) : O → S := by
  classical
  exact fun o => match labels o with
    | Sum.inl p => if p = 0 then i else j
    | Sum.inr v => b v

theorem boundarySource_state (a : Sum A B → S) (s : Sum (Fin 2) B) :
    a (boundarySource N s) =
      (match s with
        | Sum.inl p => if p = 0 then a (Sum.inl (N.observed 0))
          else a (Sum.inl (N.observed 1))
        | Sum.inr v => a (Sum.inr v)) := by
  classical
  cases s with
  | inl p => fin_cases p <;> simp [boundarySource]
  | inr v => rfl

theorem exterior_source_state (a : Sum A B → S) (e : EX) :
    a (boundarySource N (D.source e)) =
      D.sourceState (a (Sum.inl (N.observed 0))) (a (Sum.inl (N.observed 1)))
        (fun v => a (Sum.inr v)) e := by
  rw [boundarySource_state]
  rfl

theorem local_internal (labels : O → Sum (Fin 2) B) (rank : Sum A B → ℕ)
    (π : S → ℝ) (WI : EI → ℝ) (WX : EX → ℝ)
    (MI : EI → Mat S) (MX : EX → Mat S) (v : A) (a : Sum A B → S) :
    vertexFactor (cutNetwork N D labels rank)
      (Sum.elim WI WX) π (Sum.elim MI MX) (Sum.inl v) a =
    vertexFactor N WI π MI v
      (fun u => a (Sum.inl u)) := by
  classical
  by_cases hv : v = N.root
  · subst v
    simp [vertexFactor, cutNetwork]
  · simp [vertexFactor, cutNetwork, hv,
      Fintype.sum_sum_type]

theorem local_exterior (labels : O → Sum (Fin 2) B) (rank : Sum A B → ℕ)
    (π : S → ℝ) (WI : EI → ℝ) (WX : EX → ℝ)
    (MI : EI → Mat S) (MX : EX → Mat S) (v : B) (a : Sum A B → S) :
    vertexFactor (cutNetwork N D labels rank)
      (Sum.elim WI WX) π (Sum.elim MI MX) (Sum.inr v) a =
    D.factor WX MX (a (Sum.inl (N.observed 0))) (a (Sum.inl (N.observed 1)))
      v (fun u => a (Sum.inr u)) := by
  classical
  simp only [vertexFactor, cutNetwork,
    Sum.inr_ne_inl, if_false, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Sum.inl_ne_inr, Sum.inr.injEq, Finset.sum_const_zero, zero_add]
  unfold ExteriorDAG.factor
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : D.target e = v
  · simp only [he, if_true]
    rw [exterior_source_state]
  · simp only [he, if_false]

/-- Factorization of the actual original full assignmentMass. No stochastic,
independence or tensor-factorization assertion is an input to this theorem. -/
theorem assignmentMass_cut (labels : O → Sum (Fin 2) B) (rank : Sum A B → ℕ)
    (π : S → ℝ) (WI : EI → ℝ) (WX : EX → ℝ)
    (MI : EI → Mat S) (MX : EX → Mat S) (a : Sum A B → S) :
    RootBlobEdgeIndexed.assignmentMass (cutNetwork N D labels rank) π
      (Sum.elim WI WX) (Sum.elim MI MX) a =
    RootBlobEdgeIndexed.assignmentMass N π WI MI (fun u => a (Sum.inl u)) *
      exteriorMass D WX MX
        (a (Sum.inl (N.observed 0))) (a (Sum.inl (N.observed 1)))
        (fun v => a (Sum.inr v)) := by
  classical
  rw [← product_vertexFactor]
  rw [Fintype.prod_sum_type]
  simp_rw [local_internal, local_exterior]
  rw [product_vertexFactor]
  rfl

theorem readout_assignment (labels : O → Sum (Fin 2) B) (a : Sum A B → S) :
    (fun o => a (boundarySource N (labels o))) =
      readout labels (a (Sum.inl (N.observed 0))) (a (Sum.inl (N.observed 1)))
        (fun v => a (Sum.inr v)) := by
  funext o
  exact boundarySource_state N a (labels o)

/-- The original observedLaw, not a newly defined surrogate, is the joint
port-context contraction. Observations may include either port itself. -/
theorem observedLaw_cut (labels : O → Sum (Fin 2) B) (rank : Sum A B → ℕ)
    (π : S → ℝ) (WI : EI → ℝ) (WX : EX → ℝ)
    (MI : EI → Mat S) (MX : EX → Mat S) :
    RootBlobEdgeIndexed.observedLaw (cutNetwork N D labels rank) π
      (Sum.elim WI WX) (Sum.elim MI MX) =
    context (RootBlobEdgeIndexed.pairLaw N π WI MI)
      (exteriorKernel (exteriorMass D WX MX) (deterministicReadout (readout labels))) := by
  rw [← cutNetworkLaw_eq_context N π WI MI]
  funext obs
  unfold RootBlobEdgeIndexed.observedLaw cutLaw
  apply Finset.sum_congr rfl
  intro a _
  rw [assignmentMass_cut N D labels rank π WI WX MI MX a]
  have hc : (∀ o, a ((cutNetwork N D labels rank).observed o) = obs o) ↔
      readout labels (a (Sum.inl (N.observed 0))) (a (Sum.inl (N.observed 1)))
        (fun v => a (Sum.inr v)) = obs := by
    constructor
    · intro h
      rw [← readout_assignment N labels a]
      exact funext h
    · intro h o
      rw [← readout_assignment N labels a] at h
      exact congrFun h o
  rw [hc]
  unfold deterministicReadout
  split_ifs <;> simp

theorem exteriorKernel_admitted [Nonempty S]
    (labels : O → Sum (Fin 2) B) (WX : EX → ℝ) (MX : EX → Mat S)
    (hW0 : ∀ e, 0 ≤ WX e)
    (hW1 : ∀ v, (∑ e, if D.target e = v then WX e else 0) = 1)
    (hM0 : ∀ e i j, 0 ≤ MX e i j)
    (hM1 : ∀ e i, (∑ j, MX e i j) = 1) :
    ContextAdmitted
      (exteriorKernel (exteriorMass D WX MX) (deterministicReadout (readout labels))) :=
  (D.factors WX MX hW0 hW1 hM0 hM1).context_admitted
    (deterministicReadout (readout labels))
    (deterministicReadout_nonneg (readout labels))
    (deterministicReadout_total (readout labels))


/-- The full graph model with the exterior parameters fixed and only the
original root-component parameters varying over their exact open class. -/
noncomputable def cutImage (labels : O → Sum (Fin 2) B) (rank : Sum A B → ℕ)
    (WI : EI → ℝ) (WX : EX → ℝ) (MX : EX → Mat S)
    (H : Subgroup (Equiv.Perm S)) : Set ((O → S) → ℝ) :=
  {L | ∃ (π : S → ℝ) (MI : EI → Mat S),
    RootAdmitted H π ∧ (∀ e, OpenTransition H (MI e)) ∧
    RootBlobEdgeIndexed.observedLaw (cutNetwork N D labels rank) π
      (Sum.elim WI WX) (Sum.elim MI MX) = L}

theorem cutImage_eq_context (labels : O → Sum (Fin 2) B) (rank : Sum A B → ℕ)
    (WI : EI → ℝ) (WX : EX → ℝ) (MX : EX → Mat S)
    (H : Subgroup (Equiv.Perm S)) :
    cutImage N D labels rank WI WX MX H =
      Set.image (fun P => context P
        (exteriorKernel (exteriorMass D WX MX) (deterministicReadout (readout labels))))
        (RootBlobEdgeIndexed.openImage N WI H) := by
  apply Set.ext
  intro L
  constructor
  · rintro ⟨π, MI, hπ, hM, heq⟩
    refine ⟨RootBlobEdgeIndexed.pairLaw N π WI MI, ⟨π, MI, hπ, hM, rfl⟩, ?_⟩
    exact (observedLaw_cut N D labels rank π WI WX MI MX).symm.trans heq
  · rintro ⟨P, ⟨π, MI, hπ, hM, hP⟩, hL⟩
    refine ⟨π, MI, hπ, hM, ?_⟩
    rw [observedLaw_cut, hP]
    exact hL

/-- Complete literal-cut replacement endpoint for the original observed law.
Ranks and labels are explicit; no hidden claim that an arbitrary published
semidirected graph admits the required root-component partition is made. -/
theorem cutImage_eq_rootedFork [Nonempty S]
    (labels : O → Sum (Fin 2) B)
    (rank : Sum A B → ℕ) (forkRank : Sum (Fin 3) B → ℕ)
    (WI : EI → ℝ) (WX : EX → ℝ) (MX : EX → Mat S)
    (H : Subgroup (Equiv.Perm S))
    (hS : 1 < Fintype.card S)
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (hWI : RootBlobEdgeIndexed.WeightsAdmitted N WI)
    (hWX0 : ∀ e, 0 < WX e)
    (hWX1 : ∀ v, (∑ e, if D.target e = v then WX e else 0) = 1)
    (hMX : ∀ e, OpenTransition H (MX e)) :
    cutImage N D labels rank WI WX MX H =
      cutImage RootBlobEdgeIndexed.rootedFork D labels forkRank
        RootBlobEdgeIndexed.forkWeights WX MX H := by
  rw [cutImage_eq_context N D labels rank WI WX MX H,
    cutImage_eq_context RootBlobEdgeIndexed.rootedFork D labels forkRank
      RootBlobEdgeIndexed.forkWeights WX MX H]
  exact RootBlobTreeMarginals.Edge.rootForkContextClaim N WI H _
    hS hG hWI
    (exteriorKernel_admitted D labels WX MX (fun e => le_of_lt (hWX0 e)) hWX1
      (fun e i j => le_of_lt ((hMX e).1.1 i j)) (fun e => (hMX e).1.2))

end RootBlobCutFactorization
