import RootBlobCutFactorization

/-!
# Exact vertex/edge relabeling of original state sums

Author: dot (OpenAI), 22 October 2026.
UNELABORATED source-only continuation. No runtime or verification.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobCutFactorization
namespace RootBlobRelabeling
universe u v w x y z
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {V' : Type w} [Fintype V'] [DecidableEq V']
variable {E : Type x} [Fintype E]
variable {E' : Type y} [Fintype E']
variable {O : Type z} [Fintype O]
variable (N : RootBlobEdgeIndexed.Network V E O)
variable (eV : V ≃ V') (eE : E ≃ E')

/-- Pure bijective relabeling, with every original edge occurrence retained. -/
def relabel : RootBlobEdgeIndexed.Network V' E' O where
  root := eV N.root
  observed := fun o => eV (N.observed o)
  source := fun e => eV (N.source (eE.symm e))
  target := fun e => eV (N.target (eE.symm e))
  rank := fun v => N.rank (eV.symm v)

def assignmentEquiv : (V' → S) ≃ (V → S) where
  toFun := fun a v => a (eV v)
  invFun := fun a v => a (eV.symm v)
  left_inv := by intro a; funext v; simp
  right_inv := by intro a; funext v; simp

theorem vertexFactor_relabel (W : E → ℝ) (π : S → ℝ) (M : E → Mat S)
    (v : V) (a : V' → S) :
    vertexFactor (relabel N eV eE) (fun e => W (eE.symm e)) π
      (fun e => M (eE.symm e)) (eV v) a =
    vertexFactor N W π M v (fun u => a (eV u)) := by
  classical
  by_cases hv : v = N.root
  · subst v
    simp [vertexFactor, relabel]
  · simp only [vertexFactor, relabel, eV.injective.eq_iff,
      hv, if_false]
    apply Fintype.sum_equiv eE.symm
    intro e
    simp only [eV.injective.eq_iff]

theorem assignmentMass_relabel (W : E → ℝ) (π : S → ℝ) (M : E → Mat S)
    (a : V' → S) :
    RootBlobEdgeIndexed.assignmentMass (relabel N eV eE) π
      (fun e => W (eE.symm e)) (fun e => M (eE.symm e)) a =
    RootBlobEdgeIndexed.assignmentMass N π W M (fun v => a (eV v)) := by
  classical
  rw [← product_vertexFactor]
  calc
    (∏ v', vertexFactor (relabel N eV eE) (fun e => W (eE.symm e)) π
        (fun e => M (eE.symm e)) v' a) =
      ∏ v, vertexFactor (relabel N eV eE) (fun e => W (eE.symm e)) π
        (fun e => M (eE.symm e)) (eV v) a := by
          exact (eV.prod_comp _).symm
    _ = ∏ v, vertexFactor N W π M v (fun u => a (eV u)) := by
      apply Finset.prod_congr rfl
      intro v _
      exact vertexFactor_relabel N eV eE W π M v a
    _ = _ := product_vertexFactor N W π M _

theorem observedLaw_relabel (W : E → ℝ) (π : S → ℝ) (M : E → Mat S) :
    RootBlobEdgeIndexed.observedLaw (relabel N eV eE) π
      (fun e => W (eE.symm e)) (fun e => M (eE.symm e)) =
    RootBlobEdgeIndexed.observedLaw N π W M := by
  classical
  funext obs
  unfold RootBlobEdgeIndexed.observedLaw
  apply Fintype.sum_equiv (assignmentEquiv (S := S) eV)
  intro a
  rw [assignmentMass_relabel]
  rfl

theorem transition_admission_relabel (H : Subgroup (Equiv.Perm S)) (M : E → Mat S) :
    (∀ e' : E', OpenTransition H (M (eE.symm e'))) ↔
      ∀ e : E, OpenTransition H (M e) := by
  constructor
  · intro h e
    simpa using h (eE e)
  · intro h e'
    exact h (eE.symm e')

theorem graph_admission_relabel (hG : RootBlobEdgeIndexed.GraphAdmitted N) :
    RootBlobEdgeIndexed.GraphAdmitted (relabel N eV eE) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact hG.1 (eV.injective h)
  · intro o h
    exact hG.2.1 o (eV.injective h)
  · intro e
    simpa [relabel] using hG.2.2.1 (eE.symm e)
  · intro e h
    exact hG.2.2.2.1 (eE.symm e) (eV.injective h)
  · intro v hv
    have hn : eV.symm v ≠ N.root := by
      intro he
      apply hv
      change v ≠ eV N.root at hv
      simpa using congrArg eV he
    obtain ⟨e, he⟩ := hG.2.2.2.2.1 (eV.symm v) hn
    refine ⟨eE e, ?_⟩
    simpa [relabel] using congrArg eV he
  · intro v
    constructor
    · intro h
      have hs : ∀ e, N.source e ≠ eV.symm v := by
        intro e he
        apply h (eE e)
        simpa [relabel] using congrArg eV he
      obtain ⟨o, ho⟩ := (hG.2.2.2.2.2 (eV.symm v)).mp hs
      exact ⟨o, by simpa [relabel] using congrArg eV ho⟩
    · rintro ⟨o, ho⟩ e he
      have he' : N.source (eE.symm e) = N.observed o := by
        apply eV.injective
        exact he.trans ho.symm
      exact ((hG.2.2.2.2.2 (N.observed o)).mpr ⟨o, rfl⟩)
        (eE.symm e) he'

theorem weights_admission_relabel (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W) :
    RootBlobEdgeIndexed.WeightsAdmitted (relabel N eV eE)
      (fun e => W (eE.symm e)) := by
  classical
  constructor
  · intro e
    exact hW.1 (eE.symm e)
  · intro v hv
    have hn : eV.symm v ≠ N.root := by
      intro he
      apply hv
      simpa [relabel] using congrArg eV he
    calc
      (∑ e, if (relabel N eV eE).target e = v then W (eE.symm e) else 0) =
        ∑ e, if N.target e = eV.symm v then W e else 0 := by
          apply Fintype.sum_equiv eE.symm
          intro e
          simp only [relabel, eV.eq_symm_apply.symm]
      _ = 1 := hW.2 (eV.symm v) hn

end RootBlobRelabeling
