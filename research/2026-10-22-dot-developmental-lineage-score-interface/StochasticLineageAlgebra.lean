/-
Source-only algebraic support for the accepted hand-written stochastic
lineage obstruction. Author: dot (OpenAI), 22 October 2026.

UNELABORATED: no Lean/Lake execution, build certificate, or verification claim.
This file proves a proposed finite expression-tree covariance interface and
records rational data checks. It does NOT construct a branching-process law,
prove nonexplosion, identify the expressions with event-tree densities, prove
measure equality, or formalize the inherited-barcode kernel.
No sorry placeholders or extra axioms are intended.
-/

import Mathlib

universe u v w x y

namespace StochasticLineageAlgebra

inductive EventTree (Time : Type u) (Obs : Type v) where
  | tip (label : Obs)
  | death
  | edge (duration : Time) (subtree : EventTree Time Obs)
  | split (left right : EventTree Time Obs)

structure LikelihoodSystem (Time : Type u) (Obs : Type v)
    (V : Type w) (Scalar : Type x) where
  tip : Obs → V
  death : V
  edge : Time → V → V
  split : V → V → V
  root : V → Scalar

def evaluate {Time : Type u} {Obs : Type v} {V : Type w}
    {Scalar : Type x} (M : LikelihoodSystem Time Obs V Scalar) :
    EventTree Time Obs → V
  | .tip y => M.tip y
  | .death => M.death
  | .edge t tr => M.edge t (evaluate M tr)
  | .split l r => M.split (evaluate M l) (evaluate M r)

structure Intertwines {Time : Type u} {Obs : Type v} {V : Type w}
    {W : Type y} {Scalar : Type x}
    (M : LikelihoodSystem Time Obs V Scalar)
    (N : LikelihoodSystem Time Obs W Scalar) (A : V → W) : Prop where
  tip : ∀ y, N.tip y = A (M.tip y)
  death : N.death = A M.death
  edge : ∀ t v, N.edge t (A v) = A (M.edge t v)
  split : ∀ u v, N.split (A u) (A v) = A (M.split u v)
  root : ∀ v, N.root (A v) = M.root v

theorem evaluate_covariance {Time : Type u} {Obs : Type v}
    {V : Type w} {W : Type y} {Scalar : Type x}
    {M : LikelihoodSystem Time Obs V Scalar}
    {N : LikelihoodSystem Time Obs W Scalar} {A : V → W}
    (h : Intertwines M N A) (tr : EventTree Time Obs) :
    evaluate N tr = A (evaluate M tr) := by
  induction tr with
  | tip y => exact h.tip y
  | death => exact h.death
  | edge t tr ih =>
      simp only [evaluate, ih]
      exact h.edge t (evaluate M tr)
  | split l r ihl ihr =>
      simp only [evaluate, ihl, ihr]
      exact h.split (evaluate M l) (evaluate M r)

theorem root_expression_equality {Time : Type u} {Obs : Type v}
    {V : Type w} {W : Type y} {Scalar : Type x}
    {M : LikelihoodSystem Time Obs V Scalar}
    {N : LikelihoodSystem Time Obs W Scalar} {A : V → W}
    (h : Intertwines M N A) (tr : EventTree Time Obs) :
    N.root (evaluate N tr) = M.root (evaluate M tr) := by
  rw [evaluate_covariance h tr]
  exact h.root (evaluate M tr)

theorem surjective_death_values {I : Type u} {J : Type v}
    {Rate : Type w} (f : I → J) (mu : I → Rate) (nu : J → Rate)
    (onto : Function.Surjective f) (consistent : ∀ i, mu i = nu (f i))
    (x : Rate) : (∃ i, mu i = x) ↔ (∃ j, nu j = x) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨f i, (consistent i).symm.trans hi⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := onto j
    exact ⟨i, (consistent i).trans ((congrArg nu hi).trans hj)⟩

theorem distinct_death_forces_injective_lump {I : Type u} {J : Type v}
    {Rate : Type w} (f : I → J) (mu : I → Rate) (nu : J → Rate)
    (distinct : Function.Injective mu)
    (consistent : ∀ i, mu i = nu (f i)) : Function.Injective f := by
  intro i j hij
  apply distinct
  exact (consistent i).trans ((congrArg nu hij).trans (consistent j).symm)

/- Rational data for the parent-retaining fixed-root example only. -/
namespace ParentRetaining

abbrev V := Fin 3 → ℚ
abbrev Mat := Matrix (Fin 3) (Fin 3) ℚ

def A : Mat := !![3/4, 1/4, 0; 0, 1, 0; 0, 0, 1]
def Ainv : Mat := !![4/3, -1/3, 0; 0, 1, 0; 0, 0, 1]
def Q : Mat := !![-4, 0, 4; 1, -2, 1; 1, 1, -2]
def Qstar : Mat := !![-41/12, 1/6, 13/4; 4/3, -7/3, 1; 4/3, 2/3, -2]
def R : Mat := !![-9, 0, 4; 1, -8, 1; 1, 1, -6]
def Rstar : Mat := !![-26/3, 1/6, 13/4; 4/3, -25/3, 1; 4/3, 2/3, -6]
def mu : V := ![2, 3, 1]
def mustar : V := ![9/4, 3, 1]
def p : V := ![1/3, 1/3, 1/3]
def pstar : V := ![4/9, 2/9, 1/3]
def root : V := ![0, 0, 1]
def coarseX : V := ![1, 1, 0]
def coarseY : V := ![0, 0, 1]

theorem inverse_left : Ainv * A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ainv, A, Matrix.mul_apply, Fin.sum_univ_succ]

theorem inverse_right : A * Ainv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Ainv, A, Matrix.mul_apply, Fin.sum_univ_succ]

theorem killed_intertwiner : Rstar * A = A * R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Rstar, R, A, Matrix.mul_apply, Fin.sum_univ_succ]

theorem death_adapter (i : Fin 3) :
    mustar i = ∑ j : Fin 3, A i j * mu j := by
  fin_cases i <;> norm_num [mustar, mu, A, Fin.sum_univ_succ]

theorem offspring_adapter (j : Fin 3) :
    (∑ i : Fin 3, pstar i * A i j) = p j := by
  fin_cases j <;> norm_num [pstar, p, A, Fin.sum_univ_succ]

theorem root_adapter (j : Fin 3) :
    (∑ i : Fin 3, root i * A i j) = root j := by
  fin_cases j <;> norm_num [root, A, Fin.sum_univ_succ]

theorem normalization (i : Fin 3) : (∑ j : Fin 3, A i j) = 1 := by
  fin_cases i <;> norm_num [A, Fin.sum_univ_succ]

theorem coarseX_adapter (i : Fin 3) :
    (∑ j : Fin 3, A i j * coarseX j) = coarseX i := by
  fin_cases i <;> norm_num [coarseX, A, Fin.sum_univ_succ]

theorem coarseY_adapter (i : Fin 3) :
    (∑ j : Fin 3, A i j * coarseY j) = coarseY i := by
  fin_cases i <;> norm_num [coarseY, A, Fin.sum_univ_succ]

theorem original_missing_edge : Q 0 1 = 0 := by norm_num [Q]
theorem new_edge : Qstar 0 1 = 1/6 := by norm_num [Qstar]

end ParentRetaining
end StochasticLineageAlgebra
