/-
Finite-cube interpolation for the all-channel proof route.
Author: dot (OpenAI), working with Nolan, 17 October 2026.
UNCOMPILED SOURCE CANDIDATE. No claim of Lean acceptance is made.
No target inequality, matrix decomposition, or physical claim is assumed here.
This module only proves the elementary separately-affine cube lemma.
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace NanowireAllChannel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Endpoint interpolation in each coordinate, with all other coordinates fixed. -/
def CoordinateAffine (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ (x : ι → ℝ) (i : ι) (t : ℝ),
    f (Function.update x i t) =
      ((1 - t) / 2) * f (Function.update x i (-1)) +
      ((1 + t) / 2) * f (Function.update x i 1)

def InCube (x : ι → ℝ) : Prop := ∀ i, -1 ≤ x i ∧ x i ≤ 1

def CubeVertex (x : ι → ℝ) : Prop := ∀ i, x i = -1 ∨ x i = 1

/-- A separately affine real function that is nonnegative at every cube vertex
is nonnegative on the whole cube. This theorem has no dimension cutoff. -/
theorem nonneg_on_cube_of_vertices
    {f : (ι → ℝ) → ℝ} (hf : CoordinateAffine f)
    (hv : ∀ x, CubeVertex x → 0 ≤ f x)
    {x : ι → ℝ} (hx : InCube x) : 0 ≤ f x := by
  classical
  have haux : ∀ s : Finset ι, ∀ y : ι → ℝ,
      (∀ i, i ∉ s → y i = -1 ∨ y i = 1) → InCube y → 0 ≤ f y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy _
      exact hv y (fun i => hy i (Finset.not_mem_empty i))
    | @insert i s hi ih =>
      intro y hy hycube
      have hb (t : ℝ) (ht : t = -1 ∨ t = 1) :
          0 ≤ f (Function.update y i t) := by
        apply ih
        · intro j hjs
          by_cases hji : j = i
          · subst j
            simpa using ht
          · have hjnot : j ∉ insert i s := by simp [hji, hjs]
            simpa [Function.update, hji, Ne.symm hji] using hy j hjnot
        · intro j
          by_cases hji : j = i
          · subst j
            rcases ht with rfl | rfl <;> norm_num
          · simpa [Function.update, hji, Ne.symm hji] using hycube j
      have hm : 0 ≤ f (Function.update y i (-1)) := hb (-1) (Or.inl rfl)
      have hp : 0 ≤ f (Function.update y i 1) := hb 1 (Or.inr rfl)
      have heq := hf y i (y i)
      simp only [Function.update_eq_self] at heq
      rw [heq]
      exact add_nonneg
        (mul_nonneg (by linarith [(hycube i).2]) hm)
        (mul_nonneg (by linarith [(hycube i).1]) hp)
  exact haux Finset.univ x (by simp) hx

/-- Scalar constants satisfy the exact endpoint identity. -/
theorem coordinateAffine_const (c : ℝ) :
    CoordinateAffine (fun _ : ι → ℝ => c) := by
  intro x i t
  ring

/-- The cube certificate is stable under addition. -/
theorem CoordinateAffine.add {f h : (ι → ℝ) → ℝ}
    (hf : CoordinateAffine f) (hh : CoordinateAffine h) :
    CoordinateAffine (fun x => f x + h x) := by
  intro x i t
  rw [hf x i t, hh x i t]
  ring

/-- The cube certificate is stable under arbitrary real scaling. -/
theorem CoordinateAffine.smul {f : (ι → ℝ) → ℝ}
    (hf : CoordinateAffine f) (c : ℝ) :
    CoordinateAffine (fun x => c * f x) := by
  intro x i t
  rw [hf x i t]
  ring

/-- A square-free quadratic monomial has the required coordinate affinity. -/
theorem coordinateAffine_pair (j k : ι) (hjk : j ≠ k) :
    CoordinateAffine (fun x : ι → ℝ => x j * x k) := by
  intro x i t
  by_cases hji : j = i <;> by_cases hki : k = i
  all_goals simp_all [Function.update]
  all_goals ring

/-- The product of all distinct coordinates is separately affine. -/
theorem coordinateAffine_prod :
    CoordinateAffine (fun x : ι → ℝ => ∏ j, x j) := by
  classical
  intro x i t
  have hp (a : ℝ) :
      (∏ j, Function.update x i a j) =
        a * ∏ j ∈ Finset.univ.erase i, x j := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => Function.update x i a j) (Finset.mem_univ i)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update, hji, Ne.symm hji]
  rw [hp t, hp (-1), hp 1]
  ring

/-- Finite sums preserve coordinate affinity. -/
theorem coordinateAffine_sum {κ : Type*} [Fintype κ]
    {f : κ → (ι → ℝ) → ℝ} (hf : ∀ k, CoordinateAffine (f k)) :
    CoordinateAffine (fun x => ∑ k, f k x) := by
  intro x i t
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun k _ => hf k x i t)
  simpa only [Finset.sum_add_distrib, Finset.mul_sum] using h

/-- The exact scalar form arising after the real SVD trace expansion is
separately affine. Matrix-to-scalar binding remains a separate obligation. -/
theorem coordinateAffine_det_quadratic
    (d c : ℝ) (a : ι → ι → ℝ) (ha : ∀ i, a i i = 0) :
    CoordinateAffine (fun x : ι → ℝ =>
      d * (∏ i, x i) + c + ∑ i, ∑ j, a i j * (x i * x j)) := by
  apply CoordinateAffine.add
  · exact (coordinateAffine_prod.smul d).add (coordinateAffine_const c)
  · apply coordinateAffine_sum
    intro i
    apply coordinateAffine_sum
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [ha i, zero_mul] using (coordinateAffine_const (ι := ι) 0)
    · exact (coordinateAffine_pair i j hij).smul (a i j)

end NanowireAllChannel
