import G6OriginalPopulationSpectralSupport
import G6OriginalPopulationGeneratorBounds
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Ring.GeomSum

/-!
# One positive original-atom list for all capped source generators

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Source adapter for the accepted October 1 G6 Appendix A argument and its
October 10 forest/exposure handoff. This consumes Mathlib Caratheodory and the
checked original Kingman-level support; it introduces no coefficient extractor.
Total alpha mass restores the constant j=2 coordinate omitted from the tail.
The compressed atoms are preimages of the supplied atoms, chosen once before
the original source, entering state, population and destination are quantified.

This is noncomputable positive generator compression. Positive network factors,
same-bank source grafting, semigroup approximation and general Rust refinement
are separate consumers. Draft pending exact sole-scheduler kernel/audit receipt.
-/

namespace GProgram.G6.PositiveGeneratorCompression

open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G6.OriginalPopulationSpectralSupport
open GProgram.G6.OriginalPopulationGeneratorBounds
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceFiniteJumpExpansion
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open scoped BigOperators Classical

noncomputable def tailVector (M : ℕ) (z : ℝ) : Fin (M - 2) → ℝ :=
  fun j => geometricSum ((j.val + 3).choose 2) z

/-- Caratheodory on the supplied tail vectors. Zero total mass uses no atoms.
The strictly positive result is rescaled by the original total mass. -/
theorem positive_tail_compression {n : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (z alpha : Fin n → ℝ) (halpha : ∀ a, 0 ≤ alpha a) :
    ∃ r : ℕ, r ≤ M - 1 ∧ ∃ atom : Fin r → Fin n, ∃ beta : Fin r → ℝ,
      (∀ b, 0 < beta b) ∧ (∑ b, beta b) = ∑ a, alpha a ∧
      ∀ j : Fin (M - 2),
        (∑ a, alpha a * tailVector M (z a) j) =
          ∑ b, beta b * tailVector M (z (atom b)) j := by
  classical
  by_cases hzero : (∑ a, alpha a) = 0
  · have hz : ∀ a, alpha a = 0 := by
      exact fun a => (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => halpha b)).mp hzero a (Finset.mem_univ a)
    refine ⟨0, by omega, (fun b => Fin.elim0 b), (fun b => Fin.elim0 b), ?_, ?_, ?_⟩
    · intro b
      exact Fin.elim0 b
    · simpa using hzero.symm
    · intro j
      simp [hz]
  · let A : ℝ := ∑ a, alpha a
    have hA : 0 < A := by
      have hn : 0 ≤ A := Finset.sum_nonneg (fun a _ => halpha a)
      exact lt_of_le_of_ne hn (Ne.symm hzero)
    have hAn : A ≠ 0 := ne_of_gt hA
    let q : Fin n → ℝ := fun a => alpha a / A
    have hq : ∀ a, 0 ≤ q a := fun a => div_nonneg (halpha a) (le_of_lt hA)
    have hqsum : (∑ a, q a) = 1 := by
      change (∑ a, alpha a / A) = 1
      rw [← Finset.sum_div]
      exact div_self hAn
    let x : Fin (M - 2) → ℝ := ∑ a, q a • tailVector M (z a)
    have hx : x ∈ convexHull ℝ (Set.range (fun a => tailVector M (z a))) := by
      exact (convex_convexHull ℝ _).sum_mem (fun a _ => hq a) hqsum
        (fun a _ => subset_convexHull ℝ _ (Set.mem_range_self a))
    obtain ⟨ι, hι, v, w, hv, hind, hw, hwsum, hwv⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    letI := hι
    have hpre : ∀ i : ι, ∃ a : Fin n, tailVector M (z a) = v i := by
      intro i
      exact hv (Set.mem_range_self i)
    choose a ha using hpre
    let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
    have hspan : Module.finrank ℝ (vectorSpan ℝ (Set.range v)) ≤ M - 2 := by
      simpa using (Submodule.finrank_le (vectorSpan ℝ (Set.range v)))
    have hcard : Fintype.card ι ≤ M - 1 := by
      have hc := hind.card_le_finrank_succ
      omega
    refine ⟨Fintype.card ι, hcard, (fun b => a (e b)),
      (fun b => A * w (e b)), ?_, ?_, ?_⟩
    · intro b
      exact mul_pos hA (hw (e b))
    · calc
        (∑ b : Fin (Fintype.card ι), A * w (e b)) = A * ∑ b, w (e b) :=
          (Finset.mul_sum _ _ _).symm
        _ = A * ∑ i, w i := by rw [e.sum_comp]
        _ = A := by rw [hwsum, mul_one]
        _ = ∑ a, alpha a := rfl
    · intro j
      have hc : (∑ i : ι, w i * v i j) =
          ∑ a : Fin n, q a * tailVector M (z a) j := by
        simpa only [x, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
          congrArg (fun u : Fin (M - 2) → ℝ => u j) hwv
      symm
      calc
        (∑ b : Fin (Fintype.card ι), (A * w (e b)) * tailVector M (z (a (e b))) j) =
            ∑ b : Fin (Fintype.card ι), A * (w (e b) * v (e b) j) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [ha (e b)]
          ring
        _ = A * ∑ b : Fin (Fintype.card ι), w (e b) * v (e b) j :=
          (Finset.mul_sum _ _ _).symm
        _ = A * ∑ i : ι, w i * v i j := by
          exact congrArg (fun t : ℝ => A * t) (e.sum_comp (fun i : ι => w i * v i j))
        _ = A * ∑ a : Fin n, q a * tailVector M (z a) j := by rw [hc]
        _ = ∑ a : Fin n, alpha a * tailVector M (z a) j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          dsimp [q]
          field_simp [hAn]

/-- The omitted two-lineage moment is exactly the total mass. Counts zero and
one have zero geometric moment; all higher moments are tail coordinates. -/
theorem all_level_moments {n r : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (z alpha : Fin n → ℝ) (atom : Fin r → Fin n) (beta : Fin r → ℝ)
    (hmass : (∑ b, beta b) = ∑ a, alpha a)
    (htail : ∀ q : Fin (M - 2),
      (∑ a, alpha a * tailVector M (z a) q) =
        ∑ b, beta b * tailVector M (z (atom b)) q)
    (j : ℕ) (hj : j ≤ M) :
    (∑ a, alpha a * geometricSum (j.choose 2) (z a)) =
      ∑ b, beta b * geometricSum (j.choose 2) (z (atom b)) := by
  by_cases hsmall : j ≤ 1
  · interval_cases j <;> simp [geometricSum]
  · by_cases htwo : j = 2
    · subst j
      simpa [geometricSum] using hmass.symm
    · let q : Fin (M - 2) := ⟨j - 3, by omega⟩
      have hq : q.val + 3 = j := by dsimp [q]; omega
      simpa only [tailVector, hq] using htail q

lemma centeredQuotient_cons (w : ℕ × ℚ) (p : Expr) (z : ℝ) (hz : z < 1) :
    centeredQuotient (w :: p) z =
      -(w.2 : ℝ) * geometricSum w.1 z + centeredQuotient p z := by
  have h := expression_remainder_cons w p z hz
  rw [exprDerivativeAtOne_cons] at h
  linarith

lemma weighted_centered_cons {I : Type*} [Fintype I]
    (z alpha : I → ℝ) (hz : ∀ a, z a < 1) (w : ℕ × ℚ) (p : Expr) :
    (∑ a, alpha a * centeredQuotient (w :: p) (z a)) =
      -(w.2 : ℝ) * (∑ a, alpha a * geometricSum w.1 (z a)) +
        ∑ a, alpha a * centeredQuotient p (z a) := by
  calc
    _ = ∑ a, (-(w.2 : ℝ) * (alpha a * geometricSum w.1 (z a)) +
        alpha a * centeredQuotient p (z a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [centeredQuotient_cons w p (z a) (hz a)]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The same coordinate list works for every raw expression at capped Kingman
levels. No source, forest, population or observation is used to choose it. -/
theorem centered_compression {n r : ℕ} (M : ℕ)
    (z alpha : Fin n → ℝ) (atom : Fin r → Fin n) (beta : Fin r → ℝ)
    (hz : ∀ a, z a < 1)
    (hmom : ∀ j ≤ M,
      (∑ a, alpha a * geometricSum (j.choose 2) (z a)) =
        ∑ b, beta b * geometricSum (j.choose 2) (z (atom b)))
    (p : Expr) (hlevel : ∀ w ∈ p, ∃ j ≤ M, w.1 = j.choose 2) :
    (∑ a, alpha a * centeredQuotient p (z a)) =
      ∑ b, beta b * centeredQuotient p (z (atom b)) := by
  induction p with
  | nil => simp [centeredQuotient]
  | cons w p ih =>
      obtain ⟨j, hj, he⟩ := hlevel w (by simp)
      have hp : ∀ v ∈ p, ∃ j ≤ M, v.1 = j.choose 2 :=
        fun v hv => hlevel v (by simp [hv])
      rw [weighted_centered_cons z alpha hz,
        weighted_centered_cons (fun b => z (atom b)) beta (fun b => hz (atom b)),
        ih hp, he, hmom j hj]

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Entire original full-Code generator equality for any one supplied positive
compression. The entering Code need not be in a canonical encoded image. -/
theorem original_population_compression {n r : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (z alpha : Fin n → ℝ) (atom : Fin r → Fin n) (beta : Fin r → ℝ)
    (hz : ∀ a, z a < 1)
    (hmass : (∑ b, beta b) = ∑ a, alpha a)
    (htail : ∀ q : Fin (M - 2),
      (∑ a, alpha a * tailVector M (z a) q) =
        ∑ b, beta b * tailVector M (z (atom b)) q)
    (N : RootedBinary V E X) {sample : Copy → X} (s d : Code N sample)
    (i : Option E) (hs : CoLocated N s i) (hcap : liveCard s ≤ M) :
    (∑ a, alpha a * populationQuotient N M s d (z a)) =
      ∑ b, beta b * populationQuotient N M s d (z (atom b)) := by
  simp_rw [populationQuotient_eq_centered]
  apply centered_compression M z alpha atom beta hz
    (all_level_moments M hM z alpha atom beta hmass htail)
  intro w hw
  obtain ⟨j, hj, he⟩ := original_kernelExpr_level_support N M s d w hw
  exact ⟨j, hj.trans hcap, he⟩

/-- One positive list is selected before all original rows, not once per row.
All selected survival atoms are original supplied atoms. -/
theorem exists_uniform_original_population_compression {n : ℕ}
    (M : ℕ) (hM : 2 ≤ M) (z alpha : Fin n → ℝ)
    (hz : ∀ a, 0 < z a ∧ z a < 1) (halpha : ∀ a, 0 ≤ alpha a) :
    ∃ r : ℕ, r ≤ M - 1 ∧ ∃ atom : Fin r → Fin n, ∃ beta : Fin r → ℝ,
      (∀ b, 0 < beta b) ∧ (∑ b, beta b) = ∑ a, alpha a ∧
      (∀ q : Fin (M - 2),
        (∑ a, alpha a * tailVector M (z a) q) =
          ∑ b, beta b * tailVector M (z (atom b)) q) ∧
      ∀ (N : RootedBinary V E X) (sample : Copy → X) (s d : Code N sample)
        (i : Option E), CoLocated N s i → liveCard s ≤ M →
        (∑ a, alpha a * populationQuotient N M s d (z a)) =
          ∑ b, beta b * populationQuotient N M s d (z (atom b)) := by
  obtain ⟨r, hr, atom, beta, hb, hm, ht⟩ :=
    positive_tail_compression M hM z alpha halpha
  refine ⟨r, hr, atom, beta, hb, hm, ht, ?_⟩
  intro N sample s d i hs hc
  exact original_population_compression M hM z alpha atom beta (fun a => (hz a).2)
    hm ht N s d i hs hc

#print axioms positive_tail_compression
#print axioms all_level_moments
#print axioms centered_compression
#print axioms original_population_compression
#print axioms exists_uniform_original_population_compression

end GProgram.G6.PositiveGeneratorCompression
