import G7FullEpochSupport
import G7SelectedKernelPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Set.Infinite

/-!
# The actual sparse epoch polynomial identifies the inherited chosen table

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Reuses Mathlib funext_set and the original source-time projection. At one
epoch time1, independently positive original rates -log(x_i) realize every
survival assignment in (0,1)^(Option E). Rational-to-real coefficient mapping
is injective. This binds the entire polynomial and removes admitted source
representative dependence before any slot renaming or word composition.
No independence of physical multi-slot survival coordinates is assumed.
Draft pending fresh sole-scheduler kernel checking and complete owned audit.
-/
namespace GProgram.G7.SelectedEpochTableUniqueness
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceFiniteProjection
open GProgram.G7.FullEpochPolynomial GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.SparseRowProducts GProgram.G7.FullEpochSupport
open GProgram.G7.SelectedKernelPolynomial

noncomputable def inverseLogRates {E : Type*} (x : Option E → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i < 1) : PositivePairRates E where
  edge e := -Real.log (x (some e))
  edge_pos e := neg_pos.mpr (Real.log_neg (hx (some e)).1 (hx (some e)).2)
  ancestral := -Real.log (x none)
  ancestral_pos := neg_pos.mpr (Real.log_neg (hx none).1 (hx none).2)

lemma survival_inverseLogRates {E : Type*} (x : Option E → ℝ)
    (hx : ∀ i, 0 < x i ∧ x i < 1) : survival (inverseLogRates x hx) 1 = x := by
  funext i
  cases i with
  | none =>
      simp only [survival,pairRate,inverseLogRates,NNReal.coe_one,mul_one,neg_neg]
      exact Real.exp_log (hx none).1
  | some e =>
      simp only [survival,pairRate,inverseLogRates,NNReal.coe_one,mul_one,neg_neg]
      exact Real.exp_log (hx (some e)).1

/-- Freely positive original rates at this one time identify every rational
polynomial. The coordinate-box argument is entirely separate from calendars. -/
theorem polynomial_eq_of_single_epoch_evaluations {E : Type*}
    (p q : MvPolynomial (Option E) ℚ)
    (h : ∀ r : PositivePairRates E, evaluate r 1 p = evaluate r 1 q) : p = q := by
  apply MvPolynomial.map_injective (Rat.castHom ℝ) Rat.cast_injective
  apply MvPolynomial.funext_set (fun _ => Set.Ioo (0 : ℝ) 1)
    (fun _ => Set.Ioo_infinite (show (0 : ℝ) < 1 from zero_lt_one))
  intro x hx
  have hbox : ∀ i, 0 < x i ∧ x i < 1 := fun i => hx i (Set.mem_univ i)
  have physical := h (inverseLogRates x hbox)
  unfold evaluate at physical
  rw [survival_inverseLogRates] at physical
  simpa only [MvPolynomial.eval₂_eq_eval_map] using physical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- Exact arbitrary coefficient identity with the original Classical.choose
table, for every admitted literal Code in the same full selected fibre. -/
theorem polynomial_epochRows_eq_epochTable (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample)
    (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (epochRows N s) a) =
      epochTable N (project N Finset.univ s) a := by
  apply polynomial_eq_of_single_epoch_evaluations
  intro r
  rw [epochRows_actual,constructed_source_time_kernel_projection,project_eq]
  exact (actual_selected_epoch_table N (projection N Finset.univ s) a r 1).symm

theorem polynomial_epochCoefficients_eq_epochTable (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample)
    (a : SelectedIndex N sample Finset.univ) :
    polynomial (epochCoefficients N s a) = epochTable N (project N Finset.univ s) a :=
  (polynomial_epochRows N s a).symm.trans (polynomial_epochRows_eq_epochTable N s a)

/-- All literal source-valid representatives of one complete selected view
have the same entire rational sparse coefficient polynomial. -/
theorem polynomial_epochRows_representative_independent (N : RootedBinary V E X)
    {sample : Copy → X} (s d : Code N sample)
    (h : project N Finset.univ s = project N Finset.univ d)
    (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (epochRows N s) a) =
      polynomial (readRows (project N Finset.univ) (epochRows N d) a) := by
  rw [polynomial_epochRows_eq_epochTable,polynomial_epochRows_eq_epochTable,h]

/-- The exact single-epoch identity transports through any shared slot
embedding, including repeated variable coordinates. -/
theorem renamed_epochRows_eq_epochTable {I : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (a : SelectedIndex N sample Finset.univ)
    (i : Option E → I) :
    MvPolynomial.rename i
        (polynomial (readRows (project N Finset.univ) (epochRows N s) a)) =
      MvPolynomial.rename i (epochTable N (project N Finset.univ s) a) :=
  congrArg (MvPolynomial.rename i) (polynomial_epochRows_eq_epochTable N s a)

#print axioms polynomial_eq_of_single_epoch_evaluations
#print axioms polynomial_epochRows_eq_epochTable
#print axioms polynomial_epochCoefficients_eq_epochTable
#print axioms polynomial_epochRows_representative_independent
#print axioms renamed_epochRows_eq_epochTable
end GProgram.G7.SelectedEpochTableUniqueness
