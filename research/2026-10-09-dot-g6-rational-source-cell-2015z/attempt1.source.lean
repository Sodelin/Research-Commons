import NaturalCellAffineCompiler
import UnifiedLean.G6.RationalResidualCertificate

/-! Exact rational witnesses in supplied original natural cells. This is a
source consumer of the proved affine decider, not a witness-returning algorithm.
The chart's legal exposure interpretation and outer coverage remain separate.
Contributor: dot, 2026-10-09. -/
namespace UnifiedLean.G6.RationalNaturalCellWitness
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.StrictAffineElimination
open scoped BigOperators

lemma row_cast {n : ℕ} (r : Row n) (q : Fin n → ℚ) :
    r.Holds (fun i => (q i : ℝ)) ↔ r.Holds q := by
  have he : r.eval (fun i => (q i : ℝ)) = (r.eval q : ℚ) := by
    simp [Row.eval]
  unfold Row.Holds Rel
  rw [he]
  cases r.strict <;> simp

variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)

/-- One rational vector satisfies every source constraint simultaneously. -/
theorem rational_bank_conditions (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval)
    (h : originalCellFeasible N chronology rows coins) :
    ∃ q : Fin n → ℚ, BankConditions N chronology rows coins
      (agesOf N layout (fun i => (q i : ℝ)))
      (inverseRatesOf N layout (fun i => (q i : ℝ)))
      (coinsOf N layout (fun i => (q i : ℝ))) := by
  have hf := (inverse_cell_iff_compiled N layout chronology rows coins).mp
    ((original_cell_iff_inverse N chronology rows coins).mp h)
  obtain ⟨q,hq⟩ := rational_witness_of_real _ hf
  refine ⟨q, (compileCell_correct N layout chronology rows coins _).mp ?_⟩
  intro r hr
  exact (row_cast r q).mpr (hq r hr)

/-- The rational witness is a genuine Calendar, positive physical rate bank,
and original-site inheritance bank, inside the SAME supplied cell. -/
theorem rational_original_source (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval)
    (h : originalCellFeasible N chronology rows coins) :
    ∃ (c : Calendar N.graph) (r : PositivePairRates E) (g : HybridProbabilities N),
      (∀ x, c.age (N.leaf x) = 0) ∧
      (∀ j, (chronology j).holds c.age) ∧
      (∀ h, (coins h).contains (g.gamma h)) ∧
      (∀ i, (rows i).cell.contains
        (pairRate r (rows i).population * (rows i).duration c.age)) ∧
      (∀ v, ∃ a : ℚ, c.age v = a) ∧
      (∀ e, ∃ a : ℚ, pairRate r e = a) ∧
      (∀ h, ∃ a : ℚ, g.gamma h = a) := by
  obtain ⟨q,hedge,htip,hu,hg0,hg1,horder,hcoins,hrows⟩ :=
    rational_bank_conditions N layout chronology rows coins h
  let a := agesOf N layout (fun i => (q i : ℝ))
  let u := inverseRatesOf N layout (fun i => (q i : ℝ))
  let gamma := coinsOf N layout (fun i => (q i : ℝ))
  refine ⟨calendarOfAges N a hedge, ratesOfInverse u hu,
    inheritanceOfValues N gamma hg0 hg1, htip,horder,hcoins,
    reconstructed_bank_satisfies rows a u hu hrows, ?_, ?_, ?_⟩
  · intro v
    exact ⟨q (layout (.inl v)), rfl⟩
  · intro e
    refine ⟨(q (layout (.inr (.inl e))))⁻¹, ?_⟩
    simp [constructed_pair_rate, u, inverseRatesOf]
  · intro h
    exact ⟨q (layout (.inr (.inr h))), rfl⟩

/-- Literal node/cut endpoints of the same rational witness remain rational. -/
theorem atom_rational (a : V → ℝ) (ha : ∀ v, ∃ q : ℚ, a v = q)
    (atom : AgeAtom V) : ∃ q : ℚ, atom.eval a = q := by
  cases atom with
  | node v => exact ha v
  | fixed q => exact ⟨q, rfl⟩

theorem exposure_duration_rational (a : V → ℝ)
    (ha : ∀ v, ∃ q : ℚ, a v = q) (e : Exposure V E) :
    ∃ d : ℚ, e.duration a = d := by
  obtain ⟨qo,ho⟩ := atom_rational a ha e.older
  obtain ⟨qy,hy⟩ := atom_rational a ha e.younger
  refine ⟨qo-qy, ?_⟩
  simp [Exposure.duration, ho, hy]

open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.RationalResidualCertificate
open UnifiedLean.G6.RationalCertificate
open UnifiedLean.G6.ResidualPrefix
open UnifiedLean.G6.FiniteProbability
open scoped NNReal
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- A rational source witness has a rational global Poisson mean on every
rational-duration epoch. The mean is derived from the actual source bound. -/
theorem rational_source_mean (r : PositivePairRates E)
    (hr : ∀ e, ∃ a : ℚ, pairRate r e = a)
    (d : ℚ) (hd : 0 ≤ d) :
    ∃ q : ℚ, 0 ≤ q ∧
      ((globalClockRate (Copy := Copy) r *
        (⟨(d : ℝ), by exact_mod_cast hd⟩ : ℝ≥0) : ℝ≥0) : ℝ) = q := by
  classical
  choose a ha using hr
  let q : ℚ := (1 + ∑ e : Option E, a e) *
    (1 + (Fintype.card Copy : ℚ)^2) * d
  have he : ((globalClockRate (Copy := Copy) r *
      (⟨(d : ℝ), by exact_mod_cast hd⟩ : ℝ≥0) : ℝ≥0) : ℝ) = (q : ℝ) := by
    simp only [NNReal.coe_mul, globalClockRate, globalRateBound]
    simp [q, ha]
  refine ⟨q, ?_, he⟩
  have hn := (globalClockRate (Copy := Copy) r *
    (⟨(d : ℝ), by exact_mod_cast hd⟩ : ℝ≥0)).coe_nonneg
  rw [he] at hn
  exact_mod_cast hn

/-- Existing normalized rational count coefficients certify every actual
source state at the selected rational witness. No mean-equality oracle remains. -/
theorem rational_source_epoch_certificate {sample : Copy → X}
    (r : PositivePairRates E) (hr : ∀ e, ∃ a : ℚ, pairRate r e = a)
    (d ε : ℚ) (hd : 0 ≤ d) (hε : 0 < ε) :
    ∃ q : ℚ, ∃ hq : 0 ≤ q, ∀ s : Code N sample,
      tv (fun z => (sourceTimeKernel N r
        (⟨(d : ℝ), by exact_mod_cast hd⟩ : ℝ≥0) s z).toReal)
        (residualSourceVector N r
          (⟨(d : ℝ), by exact_mod_cast hd⟩ : ℝ≥0)
          (cutoff q ε hq hε) s) ≤ (ε : ℝ) := by
  obtain ⟨q,hq,he⟩ := rational_source_mean (Copy := Copy) r hr d hd
  exact ⟨q,hq, fun s => actual_source_residual_tv_cutoff N r _ q ε hq hε he s⟩

#print axioms rational_bank_conditions
#print axioms rational_original_source
#print axioms rational_source_mean
#print axioms rational_source_epoch_certificate
end UnifiedLean.G6.RationalNaturalCellWitness
