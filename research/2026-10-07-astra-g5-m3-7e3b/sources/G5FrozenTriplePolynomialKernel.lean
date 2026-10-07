import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Frozen three-label partition kernel and positive-mixture support
Contributor: GPT-6 Astra Pro, G5 session 7E3B, 2026-10-07.
STATUS: UNCHECKED. No elaboration, kernel or axiom report has been executed.

Fin 5 codes the five partitions: 0 = 0|1|2, 1 = 01|2, 2 = 02|1,
3 = 12|0, 4 = 012. It does NOT encode hidden population or routing IDs.
For a frozen hidden occupancy and q = exp(-rate * duration), the formulas
below are the standard three-lineage Kingman transition probabilities.
The symbolic ODE check is separate from this uncompiled Lean source.

This module is only the explicit polynomial/finite-mixture port. Binding its
kernel to the actual source's conditional event-free genealogy law, deriving
positive posterior seed weights, analytic continuation of the observed germ,
and full chronological cluster decoding remain named external obligations.
In particular, an arbitrary array called a kernel is not a source law by name.
-/
namespace GProgram.G5.FrozenTriplePolynomialKernel
open Filter
open scoped BigOperators Topology

noncomputable def discrete3 (q : ℝ) : ℝ := q ^ 3
noncomputable def pair3 (q : ℝ) : ℝ := (q - q ^ 3) / 2
noncomputable def together3 (q : ℝ) : ℝ := 1 - 3 * pair3 q - discrete3 q

lemma pair3_factor (q : ℝ) : pair3 q = q * (1 - q) * (1 + q) / 2 := by
  unfold pair3
  ring

lemma together3_factor (q : ℝ) : together3 q = (1 - q) ^ 2 * (q + 2) / 2 := by
  unfold together3 pair3 discrete3
  ring

lemma three_lineage_masses_sum (q : ℝ) :
    discrete3 q + pair3 q + pair3 q + pair3 q + together3 q = 1 := by
  unfold together3
  ring

lemma three_lineage_masses_nonnegative {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ discrete3 q ∧ 0 ≤ pair3 q ∧ 0 ≤ together3 q := by
  have hm : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  refine ⟨pow_nonneg hq 3, ?_, ?_⟩
  · rw [pair3_factor]
    positivity
  · rw [together3_factor]
    positivity

/-- The row starts with three distinct gene ancestors in a fixed hidden
occupancy. In occupancy 4 each specified first pair has mass pair3 q. -/
noncomputable def row (q : ℝ) (occupancy gene : Fin 5) : ℝ :=
  if occupancy = 0 then
    if gene = 0 then 1 else 0
  else if occupancy = 4 then
    if gene = 0 then discrete3 q else if gene = 4 then together3 q else pair3 q
  else
    if gene = 0 then q else if gene = occupancy then 1 - q else 0

lemma row_nonnegative {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (occupancy gene : Fin 5) : 0 ≤ row q occupancy gene := by
  have hm := three_lineage_masses_nonnegative hq hq1
  unfold row
  split_ifs <;> first | positivity | exact hm.1 | exact hm.2.1 | exact hm.2.2 |
    exact sub_nonneg.mpr hq1

lemma row_sum (q : ℝ) (occupancy : Fin 5) :
    (∑ gene : Fin 5, row q occupancy gene) = 1 := by
  fin_cases occupancy <;>
    simp [row, Fin.sum_univ_succ, together3, pair3, discrete3] <;> ring

lemma row_initial (occupancy gene : Fin 5) :
    row 1 occupancy gene = if gene = 0 then 1 else 0 := by
  fin_cases occupancy <;> fin_cases gene <;>
    norm_num [row, together3, pair3, discrete3]

lemma row_endpoint (occupancy gene : Fin 5) :
    row 0 occupancy gene = if gene = occupancy then 1 else 0 := by
  fin_cases occupancy <;> fin_cases gene <;>
    norm_num [row, together3, pair3, discrete3]

lemma row_continuous (occupancy gene : Fin 5) :
    Continuous (fun q : ℝ => row q occupancy gene) := by
  unfold row together3 pair3 discrete3
  split_ifs <;> fun_prop

/-- Continuity converts decay of q into the frozen occupancy endpoint. -/
lemma row_tendsto_endpoint {A : Type*} (l : Filter A) (q : A → ℝ)
    (hq : Tendsto q l (𝓝 0)) (occupancy gene : Fin 5) :
    Tendsto (fun a => row (q a) occupancy gene) l
      (𝓝 (if gene = occupancy then 1 else 0)) := by
  have h := ((row_continuous occupancy gene).tendsto 0).comp hq
  simpa only [Function.comp_def, row_endpoint] using h

section FiniteMixtures
variable {Seed : Type*} [Fintype Seed]

/-- No factorization assumption on weights. Survival conditioning may make
posterior route weights dependent even when their feasible support is Cartesian. -/
noncomputable def mixture (weight : Seed → ℝ) (occupancy : Seed → Fin 5)
    (q : Seed → ℝ) (gene : Fin 5) : ℝ :=
  ∑ a, weight a * row (q a) (occupancy a) gene

noncomputable def occupancyMass (weight : Seed → ℝ) (occupancy : Seed → Fin 5)
    (gene : Fin 5) : ℝ :=
  ∑ a, if occupancy a = gene then weight a else 0

lemma mixture_at_endpoint (weight : Seed → ℝ) (occupancy : Seed → Fin 5)
    (gene : Fin 5) :
    mixture weight occupancy (fun _ => 0) gene = occupancyMass weight occupancy gene := by
  classical
  apply Finset.sum_congr rfl
  intro a _
  rw [row_endpoint]
  by_cases h : occupancy a = gene
  · simp [h]
  · simp [h, Ne.symm h]

/-- A positive finite posterior mixture loses no supported hidden occupancy.
Strict positivity is essential; this is not a uniform statistical lower bound. -/
lemma occupancy_mass_positive_iff (weight : Seed → ℝ) (occupancy : Seed → Fin 5)
    (hw : ∀ a, 0 < weight a) (gene : Fin 5) :
    0 < occupancyMass weight occupancy gene ↔ ∃ a, occupancy a = gene := by
  classical
  constructor
  · intro hp
    by_contra hn
    have hz : occupancyMass weight occupancy gene = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact if_neg (fun h => hn ⟨a, h⟩)
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  · rintro ⟨a, ha⟩
    have hnonneg : ∀ b ∈ (Finset.univ : Finset Seed),
        0 ≤ (if occupancy b = gene then weight b else 0) := by
      intro b _
      split_ifs
      · exact (hw b).le
      · exact le_rfl
    have hle := Finset.single_le_sum hnonneg (Finset.mem_univ a)
    have hpositive : 0 < (if occupancy a = gene then weight a else 0) := by
      rw [if_pos ha]
      exact hw a
    exact lt_of_lt_of_le hpositive hle

end FiniteMixtures

#print axioms three_lineage_masses_nonnegative
#print axioms row_sum
#print axioms row_tendsto_endpoint
#print axioms mixture_at_endpoint
#print axioms occupancy_mass_positive_iff
end GProgram.G5.FrozenTriplePolynomialKernel
