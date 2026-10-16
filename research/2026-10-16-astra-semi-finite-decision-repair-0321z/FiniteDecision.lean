import Semi.Core.Observation
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Fintype.OfMap
import Mathlib.Tactic.Linarith

/-!
Finite randomized decisions, without a sampling channel. SOURCE CANDIDATE.
Actions are the entire declared finite action type. In the diffraction instance
that type is ALL source orbits, not just the current observation fibre.
-/

namespace Semi.Statistics

open Finset
variable {X O A : Type*} [Fintype A]

abbrev RandomizedAction (A : Type*) [Fintype A] := stdSimplex ℝ A
abbrev DecisionRule (O A : Type*) [Fintype A] := O → RandomizedAction A

noncomputable def risk (loss : A → X → ℝ) (q : RandomizedAction A) (x : X) : ℝ :=
  ∑ a, q a * loss a x

theorem risk_nonneg (loss : A → X → ℝ) (q : RandomizedAction A) (x : X)
    (h : ∀ a, 0 ≤ loss a x) : 0 ≤ risk loss q x :=
  Finset.sum_nonneg (fun a _ => mul_nonneg (stdSimplex.zero_le q a) (h a))

theorem risk_le_one (loss : A → X → ℝ) (q : RandomizedAction A) (x : X)
    (h : ∀ a, loss a x ≤ 1) : risk loss q x ≤ 1 := by
  calc
    risk loss q x ≤ ∑ a, q a * 1 := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (h a) (stdSimplex.zero_le q a)
    _ = 1 := by simp

/-- A two-state separation lower bound, for the SAME randomized action. -/
theorem pair_risk_lower_bound (loss : A → X → ℝ) (q : RandomizedAction A)
    (x y : X) (δ : ℝ) (h : ∀ a, δ ≤ loss a x + loss a y) :
    δ ≤ risk loss q x + risk loss q y := by
  calc
    δ = ∑ a, q a * δ := by rw [← Finset.sum_mul, stdSimplex.sum_eq_one q, one_mul]
    _ ≤ ∑ a, q a * (loss a x + loss a y) := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (h a) (stdSimplex.zero_le q a)
    _ = risk loss q x + risk loss q y := by simp [risk, mul_add, Finset.sum_add_distrib]

theorem indistinguishable_pair_lower_bound (observe : X → O) (loss : A → X → ℝ)
    (rule : DecisionRule O A) (x y : X) (same : observe x = observe y)
    (δ : ℝ) (h : ∀ a, δ ≤ loss a x + loss a y) :
    δ / 2 ≤ max (risk loss (rule (observe x)) x) (risk loss (rule (observe y)) y) := by
  have hp := pair_risk_lower_bound loss (rule (observe x)) x y δ h
  rw [← same]
  have hx := le_max_left (risk loss (rule (observe x)) x) (risk loss (rule (observe x)) y)
  have hy := le_max_right (risk loss (rule (observe x)) x) (risk loss (rule (observe x)) y)
  linarith

theorem continuous_risk (loss : A → X → ℝ) (x : X) :
    Continuous (fun q : RandomizedAction A => risk loss q x) := by
  apply continuous_finsetSum
  intro a _
  have hcoord : Continuous (fun q : RandomizedAction A => (q a : ℝ)) :=
    (continuous_apply a).comp continuous_subtype_val
  exact hcoord.mul_const (loss a x)

section Minimax
variable [Fintype X] [Nonempty A]

noncomputable def fibreStates (observe : X → O) (o : O) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => observe x = o)

theorem fibreStates_nonempty (observe : X → O) (o : Set.range observe) :
    (fibreStates observe o.1).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := o.2
  exact ⟨x, by simp [fibreStates, hx]⟩

/-- Worst expected loss over an exact-data fibre; optimization ranges over
the full action simplex, with no requirement that actions lie in that fibre. -/
noncomputable def fibreWorstRisk (observe : X → O) (loss : A → X → ℝ)
    (o : Set.range observe) (q : RandomizedAction A) : ℝ :=
  (fibreStates observe o.1).sup' (fibreStates_nonempty observe o) (risk loss q)

theorem continuous_fibreWorstRisk (observe : X → O) (loss : A → X → ℝ)
    (o : Set.range observe) : Continuous (fibreWorstRisk observe loss o) := by
  classical
  exact Continuous.finset_sup'_apply (fibreStates_nonempty observe o)
    (fun x _ => continuous_risk loss x)

theorem exists_fibre_minimizer (observe : X → O) (loss : A → X → ℝ)
    (o : Set.range observe) :
    ∃ q : RandomizedAction A, ∀ r : RandomizedAction A,
      fibreWorstRisk observe loss o q ≤ fibreWorstRisk observe loss o r := by
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (RandomizedAction A)).Nonempty)
    (continuous_fibreWorstRisk observe loss o).continuousOn
  exact ⟨q, fun r => (isMinOn_iff.mp hq) r (Set.mem_univ r)⟩

noncomputable def fibreMinimizer (observe : X → O) (loss : A → X → ℝ)
    (o : Set.range observe) : RandomizedAction A :=
  Classical.choose (exists_fibre_minimizer observe loss o)

noncomputable def fibreMinimaxRadius (observe : X → O) (loss : A → X → ℝ)
    (o : Set.range observe) : ℝ :=
  fibreWorstRisk observe loss o (fibreMinimizer observe loss o)

theorem fibreMinimaxRadius_le (observe : X → O) (loss : A → X → ℝ)
    (o : Set.range observe) (q : RandomizedAction A) :
    fibreMinimaxRadius observe loss o ≤ fibreWorstRisk observe loss o q :=
  Classical.choose_spec (exists_fibre_minimizer observe loss o) q

theorem fibreMinimaxRadius_pair_lower_bound (observe : X → O) (loss : A → X → ℝ)
    (o : Set.range observe) (x y : X) (hx : observe x = o.1) (hy : observe y = o.1)
    (δ : ℝ) (h : ∀ a, δ ≤ loss a x + loss a y) :
    δ / 2 ≤ fibreMinimaxRadius observe loss o := by
  classical
  let q := fibreMinimizer observe loss o
  have hp := pair_risk_lower_bound loss q x y δ h
  have hxm : x ∈ fibreStates observe o.1 := by simp [fibreStates, hx]
  have hym : y ∈ fibreStates observe o.1 := by simp [fibreStates, hy]
  have hxr : risk loss q x ≤ fibreWorstRisk observe loss o q := Finset.le_sup' _ hxm
  have hyr : risk loss q y ≤ fibreWorstRisk observe loss o q := Finset.le_sup' _ hym
  change δ / 2 ≤ fibreWorstRisk observe loss o q
  linarith

noncomputable def observationRangeFintype (observe : X → O) : Fintype (Set.range observe) := by
  classical
  exact Fintype.ofSurjective (fun x => (⟨observe x, ⟨x, rfl⟩⟩ : Set.range observe)) (by
    rintro ⟨o, ⟨x, hx⟩⟩
    exact ⟨x, Subtype.ext hx⟩)

section Global
variable [Nonempty X]

theorem observationRange_nonempty (observe : X → O) : Nonempty (Set.range observe) :=
  ⟨⟨observe (Classical.choice inferInstance), ⟨_, rfl⟩⟩⟩

/-- Worst risk of a rule on realizable observations, with all source states
and the entire action space retained. -/
noncomputable def exactDataWorstRisk (observe : X → O) (loss : A → X → ℝ)
    (rule : Set.range observe → RandomizedAction A) : ℝ := by
  classical
  letI := observationRangeFintype observe
  letI := observationRange_nonempty observe
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun o => fibreWorstRisk observe loss o (rule o))

/-- The maximum, over exact observation fibres, of the randomized minimax
radius. Half a fibre diameter is a lower bound, not this definition. -/
noncomputable def exactDataMinimaxFloor (observe : X → O) (loss : A → X → ℝ) : ℝ :=
  exactDataWorstRisk observe loss (fibreMinimizer observe loss)

theorem exactDataMinimaxFloor_le_rule (observe : X → O) (loss : A → X → ℝ)
    (rule : Set.range observe → RandomizedAction A) :
    exactDataMinimaxFloor observe loss ≤ exactDataWorstRisk observe loss rule := by
  classical
  letI := observationRangeFintype observe
  letI := observationRange_nonempty observe
  apply (Finset.sup'_le_iff Finset.univ_nonempty _).2
  intro o _
  exact (fibreMinimaxRadius_le observe loss o (rule o)).trans
    (Finset.le_sup' _ (Finset.mem_univ o))

end Global

end Minimax
end Semi.Statistics
