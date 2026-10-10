import G7ActualExactLawResponses
import G7ExactLawRankCompression
import Mathlib.LinearAlgebra.Pi

/-! Actual original-family/reset-programme instantiation of semantic F1/F2.
Finite original-ID rows, genuine pre-source row randomization, finite stochastic
observation channels, and exact full-law responses are constructed here. The
positive row-support and touched original-ID resource costs are derived.
The source class/target and allowed programme family remain supplied inputs;
full effective cofacial admission, independent algebraic source coverage and
QE/CAD selection are NOT proved by this semantic consumer.
Attribution: accepted original G7 F1/F2 and compiler, GPT-6 Astra Pro;
formalization draft by dot / OpenAI, 2026-10-10. UNCOMPILED/UNREVIEWED. -/
namespace GProgram.G7.OriginalFamilyStrategy
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G7.ExactLawResourceGame GProgram.G7.ExactLawRankCompression
open scoped Classical BigOperators

variable {S V E X ID Copy Row Obs Out A T : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype ID] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy] [Nonempty Copy]
variable [Fintype Row] [Fintype Obs] [Fintype Out]

/-- The point s contains its entire original graph/parameter bank. The SAME s
is reused for every deterministic row and every call in its exact-law history.
The ID equivalence is onto ALL actual original hybrids, never a subregistry. -/
structure OriginalFamily (S V E X ID : Type*)
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E] where
  network : S → RootedBinary V E X
  calendar : ∀ s, Calendar (network s).graph
  ids : ∀ s, ID ≃ Hybrid (network s)
  parents : ∀ s, OriginalParentRegistry (network s)
  inheritance : ∀ s, HybridProbabilities (network s)
  common : S → Bool
  rates : S → PositivePairRates E

/-- The finite channel includes both pooled and retained-row-label readouts.
Randomization is selected before biological randomness and does not change the
source bank or carry biological state to the next reset call. -/
structure Programme (Row Obs Out : Type*) where
  weights : PMF Row
  channel : Row → Obs → PMF Out

variable (F : OriginalFamily S V E X ID) (sample : Copy → X)
variable (rows : Row → ID → Option Bool) (observe : Finset (UnrankedTree Copy) → Obs)

noncomputable def rowLaw (s : S) (row : Row) : PMF Obs :=
  (controlledCompletedUnrankedLaw (F.network s) (F.calendar s) sample (F.parents s)
    (F.inheritance s) (fun _ => F.common s) (F.rates s)
    (fun h => rows row ((F.ids s).symm h))).map observe

noncomputable def baseVector (s : S) : Row × Obs → ℝ :=
  fun ro => (rowLaw F sample rows observe s ro.1 ro.2).toReal

noncomputable def programmeLaw (programme : A → Programme Row Obs Out) (s : S) (a : A) : PMF Out :=
  ((programme a).weights).bind fun row =>
    (rowLaw F sample rows observe s row).bind ((programme a).channel row)

noncomputable def coefficient (programme : A → Programme Row Obs Out)
    (a : A) (o : Out) (ro : Row × Obs) : ℝ :=
  ((programme a).weights ro.1).toReal * ((programme a).channel ro.1 ro.2 o).toReal

noncomputable def measurement (programme : A → Programme Row Obs Out)
    (a : A) (o : Out) : Module.Dual ℝ (Row × Obs → ℝ) :=
  ∑ ro, coefficient programme a o ro • LinearMap.proj ro

lemma measurement_apply (programme : A → Programme Row Obs Out)
    (a : A) (o : Out) (z : Row × Obs → ℝ) :
    measurement programme a o z = ∑ ro, coefficient programme a o ro * z ro := by
  simp [measurement,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply]

/-- The affine measurement identity is DERIVED from actual row selection,
actual original source laws and the declared finite output channel. -/
theorem actual_programme_response_linear (programme : A → Programme Row Obs Out)
    (s : S) (a : A) (o : Out) :
    (programmeLaw F sample rows observe programme s a o).toReal =
      measurement programme a o (baseVector F sample rows observe s) := by
  simp only [programmeLaw,bind_probability_real,tsum_fintype,measurement_apply,
    coefficient,baseVector,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro row _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro obs _
  ring

variable [DecidableEq Row] [DecidableEq ID] [DecidableEq A]

/-- Every row with positive programme weight is charged, whether or not that
row label is retained in the response. Zero-weight rows are not charged. -/
noncomputable def programmeSupport (programme : A → Programme Row Obs Out) (a : A) : Finset Row :=
  Finset.univ.filter fun row => (programme a).weights row ≠ 0

def rowSites (row : Row) : Finset ID := Finset.univ.filter fun i => (rows row i).isSome

noncomputable def experiment (programme : A → Programme Row Obs Out)
    (admitted : S → Prop) (target : S → T) (allowed : A → Prop) (budget : Budget) :
    Experiment S A (Out → ℝ) T (List A) where
  admitted := admitted
  target := target
  response := fun s a o => (programmeLaw F sample rows observe programme s a o).toReal
  legal := fun past a => allowed a ∧
    WithinBudget (programmeSupport programme) (rowSites rows) budget (a::past)
  update := fun past a => a::past

lemma original_programme_legal_deletion (programme : A → Programme Row Obs Out)
    (admitted : S → Prop) (target : S → T) (allowed : A → Prop) (budget : Budget)
    {small large : List A} (h : small.Sublist large) (a : A)
    (ha : (experiment F sample rows observe programme admitted target allowed budget).legal large a) :
    (experiment F sample rows observe programme admitted target allowed budget).legal small a := by
  exact ⟨ha.1,trajectory_budget_deletion_closed _ _ budget (h.cons_cons a) ha.2⟩

/-- One finite base coordinate per deterministic original row and finite
unranked outcome bounds informative exact-law calls, even when legal programme
weights range over a continuum. This is a semantic theorem, not a QE run. -/
theorem actual_total_original_strategy_bounded_winning
    (programme : A → Programme Row Obs Out)
    (admitted : S → Prop) (target : S → T) (allowed : A → Prop) (budget : Budget)
    (policy : Policy A Out T)
    (total : ∀ s, admitted s → CorrectRun
      (experiment F sample rows observe programme admitted target allowed budget) policy s [] []) :
    Winning (experiment F sample rows observe programme admitted target allowed budget)
      (Fintype.card (Row × Obs)) [] [] := by
  have result := pointwise_total_strategy_has_finite_informative_horizon
    (experiment F sample rows observe programme admitted target allowed budget)
    (baseVector F sample rows observe) (measurement programme) (fun _ _ => 0)
    (fun s a o => by
      simpa only [experiment,add_zero] using
        actual_programme_response_linear F sample rows observe programme s a o)
    policy (fun h a ha => original_programme_legal_deletion F sample rows observe
      programme admitted target allowed budget h a ha) (fun _ _ => rfl) total
  simpa only [Module.finrank_pi] using result

/-- Semantic actual-source endpoint: an original pointwise-total reset policy
within the concrete path budget has a valid finite-depth identifying plan.
Effective semialgebraic policy selection is a separate formal obligation. -/
theorem actual_total_original_strategy_has_bounded_plan [Nonempty T]
    (programme : A → Programme Row Obs Out)
    (admitted : S → Prop) (target : S → T) (allowed : A → Prop) (budget : Budget)
    (policy : Policy A Out T)
    (total : ∀ s, admitted s → CorrectRun
      (experiment F sample rows observe programme admitted target allowed budget) policy s [] []) :
    ∃ plan : Plan A (Out → ℝ) T (Fintype.card (Row × Obs)),
      Valid (experiment F sample rows observe programme admitted target allowed budget) plan [] [] :=
  winning_has_plan _ _ _ _ (actual_total_original_strategy_bounded_winning
    F sample rows observe programme admitted target allowed budget policy total)

/-- A failed bounded game rules out EVERY pointwise-total identifying policy
at the same actual union-site/row/call trajectory budget. -/
theorem actual_losing_budget_excludes_total_policy
    (programme : A → Programme Row Obs Out)
    (admitted : S → Prop) (target : S → T) (allowed : A → Prop) (budget : Budget)
    (losing : ¬ Winning (experiment F sample rows observe programme admitted target allowed budget)
      (Fintype.card (Row × Obs)) [] []) :
    ¬ ∃ policy : Policy A Out T, ∀ s, admitted s → CorrectRun
      (experiment F sample rows observe programme admitted target allowed budget) policy s [] [] := by
  rintro ⟨policy,total⟩
  exact losing (actual_total_original_strategy_bounded_winning F sample rows observe
    programme admitted target allowed budget policy total)

end GProgram.G7.OriginalFamilyStrategy
