import SocialScience.Identifiability

namespace SocialScience.Causality

/-- Outcome indexed by treatment and an unobserved binary background variable. -/
structure BinaryModel where
  outcome : Bool → Bool → Bool

def treatmentEffect : BinaryModel := ⟨fun treatment _ => treatment⟩
def commonCause : BinaryModel := ⟨fun _ background => background⟩

/-- Observational assignment is treatment = background in both candidate models. -/
def observed (model : BinaryModel) (background : Bool) : Bool × Bool :=
  (background, model.outcome background background)

def indicator (b : Bool) : Int := if b then 1 else 0

/-- Twice the average treatment effect if background is uniformly distributed. -/
def effectNumerator (model : BinaryModel) : Int :=
  indicator (model.outcome true false) + indicator (model.outcome true true) -
  (indicator (model.outcome false false) + indicator (model.outcome false true))

theorem observational_equivalence : observed treatmentEffect = observed commonCause := by
  funext background
  rfl

theorem intervention_disagreement :
    treatmentEffect.outcome true false ≠ commonCause.outcome true false := by decide

theorem treatment_effect_numerator : effectNumerator treatmentEffect = 2 := by decide

theorem common_cause_numerator : effectNumerator commonCause = 0 := by decide

/-- No rule using only this observational function recovers every candidate's effect. -/
theorem no_universal_observational_estimator :
    ¬ ∃ estimate : (Bool → Bool × Bool) → Int,
      ∀ model, estimate (observed model) = effectNumerator model := by
  rintro ⟨estimate, correct⟩
  have same := congrArg estimate observational_equivalence
  have first := correct treatmentEffect
  have second := correct commonCause
  rw [treatment_effect_numerator] at first
  rw [common_cause_numerator] at second
  omega

/-- Complete exact response information suffices within this deterministic model class. -/
theorem all_responses_identify (first second : BinaryModel)
    (same : ∀ treatment background,
      first.outcome treatment background = second.outcome treatment background) :
    first = second := by
  cases first with
  | mk f =>
    cases second with
    | mk g =>
      have eq : f = g := by
        funext treatment background
        exact same treatment background
      cases eq
      rfl

end SocialScience.Causality
