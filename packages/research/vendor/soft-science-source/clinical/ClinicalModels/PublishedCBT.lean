import Std

/-!
A limited formal reconstruction of the observation and transition fragment in
Smith, Moutoussis and Bilek (2021), DOI 10.1038/s41598-021-89047-0.
Upstream CBT_model.m at 82a0a3d75b0bdc08d2b78cdf2201d7aa626c27a3.
This file does not implement SPM inference, learning, or therapeutic outcomes.
-/
namespace ClinicalModels.PublishedCBT

inductive Phase where
  | start | stimulus | approach | interact | avoid | safetyCost
  deriving DecidableEq, Repr

inductive Affect where
  | positive | negative | harm
  deriving DecidableEq, Repr

/-- Deterministic columns of B{1}(:,:,1), upstream lines 173-178. -/
def approachStep : Phase → Phase
  | .start => .stimulus
  | .stimulus => .approach
  | _ => .interact

/-- Deterministic columns of B{1}(:,:,2), upstream lines 181-186. -/
def avoidStep : Phase → Phase
  | .start => .stimulus
  | .stimulus => .avoid
  | _ => .safetyCost

/-- Four time points, as configured by upstream T = 4. -/
def trajectory (step : Phase → Phase) : List Phase :=
  [.start, step .start, step (step .start), step (step (step .start))]

/-- Outcome of A{3} with a spider present, from upstream lines 121-129. -/
def affect (dangerous : Bool) : Phase → Affect
  | .start | .stimulus => .positive
  | .approach => if dangerous then .negative else .positive
  | .interact => if dangerous then .harm else .positive
  | .avoid | .safetyCost => .negative

/-- A{1}: the spider is observed after the initial phase. -/
def seesSpider (phase : Phase) : Bool := phase != .start

/-- A{2} with a spider present: high arousal at stimulus and avoidance. -/
def highArousal : Phase → Bool
  | .stimulus | .avoid => true
  | _ => false

/-- A{4} reports the phase itself. All four modalities are included. -/
def observation (dangerous : Bool) (phase : Phase) : Bool × Bool × Affect × Phase :=
  (seesSpider phase, highArousal phase, affect dangerous phase, phase)

def observedTrajectory (dangerous : Bool) (step : Phase → Phase) :=
  (trajectory step).map (observation dangerous)

/-- Three outcome weights, proportional to a{3} before its common factor 5.
    Scale is 10*u; CABi is c/(10*u). This represents exact rational parameters. -/
def implicitSafe (u c : Int) : Phase → Int × Int × Int
  | .start | .stimulus => (10*u, 0, 0)
  | .approach => (c, 10*u-c, 0)
  | .interact => (c, 0, 10*u-c)
  | .avoid | .safetyCost => (0, 10*u, 0)

/-- Fixed .1/.9 weights in a{3}(:,:,2,1). -/
def implicitDanger (u : Int) : Phase → Int × Int × Int
  | .start | .stimulus => (10*u, 0, 0)
  | .approach => (u, 9*u, 0)
  | .interact => (u, 0, 9*u)
  | .avoid | .safetyCost => (0, 10*u, 0)

def mass (weights : Int × Int × Int) : Int := weights.1 + weights.2.1 + weights.2.2

def Nonnegative (weights : Int × Int × Int) : Prop :=
  0 ≤ weights.1 ∧ 0 ≤ weights.2.1 ∧ 0 ≤ weights.2.2

theorem approach_trajectory : trajectory approachStep =
    [.start, .stimulus, .approach, .interact] := rfl

theorem avoidance_trajectory : trajectory avoidStep =
    [.start, .stimulus, .avoid, .safetyCost] := rfl

/-- Avoidance gives identical deterministic observations under safe and dangerous states. -/
theorem avoidance_observational_equivalence :
    observedTrajectory true avoidStep = observedTrajectory false avoidStep := rfl

/-- Thus a classifier using only this trajectory cannot be correct for both states. -/
theorem avoidance_no_perfect_classifier :
    ¬ ∃ classify : List (Bool × Bool × Affect × Phase) → Bool,
      ∀ dangerous, classify (observedTrajectory dangerous avoidStep) = dangerous := by
  rintro ⟨classify, works⟩
  have first := works true
  have second := works false
  rw [avoidance_observational_equivalence] at first
  have contradiction : true = false := first.symm.trans second
  cases contradiction

/-- The approach trajectory contains an observation that separates the two states. -/
theorem approach_observations_differ :
    observedTrajectory true approachStep ≠ observedTrajectory false approachStep := by decide

/-- The full deterministic trajectory identifies danger among the two candidate states. -/
theorem approach_identifies_state (a b : Bool)
    (same : observedTrajectory a approachStep = observedTrajectory b approachStep) : a = b := by
  cases a <;> cases b <;> simp_all [observedTrajectory, trajectory, approachStep,
    observation, seesSpider, highArousal, affect]

theorem safe_columns_total_mass (u c : Int) (phase : Phase) :
    mass (implicitSafe u c phase) = 10*u := by
  cases phase <;> simp [implicitSafe, mass] <;> omega

theorem danger_columns_total_mass (u : Int) (phase : Phase) :
    mass (implicitDanger u phase) = 10*u := by
  cases phase <;> simp [implicitDanger, mass] <;> omega

theorem safe_columns_nonnegative (u c : Int) (hu : 0 < u)
    (lower : 0 ≤ c) (upper : c ≤ 10*u) (phase : Phase) :
    Nonnegative (implicitSafe u c phase) := by
  cases phase <;> simp [Nonnegative, implicitSafe] <;> omega

theorem danger_columns_nonnegative (u : Int) (hu : 0 < u) (phase : Phase) :
    Nonnegative (implicitDanger u phase) := by
  cases phase <;> simp [Nonnegative, implicitDanger] <;> omega

/-- At CABi=.1, the two implicit affective mappings coincide at every phase. -/
theorem implicit_mappings_equal_at_tenth (u : Int) (phase : Phase) :
    implicitSafe u u phase = implicitDanger u phase := by
  cases phase <;> simp [implicitSafe, implicitDanger] <;> omega

/-- Equality of the approach columns occurs exactly at CABi=.1 when u>0. -/
theorem approach_implicit_equality_iff (u c : Int) :
    implicitSafe u c .approach = implicitDanger u .approach ↔ c = u := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    subst c
    exact implicit_mappings_equal_at_tenth u .approach

/-- Avoidance's implicit columns ignore CABi and the danger label. -/
theorem avoidance_implicit_columns_equal (u c : Int) :
    implicitSafe u c .avoid = implicitDanger u .avoid ∧
    implicitSafe u c .safetyCost = implicitDanger u .safetyCost := by
  constructor <;> rfl

/-- Explicit prior d{3}, before common multiplier 50, has total mass one. -/
theorem explicit_prior_weights (scale safe : Int) (positive : 0 < scale)
    (lower : 0 ≤ safe) (upper : safe ≤ scale) :
    0 ≤ scale-safe ∧ 0 ≤ safe ∧ (scale-safe)+safe = scale := by omega

end ClinicalModels.PublishedCBT
