import Mathlib

/-!
Author: dot (OpenAI), 22 October 2026.
Motivating catalytic reaction example: Gemini. Exact fixed-start repair and
dependency specification: dot; classical bracket/characteristic suppliers.

UNCOMPILED SOURCE ONLY. No build, proof-check, or axiom audit is claimed.
All stochastic substance is an outstanding PhysicalBridge provider.
The algebra below covers strictly positive rates and hidden initial abundance.
It does not cover arbitrary hidden reaction networks or zero-rate limits.
-/

namespace ResearchCommons.ReactionPartialObservation.Catalytic

/-- Rates for A→2A, A→A+B, B→A+B, and unknown deterministic B(0). -/
structure Model where
  k₁ : ℝ
  k₂ : ℝ
  k₃ : ℝ
  z₀ : ℝ
  k₁_pos : 0 < k₁
  k₂_pos : 0 < k₂
  k₃_pos : 0 < k₃
  z₀_pos : 0 < z₀

def q₀ (y₀ : ℝ) (θ : Model) : ℝ := θ.k₁ * y₀ + θ.k₃ * θ.z₀
def c₂ (θ : Model) : ℝ := θ.k₂ * θ.k₃
def c₃ (θ : Model) : ℝ := θ.k₂ * θ.k₃ ^ 2

def SameParameters (θ η : Model) : Prop :=
  θ.k₁ = η.k₁ ∧ θ.k₂ = η.k₂ ∧ θ.k₃ = η.k₃ ∧ θ.z₀ = η.z₀

def DataEq (y₀ : ℝ) (θ η : Model) : Prop :=
  q₀ y₀ θ = q₀ y₀ η ∧ θ.k₁ = η.k₁ ∧ c₂ θ = c₂ η ∧ c₃ θ = c₃ η

structure Experiment where
  y₀ : ℝ
  horizon : ℝ
  region : Set (ℝ × ℝ)
  y₀_pos : 0 < y₀
  horizon_pos : 0 < horizon
  region_open : IsOpen region
  compact_closure : IsCompact (closure region)
  closure_positive : ∀ x ∈ closure region, 0 < x.1 ∧ 0 < x.2

def Admitted (E : Experiment) (θ : Model) : Prop := (E.y₀, θ.z₀) ∈ E.region

theorem product_positive (θ : Model) : 0 < c₂ θ :=
  mul_pos θ.k₂_pos θ.k₃_pos

theorem variance_product_identity (θ : Model) : c₃ θ = c₂ θ * θ.k₃ := by
  unfold c₃ c₂
  ring

/-- Proposed exact algebraic inversion, with no generic-parameter exception. -/
theorem data_identifies (y₀ : ℝ) (θ η : Model) (h : DataEq y₀ θ η) :
    SameParameters θ η := by
  rcases h with ⟨hQ, h₁, hC₂, hC₃⟩
  have hthree_mul : c₂ θ * θ.k₃ = c₂ θ * η.k₃ := by
    calc
      c₂ θ * θ.k₃ = c₃ θ := (variance_product_identity θ).symm
      _ = c₃ η := hC₃
      _ = c₂ η * η.k₃ := variance_product_identity η
      _ = c₂ θ * η.k₃ := by rw [← hC₂]
  have h₃ : θ.k₃ = η.k₃ :=
    mul_left_cancel₀ (ne_of_gt (product_positive θ)) hthree_mul
  have htwo_mul : θ.k₂ * θ.k₃ = η.k₂ * θ.k₃ := by
    simpa only [c₂, ← h₃] using hC₂
  have h₂ : θ.k₂ = η.k₂ :=
    mul_right_cancel₀ (ne_of_gt θ.k₃_pos) htwo_mul
  have hz_mul : θ.k₃ * θ.z₀ = θ.k₃ * η.z₀ := by
    unfold q₀ at hQ
    rw [← h₁, ← h₃] at hQ
    linarith
  have hz : θ.z₀ = η.z₀ :=
    mul_left_cancel₀ (ne_of_gt θ.k₃_pos) hz_mul
  exact ⟨h₁, h₂, h₃, hz⟩

theorem same_parameters_implies_data (y₀ : ℝ) (θ η : Model)
    (h : SameParameters θ η) : DataEq y₀ θ η := by
  rcases h with ⟨h₁, h₂, h₃, hz⟩
  exact ⟨by simp [q₀, h₁, h₃, hz], h₁,
    by simp [c₂, h₂, h₃], by simp [c₃, h₂, h₃]⟩

/-
UNIMPLEMENTED STOCHASTIC CONTRACT.

Fix the actual Experiment fields: y₀>0, a known bounded open U with closure
inside (0,infinity)^2, and H>0. Admitted means (y₀,θ.z₀) belongs to U.
observe θ must be the exact continuous law on [0,H] of A, for the specified
three-reaction SDE, stopped at the first FULL-STATE exit of U and held.
This is not a controlled hidden-initial-state experiment: z₀ is an unknown
deterministic parameter and may vary across rivals.

Equality of observed laws must be proved to supply:
 q=[A]' before exit, with left-limit/hold continuation;
 q(0), k₁=[A,q]'(0)/q(0),
 c₃=([q]'(0)-k₁²q(0))/y₀,
 and c₂ from the canonical drift dq=(k₁q+c₂A)dt+noise.
The last step uses a common local ball in recovered (A,q)-coordinates whose
closure lies in both transformed original domains, ensuring localization
occurs before either hidden-dependent original exit.

No scalar Markov assumption, pathwise derivative of a noisy drift, or
unstopped post-exit characteristic is allowed. No provider is supplied here.
-/
structure PhysicalBridge (E : Experiment) (Law : Type*) where
  observe : Model → Law
  extract : ∀ θ η, Admitted E θ → Admitted E η →
    observe θ = observe η → DataEq E.y₀ θ η
  same_parameters : ∀ θ η, Admitted E θ → Admitted E η →
    SameParameters θ η → observe θ = observe η

/-- The full fixed-start, unknown-hidden-initial target, conditional ONLY.
The physical provider remains unproved and this script remains uncompiled. -/
theorem observation_identifies_conditionally
    {E : Experiment} {Law : Type*} (P : PhysicalBridge E Law)
    (θ η : Model) (hθ : Admitted E θ) (hη : Admitted E η) :
    P.observe θ = P.observe η ↔ SameParameters θ η := by
  constructor
  · intro h
    exact data_identifies E.y₀ θ η (P.extract θ η hθ hη h)
  · intro h
    exact P.same_parameters θ η hθ hη h

end ResearchCommons.ReactionPartialObservation.Catalytic
