import SamuelAlexanderResearch.ObservationPrediction
import Mathlib.Data.Set.Function

/-!
Reusable observation interfaces. SOURCE CANDIDATE: not yet elaborated or audited.
The Option-valued factorization is inherited verbatim from the accepted
ObservationPrediction supplier. No empirical observation model is asserted here.
-/

namespace Semi.Core

universe u v w
variable {X : Type u} {O : Type v} {A : Type w}

def observationSetoid (observe : X → O) : Setoid X where
  r x y := observe x = observe y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev ConstantOnFibres := @ObservationPrediction.ConstantOnFibres
abbrev OptionRecoverable := @ObservationPrediction.Recoverable

theorem option_factorization_iff (observe : X → O) (target : X → A) :
    OptionRecoverable observe target ↔ ConstantOnFibres observe target :=
  ObservationPrediction.recoverable_iff_constant_on_fibres observe target

/-- A decoder on the actual observation range needs no default answer. -/
theorem range_factorization_iff (observe : X → O) (target : X → A) :
    (∃ decode : Set.range observe → A,
      ∀ x, decode ⟨observe x, ⟨x, rfl⟩⟩ = target x) ↔
      ConstantOnFibres observe target := by
  classical
  constructor
  · rintro ⟨decode, hd⟩ x y hxy
    have he : (⟨observe x, ⟨x, rfl⟩⟩ : Set.range observe) =
        ⟨observe y, ⟨y, rfl⟩⟩ := Subtype.ext hxy
    exact (hd x).symm.trans ((congrArg decode he).trans (hd y))
  · intro h
    let decode : Set.range observe → A := fun o => target (Classical.choose o.2)
    refine ⟨decode, fun x => ?_⟩
    exact h _ _ (Classical.choose_spec (show observe x ∈ Set.range observe from ⟨x, rfl⟩))

/-- A total A-valued decoder on unused observations needs a default, supplied
here by Nonempty A. This premise is not needed by the range/Option results. -/
theorem total_factorization_iff [Nonempty A] (observe : X → O) (target : X → A) :
    (∃ decode : O → A, ∀ x, decode (observe x) = target x) ↔
      ConstantOnFibres observe target := by
  classical
  constructor
  · rintro ⟨decode, hd⟩ x y hxy
    exact (hd x).symm.trans ((congrArg decode hxy).trans (hd y))
  · intro h
    obtain ⟨decode, hd⟩ := (option_factorization_iff observe target).2 h
    refine ⟨fun o => (decode o).getD (Classical.choice inferInstance), ?_⟩
    intro x
    simp [hd x]

/-- Exact total-decoder extension condition, including empty types. -/
theorem total_factorization_iff_extension (observe : X → O) (target : X → A) :
    (∃ decode : O → A, ∀ x, decode (observe x) = target x) ↔
      ConstantOnFibres observe target ∧ (Nonempty O → Nonempty A) := by
  classical
  constructor
  · rintro ⟨decode, hd⟩
    refine ⟨?_, ?_⟩
    · intro x y hxy
      exact (hd x).symm.trans ((congrArg decode hxy).trans (hd y))
    · rintro ⟨o⟩
      exact ⟨decode o⟩
  · rintro ⟨h, hext⟩
    by_cases ho : Nonempty O
    · letI : Nonempty A := hext ho
      exact (total_factorization_iff observe target).2 h
    · exact ⟨fun o => False.elim (ho ⟨o⟩), fun x => False.elim (ho ⟨observe x⟩)⟩

end Semi.Core
