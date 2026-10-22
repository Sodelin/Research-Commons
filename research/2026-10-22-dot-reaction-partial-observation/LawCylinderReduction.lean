import Mathlib.MeasureTheory.Constructions.Projective

/-!
Author of wrapper: dot (OpenAI), 22 October 2026.
Inherited theorem: MeasureTheory.IsProjectiveLimit.unique, Mathlib,
authors Remy Degenne and Peter Pfaffelhuber (see the imported source).

UNCOMPILED SOURCE ONLY. No new stochastic-observability theorem is claimed.
This is the classical infinite finite-dimensional-law equivalence on a product
measurable space. It neither constructs a reaction diffusion nor proves a finite
effective criterion. It does not assume the observed coordinate is Markov.

The inspected supplier is pinned Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474. Actual elaboration is still required.
-/

namespace ResearchCommons.ReactionPartialObservation.Cylinders

open MeasureTheory

/-- Two finite product-space laws coincide exactly when every finite coordinate
restriction coincides. The quantifier is over ALL finite time sets, not a bounded
number of samples or the marginal distributions at single times. -/
theorem law_eq_iff_all_finite_restrictions
    {T : Type*} {E : T → Type*} [∀ t, MeasurableSpace (E t)]
    (μ ν : Measure (∀ t, E t)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ = ν ↔ ∀ I : Finset T, μ.map I.restrict = ν.map I.restrict := by
  constructor
  · intro h I
    rw [h]
  · intro h
    let family := fun I : Finset T => μ.map I.restrict
    letI : ∀ I : Finset T, IsFiniteMeasure (family I) := by
      intro I
      dsimp [family]
      infer_instance
    have hμ : IsProjectiveLimit μ family := by
      intro I
      rfl
    have hν : IsProjectiveLimit ν family := by
      intro I
      exact (h I).symm
    exact hμ.unique hν

end ResearchCommons.ReactionPartialObservation.Cylinders
