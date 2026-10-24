import BinaryGlobalMarkov
import BinaryCommonPositiveMinorFamily

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

D1–D5 composition on one common rational CPT registry. The forward
graph-to-CI implication is the actual finite-product global Markov body;
the reverse implication uses the constructed nonzero selected minors.
All baseline and separate single-indicator slices share one theta.
These are elementary binary pair CIs, not arbitrary full-law binary tests.
The separate selected normalized-law bridge and final graph/game adapter
must still be composed, and every source body must still elaborate.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators
open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : Type v} [Fintype T] [DecidableEq T]

def SelectedBinaryCI (D : V → V → Prop) (θ : Coordinate D → ℚ) (S : Finset V)
    (x y : V) (C : Finset V) : Prop :=
  ∀ c : Assignment V, Matches S (fun _ => true) c →
    BinaryMassIndependent (cellMass D θ x y C c)

def SelectedBinaryFaithful (D : V → V → Prop) (θ : Coordinate D → ℚ) (S : Finset V) : Prop :=
  ∀ x y C, x ≠ y → x ∉ C → y ∉ C → S ⊆ C →
    (SelectedBinaryCI D θ S x y C ↔
      ¬ ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y)

theorem selected_witness_matches (S : Finset V) :
    Matches S (fun _ => true) (flipSinks S (fun _ => false)) := by
  intro s member
  simp only [flipSinks, if_pos member, Bool.not_false]

/-- The minor hypothesis here is an internal join. The final existence
theorem below supplies it from the actual active-path witness and the
common positive rational avoidance construction. -/
theorem selected_faithful_of_actual_minors (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (S : Finset V)
    (nonzero : ∀ q : SelectedAtomicIndex D S,
      MvPolynomial.eval θ (selectedAtomicMinor D S q) ≠ 0) :
    SelectedBinaryFaithful D θ S := by
  intro x y C different xOutside yOutside contains
  constructor
  · intro independent connected
    let q : SelectedAtomicIndex D S := ⟨(x, y, C),
      different, xOutside, yOutside, contains, connected⟩
    have atWitness := independent (flipSinks S (fun _ => false)) (selected_witness_matches S)
    have determinant := (binary_independent_iff_determinant _).mp atWitness
    apply nonzero q
    simpa only [selectedAtomicMinor, q, eval_minor, binaryDeterminant] using determinant
  · intro separated c selectedValues
    exact binary_global_markov D acyclic θ C x y different xOutside yOutside separated c

/-- Actual full finite binary product normalization is derived for every
pullback parameter table, rather than assumed as a distribution oracle. -/
theorem exists_common_positive_faithful_source (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (target : T → V) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) :
    ∃ θ : SharedCoordinate D target → ℚ,
      (∀ i, 0 < θ i ∧ θ i < 1) ∧
      SelectedBinaryFaithful D (θ ∘ baselineCoordinate D target) S ∧
      (∀ t, SelectedBinaryFaithful (AddIndicator D (target t))
        (θ ∘ singleIndicatorCoordinate D target t) (liftedSelection S)) ∧
      (∑ w : Assignment V, jointMass D (θ ∘ baselineCoordinate D target) w) = 1 ∧
      (∀ t i, (∑ w : Assignment V, jointMass D (θ ∘ regimeCoordinate D target t i) w) = 1) ∧
      (∀ t, (∑ w : Assignment (Option V),
        jointMass (AddIndicator D (target t)) (θ ∘ singleIndicatorCoordinate D target t) w) = 1) := by
  classical
  obtain ⟨θ, positive, baselineMinors, indicatorMinors⟩ :=
    exists_common_positive_selected_minors D acyclic target S sinks
  refine ⟨θ, positive,
    selected_faithful_of_actual_minors D acyclic _ S baselineMinors, ?_, ?_, ?_, ?_⟩
  · intro t
    exact selected_faithful_of_actual_minors (AddIndicator D (target t))
      (add_indicator_acyclic D (target t) acyclic) _ (liftedSelection S) (indicatorMinors t)
  · exact binary_dag_product_normalized D acyclic _
  · intro t i
    exact binary_dag_product_normalized D acyclic _
  · intro t
    exact binary_dag_product_normalized (AddIndicator D (target t))
      (add_indicator_acyclic D (target t) acyclic) _

end RestrictedCausal.ProbabilitySource.BinaryCPT
