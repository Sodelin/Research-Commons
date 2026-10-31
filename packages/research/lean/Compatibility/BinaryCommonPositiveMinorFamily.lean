import BinarySharedMechanismRegistry
import Mathlib.Data.Fintype.Powerset

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The concrete finite D2/D3/D4-to-D5 application. One common rational point
in the positive cube simultaneously preserves every graphical nonzero
selected pair minor, both in the baseline and in EVERY separate named
single-indicator augmentation of the SAME original finite DAG.

This does not yet supply arbitrary-DAG normalization/global Markov (D1),
the selected conditional-invariance law identity (D6), or the final G7
physical-source oracle adapter. It is not a sample-complexity statement.

API read: mathlib 0df444a360eaa60ab8c11dca51a86af692955474,
Data/Fintype/Powerset.lean blob 24ae705d64e036c959cfa6fc3593128ba56e6f7c,
the actual Finset.fintype enumeration by powerset of the finite universe.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open SelectedWalk CanonicalSelection LatentRoots VertexActivePaths
open InducingSeparation OriginalProjection

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : Type v} [Fintype T] [DecidableEq T]

abbrev AtomicQuery (V : Type u) := V × V × Finset V

def SelectedAtomicValid (D : V → V → Prop) (S : Finset V) (q : AtomicQuery V) : Prop :=
  q.1 ≠ q.2.1 ∧ q.1 ∉ q.2.2 ∧ q.2.1 ∉ q.2.2 ∧ S ⊆ q.2.2 ∧
    ActiveConnection (arrowGraph D) (fun v => v ∈ q.2.2) q.1 q.2.1

abbrev SelectedAtomicIndex (D : V → V → Prop) (S : Finset V) :=
  {q : AtomicQuery V // SelectedAtomicValid D S q}

noncomputable instance selectedAtomicIndexFintype (D : V → V → Prop) (S : Finset V) :
    Fintype (SelectedAtomicIndex D S) := by
  classical
  infer_instance

def liftedSelection (S : Finset V) : Finset (Option V) := S.image some

theorem lifted_selection_sinks (D : V → V → Prop) (target : V) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) :
    ∀ s ∈ liftedSelection S, ∀ v, ¬ AddIndicator D target s v := by
  intro s member v edge
  obtain ⟨old, oldMember, equation⟩ := Finset.mem_image.mp member
  subst s
  cases v with
  | none => exact edge.elim
  | some child => exact sinks old oldMember child edge

noncomputable def selectedAtomicMinor (D : V → V → Prop) (S : Finset V) (q : SelectedAtomicIndex D S) :
    MvPolynomial (Coordinate D) ℚ :=
  minorPolynomial D q.val.1 q.val.2.1 q.val.2.2 (flipSinks S (fun _ => false))

theorem selected_atomic_minor_nonzero (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) (q : SelectedAtomicIndex D S) :
    selectedAtomicMinor D S q ≠ 0 :=
  binary_selected_sink_minor_nonzero D acyclic q.val.1 q.val.2.1 q.val.2.2 S
    q.property.2.2.2.1 sinks q.property.1 q.property.2.1 q.property.2.2.1 q.property.2.2.2.2

abbrev SharedMinorIndex (D : V → V → Prop) (target : T → V) (S : Finset V) :=
  Sum (SelectedAtomicIndex D S)
    ((t : T) × SelectedAtomicIndex (AddIndicator D (target t)) (liftedSelection S))

noncomputable def sharedMinorPolynomial (D : V → V → Prop) (target : T → V) (S : Finset V) :
    SharedMinorIndex D target S → MvPolynomial (SharedCoordinate D target) ℚ
  | .inl q => MvPolynomial.rename (baselineCoordinate D target) (selectedAtomicMinor D S q)
  | .inr ⟨t, q⟩ => MvPolynomial.rename (singleIndicatorCoordinate D target t)
      (selectedAtomicMinor (AddIndicator D (target t)) (liftedSelection S) q)

theorem shared_minor_polynomial_nonzero (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (target : T → V) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) (q : SharedMinorIndex D target S) :
    sharedMinorPolynomial D target S q ≠ 0 := by
  rcases q with q | ⟨t, q⟩
  · exact shared_baseline_polynomial_nonzero D target _ (selected_atomic_minor_nonzero D acyclic S sinks q)
  · exact shared_indicator_polynomial_nonzero D target t _
      (selected_atomic_minor_nonzero (AddIndicator D (target t))
        (add_indicator_acyclic D (target t) acyclic) (liftedSelection S)
        (lifted_selection_sinks D (target t) S sinks) q)

/-- All pair constraints are indexed by actual finite labels, endpoint
pairs and conditioning subsets. Graphical connection only filters that
finite family. Thus D5 receives concrete nonzero original-source minors,
not an external faithfulness assumption or supplied minor certificate. -/
theorem exists_common_positive_selected_minors (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (target : T → V) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) :
    ∃ θ : SharedCoordinate D target → ℚ,
      (∀ i, 0 < θ i ∧ θ i < 1) ∧
      (∀ q : SelectedAtomicIndex D S,
        MvPolynomial.eval (θ ∘ baselineCoordinate D target) (selectedAtomicMinor D S q) ≠ 0) ∧
      (∀ t (q : SelectedAtomicIndex (AddIndicator D (target t)) (liftedSelection S)),
        MvPolynomial.eval (θ ∘ singleIndicatorCoordinate D target t)
          (selectedAtomicMinor (AddIndicator D (target t)) (liftedSelection S) q) ≠ 0) := by
  classical
  letI : Fintype (SharedMinorIndex D target S) := inferInstance
  obtain ⟨θ, positive, every⟩ := exists_common_positive_rational_point
    (sharedMinorPolynomial D target S) (shared_minor_polynomial_nonzero D acyclic target S sinks)
  refine ⟨θ, positive, ?_, ?_⟩
  · intro q
    have chosen := every (.inl q)
    simpa only [sharedMinorPolynomial, MvPolynomial.eval_rename] using chosen
  · intro t q
    have chosen := every (.inr ⟨t, q⟩)
    simpa only [sharedMinorPolynomial, MvPolynomial.eval_rename] using chosen

end RestrictedCausal.ProbabilitySource.BinaryCPT
