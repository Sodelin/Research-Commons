import BinaryNestedElimination
import Mathlib.Data.Finset.Dedup

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual D1 binary global Markov theorem for the existing active-path
semantics. All products and cell sums are those of the original finite
DAG. Moral-component separation supplies the two factor supports;
ancestral marginalization and explicit binary elimination supply the
cell factorization. Neither global Markov nor a factorization oracle is
an exposed premise. Classical DAG factorization attribution applies.

Finset.toList below is classical finite enumeration in a mathematical
existence proof, not an extracted effective intervention policy.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem moral_factor_supports_disjoint (D : V → V → Prop) (C : Finset V) (x y : V) :
    Disjoint (leftMoralComponent D C x y) (rightMoralVertices D C x y) := by
  apply Finset.disjoint_left.mpr
  intro v «left» «right»
  exact (Finset.mem_sdiff.mp «right»).2 (Finset.mem_union.mpr (Or.inr «left»))

theorem left_support_after_elimination (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : Finset V) (x y : V)
    (separated : ¬ ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y)
    (inner : List V)
    (members : ∀ v, v ∈ inner ↔
      v ∈ ancestralVertices D C x y ∧ v ∉ insert x (insert y C)) :
    leftMoralComponent D C x y \ inner.toFinset ⊆ {x} := by
  intro v member
  have inLeft := (Finset.mem_sdiff.mp member).1
  have outsideInner : v ∉ inner := by
    intro h
    exact (Finset.mem_sdiff.mp member).2 (List.mem_toFinset.mpr h)
  have facts := (mem_leftMoralComponent D C x y v).mp inLeft
  have retained : v ∈ insert x (insert y C) := by
    by_contra outside
    exact outsideInner ((members v).mpr ⟨facts.1, outside⟩)
  rcases Finset.mem_insert.mp retained with same | retained
  · exact Finset.mem_singleton.mpr same
  · rcases Finset.mem_insert.mp retained with same | inC
    · subst v
      exact (finish_not_in_left_component D acyclic C x y separated inLeft).elim
    · exact (facts.2.1 inC).elim

theorem right_support_after_elimination (D : V → V → Prop) (C : Finset V) (x y : V)
    (xOutside : x ∉ C) (inner : List V)
    (members : ∀ v, v ∈ inner ↔
      v ∈ ancestralVertices D C x y ∧ v ∉ insert x (insert y C)) :
    rightMoralVertices D C x y \ inner.toFinset ⊆ {y} := by
  intro v member
  have inRight := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp member).1
  have outsideInner : v ∉ inner := by
    intro h
    exact (Finset.mem_sdiff.mp member).2 (List.mem_toFinset.mpr h)
  have retained : v ∈ insert x (insert y C) := by
    by_contra outside
    exact outsideInner ((members v).mpr ⟨inRight.1, outside⟩)
  rcases Finset.mem_insert.mp retained with same | retained
  · subst v
    exact (inRight.2 (Finset.mem_union.mpr
      (Or.inr (start_in_left_component D C x y xOutside)))).elim
  · rcases Finset.mem_insert.mp retained with same | inC
    · exact Finset.mem_singleton.mpr same
    · exact (inRight.2 (Finset.mem_union.mpr (Or.inl inC))).elim

/-- The literal four original cell masses factor across the endpoints.
The factors can be signed for arbitrary algebraic parameters; positivity
is not needed for the global-Markov polynomial identity. -/
theorem separated_cells_factor (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (C : Finset V) (x y : V) (different : x ≠ y)
    (xOutside : x ∉ C) (yOutside : y ∉ C)
    (separated : ¬ ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y)
    (c : Assignment V) :
    ∃ «left» «right» : Bool → ℚ, ∀ a b, cellMass D θ x y C c a b = «left» a * «right» b := by
  classical
  let inner := (ancestralVertices D C x y \ insert x (insert y C)).toList
  have simple : inner.Nodup := Finset.nodup_toList _
  have members : ∀ v, v ∈ inner ↔
      v ∈ ancestralVertices D C x y ∧ v ∉ insert x (insert y C) := by
    intro v
    simp only [inner, Finset.mem_toList, Finset.mem_sdiff]
  obtain ⟨f, g, fDepends, gDepends, originalFactors⟩ :=
    clamped_ancestral_product_factors D θ C x y c
  obtain ⟨F, G, FDepends, GDepends, eliminatedFactors⟩ :=
    eliminate_disjoint_product inner (leftMoralComponent D C x y) (rightMoralVertices D C x y)
      (moral_factor_supports_disjoint D C x y) f g fDepends gDepends
  have leftOnly : DependsOn {x} F := dependsOn_mono FDepends
    (left_support_after_elimination D acyclic C x y separated inner members)
  have rightOnly : DependsOn {y} G := dependsOn_mono GDepends
    (right_support_after_elimination D C x y xOutside inner members)
  refine ⟨(fun a => F (cellAssignment x y c a false)),
    (fun b => G (cellAssignment x y c false b)), ?_⟩
  intro a b
  rw [cell_mass_as_clamped_elimination D acyclic θ C x y xOutside yOutside
    inner simple members c a b, originalFactors, eliminatedFactors]
  have leftValue : F (cellAssignment x y c a b) = F (cellAssignment x y c a false) := by
    apply leftOnly
    intro v member
    have same := Finset.mem_singleton.mp member
    subst v
    simp (config := {instances := true}) [cellAssignment]
  have rightValue : G (cellAssignment x y c a b) = G (cellAssignment x y c false b) := by
    apply rightOnly
    intro v member
    have same := Finset.mem_singleton.mp member
    subst v
    simp (config := {instances := true}) [cellAssignment, different.symm]
  dsimp only
  rw [leftValue, rightValue]

theorem separated_minor_eval_zero (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (C : Finset V) (x y : V) (different : x ≠ y)
    (xOutside : x ∉ C) (yOutside : y ∉ C)
    (separated : ¬ ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y)
    (c : Assignment V) :
    MvPolynomial.eval θ (minorPolynomial D x y C c) = 0 := by
  obtain ⟨«left», «right», factors⟩ := separated_cells_factor D acyclic θ C x y
    different xOutside yOutside separated c
  rw [eval_minor, factors false false, factors true true, factors false true, factors true false]
  ring

/-- Standard binary conditional independence on every conditioning slice,
derived from the original finite DAG's d-separation. For positive CPTs,
the earlier normalization/positivity lemmas make these genuine probability
laws. No faithfulness or independence oracle is assumed. -/
theorem binary_global_markov (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (C : Finset V) (x y : V) (different : x ≠ y)
    (xOutside : x ∉ C) (yOutside : y ∉ C)
    (separated : ¬ ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y) :
    ∀ c : Assignment V, BinaryMassIndependent (cellMass D θ x y C c) := by
  intro c
  apply (binary_independent_iff_determinant _).mpr
  have zero := separated_minor_eval_zero D acyclic θ C x y different xOutside yOutside separated c
  simpa only [eval_minor, binaryDeterminant] using zero

end RestrictedCausal.ProbabilitySource.BinaryCPT
