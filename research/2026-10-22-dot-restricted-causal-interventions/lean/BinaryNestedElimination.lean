import BinaryMoralFactorization

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

D1's actual finite-sum join: eliminate vertices outside the ancestral
set first, then its non-retained vertices. This is identified with the
original cylinder mass by the explicit assignment enumeration. Clamping
the conditioning coordinates commutes with all remaining eliminations.
The vertex enumeration is a supplied finite list here, not extracted code.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open SelectedWalk

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem eliminateVariables_append («first» second : List V) (f : Assignment V → ℚ) :
    eliminateVariables («first» ++ second) f =
      eliminateVariables second (eliminateVariables «first» f) := by
  induction «first» generalizing f with
  | nil => rfl
  | cons vertex rest ih =>
      exact ih (sumAt vertex f)

/-- An arbitrary retained subset of an ancestral set. The output is the
actual full-assignment cylinder sum, including all latent variables. -/
theorem ancestral_partial_elimination (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (A B : Finset V) (ancestral : AncestralSet D A) (subset : B ⊆ A)
    (inner : List V) (simple : inner.Nodup)
    (members : ∀ v, v ∈ inner ↔ v ∈ A ∧ v ∉ B) (base : Assignment V) :
    eliminateVariables inner (partialJointMass D θ A) base = cylinderMass D θ B base := by
  classical
  let U : Finset V := Finset.univ \ A
  have disjoint : Disjoint A U := by
    apply Finset.disjoint_left.mpr
    intro v inA inU
    exact (Finset.mem_sdiff.mp inU).2 inA
  obtain ⟨outer, outerSimple, outerMembers, eliminates⟩ :=
    ancestral_elimination_order D acyclic A ancestral U disjoint
  have outerComplement : ∀ v, v ∈ outer ↔ v ∉ A := by
    intro v
    simpa only [U, Finset.mem_sdiff, Finset.mem_univ, true_and] using outerMembers v
  have listDisjoint : List.Disjoint outer inner := by
    intro v inOuter inInner
    exact (outerComplement v).mp inOuter ((members v).mp inInner).1
  have joinedSimple := outerSimple.append simple listDisjoint
  have joinedMembers : ∀ v, v ∈ outer ++ inner ↔ v ∉ B := by
    intro v
    constructor
    · intro member
      rcases List.mem_append.mp member with outside | inside
      · exact fun inB => (outerComplement v).mp outside (subset inB)
      · exact ((members v).mp inside).2
    · intro outsideB
      by_cases inA : v ∈ A
      · exact List.mem_append.mpr (Or.inr ((members v).mpr ⟨inA, outsideB⟩))
      · exact List.mem_append.mpr (Or.inl ((outerComplement v).mpr inA))
  have all : A ∪ U = Finset.univ := by
    ext v
    simp only [U, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    exact Classical.em (v ∈ A)
  have outsideEliminates := eliminates θ
  rw [all] at outsideEliminates
  have originalProduct : partialJointMass D θ Finset.univ = jointMass D θ := rfl
  rw [originalProduct] at outsideEliminates
  have cylinder := elimination_eq_cylinder D θ B base (outer ++ inner) joinedSimple joinedMembers
  rw [eliminateVariables_append, outsideEliminates] at cylinder
  exact cylinder

theorem clamp_point_outside (C : Finset V) (base w : Assignment V) (vertex : V)
    (outside : vertex ∉ C) (bit : Bool) :
    clampCondition C base (pointAssignment vertex w bit) =
      pointAssignment vertex (clampCondition C base w) bit := by
  funext v
  by_cases atVertex : v = vertex
  · subst v
    simp only [clampCondition, pointAssignment, if_pos rfl, if_neg outside]
  · by_cases conditioned : v ∈ C
    · simp only [clampCondition, pointAssignment, if_neg atVertex, if_pos conditioned]
    · simp only [clampCondition, pointAssignment, if_neg atVertex, if_neg conditioned]

theorem eliminate_clamped (C : Finset V) (base : Assignment V)
    (vertices : List V) (outside : ∀ v ∈ vertices, v ∉ C) (f : Assignment V → ℚ) :
    eliminateVariables vertices (fun w => f (clampCondition C base w)) =
      fun w => eliminateVariables vertices f (clampCondition C base w) := by
  revert outside
  induction vertices generalizing f with
  | nil => intro _; rfl
  | cons vertex rest ih =>
      intro outside
      have vertexOutside := outside vertex List.mem_cons_self
      have restOutside : ∀ v ∈ rest, v ∉ C :=
        fun v member => outside v (List.mem_cons_of_mem _ member)
      have firstStep : sumAt vertex (fun w => f (clampCondition C base w)) =
          fun w => sumAt vertex f (clampCondition C base w) := by
        funext w
        unfold sumAt
        rw [clamp_point_outside C base w vertex vertexOutside false,
          clamp_point_outside C base w vertex vertexOutside true]
      rw [eliminateVariables, firstStep, ih (f := sumAt vertex f) restOutside]
      rfl

theorem clamp_cell_assignment (C : Finset V) (x y : V) (c : Assignment V) (a b : Bool)
    (xOutside : x ∉ C) (yOutside : y ∉ C) :
    clampCondition C c (cellAssignment x y c a b) = cellAssignment x y c a b := by
  funext v
  by_cases member : v ∈ C
  · have notX : v ≠ x := by intro same; subst v; exact xOutside member
    have notY : v ≠ y := by intro same; subst v; exact yOutside member
    simp only [clampCondition, if_pos member, cellAssignment, if_neg notX, if_neg notY]
  · simp only [clampCondition, if_neg member]

theorem retained_subset_ancestral (D : V → V → Prop) (C : Finset V) (x y : V) :
    insert x (insert y C) ⊆ ancestralVertices D C x y := by
  intro v member
  apply (mem_ancestralVertices D C x y v).mpr
  refine ⟨v, ⟨[], .nil v⟩, ?_⟩
  rcases Finset.mem_insert.mp member with atX | member
  · exact Or.inl atX
  · rcases Finset.mem_insert.mp member with atY | inC
    · exact Or.inr (Or.inl atY)
    · exact Or.inr (Or.inr inC)

/-- Each actual x/y cell is the same clamped ancestral-product elimination,
evaluated at its endpoint values. No numerical-law factorization is assumed. -/
theorem cell_mass_as_clamped_elimination (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (C : Finset V) (x y : V) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (inner : List V) (simple : inner.Nodup)
    (members : ∀ v, v ∈ inner ↔
      v ∈ ancestralVertices D C x y ∧ v ∉ insert x (insert y C))
    (c : Assignment V) (a b : Bool) :
    cellMass D θ x y C c a b =
      eliminateVariables inner
        (fun w => partialJointMass D θ (ancestralVertices D C x y) (clampCondition C c w))
        (cellAssignment x y c a b) := by
  have outside : ∀ v ∈ inner, v ∉ C := by
    intro v member inC
    exact ((members v).mp member).2
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem inC))
  rw [eliminate_clamped C c inner outside, clamp_cell_assignment C x y c a b xOutside yOutside]
  exact (ancestral_partial_elimination D acyclic θ _ _
    (ancestralVertices_closed D C x y) (retained_subset_ancestral D C x y)
    inner simple members (cellAssignment x y c a b)).symm

end RestrictedCausal.ProbabilitySource.BinaryCPT
