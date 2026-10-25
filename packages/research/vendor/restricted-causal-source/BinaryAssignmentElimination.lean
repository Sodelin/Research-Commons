import BinaryAncestralElimination
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Explicit full binary-assignment enumeration for iterated elimination.
Membership is exactly agreement outside the eliminated vertex list;
simple vertex lists produce each assignment once. This connects the
two-point elimination operator to actual finite cylinder sums, rather
than assuming a marginalization/Fubini interface.

API read at mathlib 0df444a360eaa60ab8c11dca51a86af692955474:
Algebra/BigOperators/Group/List/Basic.lean,
blob 525adfce9ad64922cf64efad06d518341695f3e0 (List.sum_map_add);
previously pinned Finset/Basic.lean (List.sum_toFinset) and
Data/List/Nodup.lean (Nodup.map_on, Nodup.append).
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def assignmentEnumeration (base : Assignment V) : List V → List (Assignment V)
  | [] => [base]
  | vertex :: rest =>
      (assignmentEnumeration base rest).map (fun w => pointAssignment vertex w false) ++
      (assignmentEnumeration base rest).map (fun w => pointAssignment vertex w true)

def AgreesOutside (vertices : List V) (base w : Assignment V) : Prop :=
  ∀ vertex, vertex ∉ vertices → w vertex = base vertex

theorem enumeration_membership (base : Assignment V) (vertices : List V) (w : Assignment V) :
    w ∈ assignmentEnumeration base vertices ↔ AgreesOutside vertices base w := by
  induction vertices generalizing w with
  | nil =>
      constructor
      · intro member
        have same : w = base := by simpa only [assignmentEnumeration, List.mem_singleton] using member
        intro vertex _
        exact congrFun same vertex
      · intro agreement
        have same : w = base := funext (fun v => agreement v (by simp))
        simp only [assignmentEnumeration, List.mem_singleton, same]
  | cons vertex rest ih =>
      constructor
      · intro member
        rcases List.mem_append.mp member with member | member
        all_goals
          obtain ⟨old, oldMember, equation⟩ := List.mem_map.mp member
          have agreement := (ih old).mp oldMember
          intro v outside
          have notVertex : v ≠ vertex := fun same => outside (List.mem_cons.mpr (Or.inl same))
          have notRest : v ∉ rest := fun member => outside (List.mem_cons_of_mem _ member)
          rw [← equation]
          simpa only [pointAssignment, if_neg notVertex] using agreement v notRest
      · intro agreement
        let old := pointAssignment vertex w (base vertex)
        have oldAgreement : AgreesOutside rest base old := by
          intro v outside
          by_cases same : v = vertex
          · subst v
            simp only [old, pointAssignment, if_pos rfl]
          · simp only [old, pointAssignment, if_neg same]
            exact agreement v (by simpa only [List.mem_cons, not_or] using And.intro same outside)
        have oldMember := (ih old).mpr oldAgreement
        have recovery : pointAssignment vertex old (w vertex) = w := by
          funext v
          by_cases same : v = vertex
          · subst v; simp only [pointAssignment, if_pos rfl]
          · simp only [pointAssignment, if_neg same, old]
        cases value : w vertex with
        | false =>
            apply List.mem_append.mpr
            apply Or.inl
            apply List.mem_map.mpr
            exact ⟨old, oldMember, by simpa only [value] using recovery⟩
        | true =>
            apply List.mem_append.mpr
            apply Or.inr
            apply List.mem_map.mpr
            exact ⟨old, oldMember, by simpa only [value] using recovery⟩

theorem point_update_injective_on_agreeing (vertex : V) (b : Bool) (base «first» second : Assignment V)
    (firstAt : «first» vertex = base vertex) (secondAt : second vertex = base vertex)
    (same : pointAssignment vertex «first» b = pointAssignment vertex second b) : «first» = second := by
  funext v
  by_cases atVertex : v = vertex
  · subst v
    exact firstAt.trans secondAt.symm
  · have valueEq := congrFun same v
    simpa only [pointAssignment, if_neg atVertex] using valueEq

theorem assignmentEnumeration_nodup (base : Assignment V) (vertices : List V) (simple : vertices.Nodup) :
    (assignmentEnumeration base vertices).Nodup := by
  revert simple
  induction vertices with
  | nil => intro _; exact List.nodup_singleton base
  | cons vertex rest ih =>
      intro simple
      have outside := (List.nodup_cons.mp simple).1
      have oldSimple := ih (List.nodup_cons.mp simple).2
      have mapSimple : ∀ b, ((assignmentEnumeration base rest).map
          (fun w => pointAssignment vertex w b)).Nodup := by
        intro b
        apply List.Nodup.map_on ?_ oldSimple
        intro «first» firstMember second secondMember same
        exact point_update_injective_on_agreeing vertex b base «first» second
          ((enumeration_membership base rest «first»).mp firstMember vertex outside)
          ((enumeration_membership base rest second).mp secondMember vertex outside) same
      apply (mapSimple false).append (mapSimple true)
      intro w inZero inOne
      obtain ⟨«first», _, zeroEq⟩ := List.mem_map.mp inZero
      obtain ⟨second, _, oneEq⟩ := List.mem_map.mp inOne
      have unequal := congrFun (zeroEq.trans oneEq.symm) vertex
      simp only [pointAssignment, if_pos rfl] at unequal
      cases unequal

def eliminateVariables : List V → (Assignment V → ℚ) → Assignment V → ℚ
  | [], f => f
  | vertex :: rest, f => eliminateVariables rest (sumAt vertex f)

theorem elimination_eq_enumeration_sum (base : Assignment V) (vertices : List V)
    (f : Assignment V → ℚ) :
    eliminateVariables vertices f base = ((assignmentEnumeration base vertices).map f).sum := by
  induction vertices generalizing f with
  | nil => simp only [eliminateVariables, assignmentEnumeration, List.map_singleton, List.sum_singleton]
  | cons vertex rest ih =>
      rw [eliminateVariables, ih]
      simp only [assignmentEnumeration, List.map_append, List.map_map, List.sum_append,
        Function.comp_apply]
      exact List.sum_map_add

theorem elimination_eq_finite_sum (base : Assignment V) (vertices : List V)
    (simple : vertices.Nodup) (f : Assignment V → ℚ) :
    eliminateVariables vertices f base =
      ∑ w : Assignment V, if AgreesOutside vertices base w then f w else 0 := by
  classical
  rw [elimination_eq_enumeration_sum]
  rw [← List.sum_toFinset f (assignmentEnumeration_nodup base vertices simple)]
  have exactSet : (assignmentEnumeration base vertices).toFinset =
      Finset.univ.filter (AgreesOutside vertices base) := by
    ext w
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and, enumeration_membership]
  rw [exactSet, Finset.sum_filter]

/-- This is the actual cylinder sum on retained A, not a symbolic partial
integration operator. The list enumerates exactly the complementary
vertices, with no repeats. -/
theorem elimination_eq_cylinder (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (A : Finset V) (base : Assignment V) (vertices : List V) (simple : vertices.Nodup)
    (complement : ∀ v, v ∈ vertices ↔ v ∉ A) :
    eliminateVariables vertices (jointMass D θ) base = cylinderMass D θ A base := by
  rw [elimination_eq_finite_sum base vertices simple]
  unfold cylinderMass
  apply Finset.sum_congr rfl
  intro w _
  have condition : AgreesOutside vertices base w ↔ Matches A base w := by
    constructor
    · intro agreement v member
      exact agreement v (fun h => (complement v).mp h member)
    · intro matching v outside
      apply matching v
      by_contra notMember
      exact outside ((complement v).mpr notMember)
  rw [condition]

end RestrictedCausal.ProbabilitySource.BinaryCPT
