import BinaryAssignmentElimination

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual finite-DAG ancestral marginalization and normalization. A complete
sink-elimination order is constructed outside the retained ancestral set;
the explicit binary-assignment enumeration identifies its operator with
the original full-assignment cylinder sum. No normalizing constant or
factorization identity is an extra premise. D1 global Markov remains.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators
open SelectedWalk

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem ancestral_elimination_order (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (A : Finset V) (ancestral : AncestralSet D A)
    (U : Finset V) (disjoint : Disjoint A U) :
    ∃ vertices : List V, vertices.Nodup ∧ (∀ v, v ∈ vertices ↔ v ∈ U) ∧
      ∀ θ : Coordinate D → ℚ,
        eliminateVariables vertices (partialJointMass D θ (A ∪ U)) = partialJointMass D θ A := by
  classical
  have establish : ∀ n, ∀ U : Finset V, U.card = n → Disjoint A U →
      ∃ vertices : List V, vertices.Nodup ∧ (∀ v, v ∈ vertices ↔ v ∈ U) ∧
        ∀ θ : Coordinate D → ℚ,
          eliminateVariables vertices (partialJointMass D θ (A ∪ U)) = partialJointMass D θ A := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro U cardinal disjoint
        by_cases empty : U = ∅
        · subst U
          refine ⟨[], List.nodup_nil, ?_, ?_⟩
          · intro v; simp
          · intro θ; simp only [Finset.union_empty, eliminateVariables]
        · obtain ⟨vertex, member, sink⟩ := sink_outside_ancestral D acyclic A U ancestral disjoint
            (Finset.nonempty_iff_ne_empty.mpr empty)
          have smaller : (U.erase vertex).card < n := by
            have bound := Finset.card_erase_lt_of_mem member
            omega
          have remainingDisjoint : Disjoint A (U.erase vertex) := by
            apply Finset.disjoint_left.mpr
            intro v inA inU
            exact Finset.disjoint_left.mp disjoint inA (Finset.mem_erase.mp inU).2
          obtain ⟨rest, restSimple, restMembers, restEliminates⟩ :=
            ih (U.erase vertex).card smaller (U.erase vertex) rfl remainingDisjoint
          have outsideA : vertex ∉ A := fun inA => Finset.disjoint_left.mp disjoint inA member
          have outsideRest : vertex ∉ rest := by
            intro inRest
            exact (Finset.mem_erase.mp ((restMembers vertex).mp inRest)).1 rfl
          have eraseUnion : (A ∪ U).erase vertex = A ∪ U.erase vertex := by
            ext v
            by_cases same : v = vertex
            · subst v; simp [outsideA]
            · simp [Finset.mem_erase, Finset.mem_union, same]
          refine ⟨vertex :: rest, List.nodup_cons.mpr ⟨outsideRest, restSimple⟩, ?_, ?_⟩
          · intro v
            constructor
            · intro inList
              rcases List.mem_cons.mp inList with same | inRest
              · exact same.symm ▸ member
              · exact (Finset.mem_erase.mp ((restMembers v).mp inRest)).2
            · intro inU
              by_cases same : v = vertex
              · exact List.mem_cons.mpr (Or.inl same)
              · exact List.mem_cons_of_mem _ ((restMembers v).mpr (Finset.mem_erase.mpr ⟨same, inU⟩))
          · intro θ
            rw [eliminateVariables,
              sumAt_sink_product D θ (A ∪ U) vertex (Finset.mem_union.mpr (Or.inr member)) sink,
              eraseUnion]
            exact restEliminates θ
  exact establish U.card U rfl disjoint

theorem ancestral_cylinder_mass (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ)
    (A : Finset V) (ancestral : AncestralSet D A) (base : Assignment V) :
    cylinderMass D θ A base = partialJointMass D θ A base := by
  classical
  let U : Finset V := Finset.univ \ A
  have disjoint : Disjoint A U := by
    apply Finset.disjoint_left.mpr
    intro v inA inU
    exact (Finset.mem_sdiff.mp inU).2 inA
  obtain ⟨vertices, simple, members, eliminates⟩ := ancestral_elimination_order D acyclic A ancestral U disjoint
  have complement : ∀ v, v ∈ vertices ↔ v ∉ A := by
    intro v
    simpa only [U, Finset.mem_sdiff, Finset.mem_univ, true_and] using members v
  have all : A ∪ U = Finset.univ := by
    ext v
    simp only [U, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    exact Classical.em (v ∈ A)
  have evaluated := congrFun (eliminates θ) base
  rw [all] at evaluated
  have originalProduct : partialJointMass D θ Finset.univ = jointMass D θ := rfl
  rw [originalProduct, elimination_eq_cylinder D θ A base vertices simple complement] at evaluated
  exact evaluated

/-- The actual arbitrary finite binary-DAG product is normalized. This
holds even for algebraic rational parameters; positivity is needed only
when interpreting it as a probability law. -/
theorem binary_dag_product_normalized (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (θ : Coordinate D → ℚ) :
    (∑ w : Assignment V, jointMass D θ w) = 1 := by
  have ancestralEmpty : AncestralSet D (∅ : Finset V) := by
    intro parent child edge impossible
    exact (Finset.notMem_empty child impossible).elim
  have marginal := ancestral_cylinder_mass D acyclic θ ∅ ancestralEmpty (fun _ => false)
  simpa [cylinderMass, Matches, partialJointMass] using marginal

end RestrictedCausal.ProbabilitySource.BinaryCPT
