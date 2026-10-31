import BinaryTrekDecomposition
import Mathlib.Data.Fintype.Card

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Derive a strict natural rank for every original arrow in an arbitrary
finite DAG. The bound comes from acyclic route simplicity and the actual
finite vertex carrier, not a hidden-source size hypothesis. This is an
existential source construction, not an extracted topological-sort run.

API read pin: mathlib 0df444a360eaa60ab8c11dca51a86af692955474,
Data/Fintype/Card.lean blob 882bcfa5829eca220faf26d0bee76bf2f055558f,
List.Nodup.length_le_card. All probability/source joins remain explicit.
-/

namespace RestrictedCausal.ProbabilitySource

open SelectedWalk

universe u

theorem bounded_nat_maximum (P : Nat → Prop) (bound : Nat)
    (inhabited : ∃ n, P n) (bounded : ∀ n, P n → n ≤ bound) :
    ∃ largest, P largest ∧ ∀ n, P n → n ≤ largest := by
  classical
  revert inhabited bounded
  induction bound with
  | zero =>
      intro inhabited bounded
      obtain ⟨witness, property⟩ := inhabited
      refine ⟨witness, property, ?_⟩
      intro n admitted
      have small := bounded n admitted
      omega
  | succ bound ih =>
      intro inhabited bounded
      by_cases last : P (bound + 1)
      · exact ⟨bound + 1, last, bounded⟩
      · apply ih inhabited
        intro n admitted
        have small := bounded n admitted
        have notLast : n ≠ bound + 1 := by intro same; exact last (same ▸ admitted)
        omega

def IncomingLength {V : Type u} (D : V → V → Prop) (vertex : V) (length : Nat) : Prop :=
  ∃ start vertices, Route D start vertices vertex ∧ vertices.length = length

theorem incoming_length_bounded {V : Type u} [Fintype V] (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (vertex : V) (n : Nat)
    (witness : IncomingLength D vertex n) : n < Fintype.card V := by
  obtain ⟨start, vertices, route, length⟩ := witness
  have bound := (route.acyclic_trace_nodup acyclic).length_le_card
  simp only [List.length_cons, length] at bound
  omega

theorem maximum_incoming_length {V : Type u} [Fintype V] (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (vertex : V) :
    ∃ largest, IncomingLength D vertex largest ∧
      ∀ n, IncomingLength D vertex n → n ≤ largest := by
  apply bounded_nat_maximum (IncomingLength D vertex) (Fintype.card V)
  · exact ⟨0, vertex, [], .nil vertex, rfl⟩
  · intro n witness
    exact (incoming_length_bounded D acyclic vertex n witness).le

noncomputable def dagRank {V : Type u} [Fintype V] (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (vertex : V) : Nat :=
  Classical.choose (maximum_incoming_length D acyclic vertex)

theorem dagRank_spec {V : Type u} [Fintype V] (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (vertex : V) :
    IncomingLength D vertex (dagRank D acyclic vertex) ∧
      ∀ n, IncomingLength D vertex n → n ≤ dagRank D acyclic vertex :=
  Classical.choose_spec (maximum_incoming_length D acyclic vertex)

theorem dagRank_lt_card {V : Type u} [Fintype V] (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (vertex : V) :
    dagRank D acyclic vertex < Fintype.card V :=
  incoming_length_bounded D acyclic vertex _ (dagRank_spec D acyclic vertex).1

theorem dagRank_strict {V : Type u} [Fintype V] (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) {parent child : V}
    (edge : D parent child) : dagRank D acyclic parent < dagRank D acyclic child := by
  obtain ⟨start, vertices, route, length⟩ := (dagRank_spec D acyclic parent).1
  have extended : IncomingLength D child (dagRank D acyclic parent + 1) :=
    ⟨start, vertices ++ [child], route.append (.cons edge (.nil child)), by
      simp only [List.length_append, List.length_singleton, length]⟩
  have bound := (dagRank_spec D acyclic child).2 _ extended
  omega

end RestrictedCausal.ProbabilitySource
