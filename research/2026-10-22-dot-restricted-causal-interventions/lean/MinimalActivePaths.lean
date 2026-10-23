import VertexActivePaths

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Construct shortest and closest m-connecting paths from the actual path
semantics, including genuine minimum directed distances of colliders to Z.
This is the existence component of the classical Ali--Richardson--Spirtes
closest-path argument, not its order/ancestry-transfer geometry.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation DiscriminatingStatus
open SourceSelection (AncestorOf)

universe u

theorem minimum_nat_measure {A : Type u} (P : A → Prop) (cost : A → Nat)
    (witness : A) (admitted : P witness) : ∃ best, P best ∧ ∀ a, P a → cost best ≤ cost a := by
  classical
  have find : ∀ n, ∀ a, cost a = n → P a → ∃ best, P best ∧ ∀ b, P b → cost best ≤ cost b := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro a value ha
        by_cases smaller : ∃ b, P b ∧ cost b < n
        · obtain ⟨b, hb, less⟩ := smaller
          exact ih (cost b) less b rfl hb
        · refine ⟨a, ha, ?_⟩
          intro b hb
          have notLess : ¬ cost b < n := fun h => smaller ⟨b, hb, h⟩
          omega
  exact find (cost witness) witness rfl admitted

def DirectedLength {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (b : V) (n : Nat) : Prop :=
  ∃ z xs, Route (Directed G) b xs z ∧ Z z ∧ xs.length = n

theorem minimum_directed_length {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (b : V)
    (h : AncestorOf G Z b) : ∃ n, DirectedLength G Z b n ∧ ∀ m, DirectedLength G Z b m → n ≤ m := by
  obtain ⟨z, ⟨xs, route⟩, hz⟩ := h
  exact minimum_nat_measure (DirectedLength G Z b) id xs.length ⟨z, xs, route, hz, rfl⟩

noncomputable def directedDistance {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (b : V) : Nat := by
  classical
  exact if h : AncestorOf G Z b then Classical.choose (minimum_directed_length G Z b h) else 0

theorem directedDistance_spec {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (b : V)
    (h : AncestorOf G Z b) : DirectedLength G Z b (directedDistance G Z b) ∧
      ∀ m, DirectedLength G Z b m → directedDistance G Z b ≤ m := by
  classical
  simpa only [directedDistance, dif_pos h] using Classical.choose_spec (minimum_directed_length G Z b h)

theorem directedDistance_zero_iff {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (b : V)
    (h : AncestorOf G Z b) : directedDistance G Z b = 0 ↔ Z b := by
  constructor
  · intro zero
    obtain ⟨z, xs, route, hz, length⟩ := (directedDistance_spec G Z b h).1
    rw [zero] at length
    have nil : xs = [] := by cases xs with
      | nil => rfl
      | cons a as => simp only [List.length_cons] at length; omega
    subst xs
    cases route
    exact hz
  · intro hz
    have le := (directedDistance_spec G Z b h).2 0 ⟨b, [], .nil b, hz, rfl⟩
    omega

noncomputable def colliderPotential {V : Type u} (G : MarkedGraph V) (Z : V → Prop) : List V → Nat
  | a :: b :: c :: xs =>
      (@ite Nat (Collider G a b c) (Classical.propDecidable _) (directedDistance G Z b) 0) +
        colliderPotential G Z (b :: c :: xs)
  | _ => 0

def Shortest {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (x y : V) (xs : List V) : Prop :=
  Path G Z x y xs ∧ ∀ ys, Path G Z x y ys → xs.length ≤ ys.length

def Closest {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (x y : V) (xs : List V) : Prop :=
  Shortest G Z x y xs ∧ ∀ ys, Path G Z x y ys → ys.length = xs.length →
    colliderPotential G Z (x :: xs) ≤ colliderPotential G Z (x :: ys)

theorem exists_closest {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) (x y : V) (h : ActiveConnection G Z x y) : ∃ xs, Closest G Z x y xs := by
  obtain ⟨«first», firstPath⟩ := active_connection_vertex_path G single Z x y h
  obtain ⟨shortest, shortestPath, shortestBound⟩ :=
    minimum_nat_measure (Path G Z x y) List.length «first» firstPath
  obtain ⟨best, ⟨bestPath, bestLength⟩, bestBound⟩ :=
    minimum_nat_measure (fun xs => Path G Z x y xs ∧ xs.length = shortest.length)
      (fun xs => colliderPotential G Z (x :: xs)) shortest ⟨shortestPath, rfl⟩
  refine ⟨best, ⟨bestPath, ?_⟩, ?_⟩
  · intro ys hy
    rw [bestLength]
    exact shortestBound ys hy
  · intro ys hy length
    exact bestBound ys ⟨hy, length.trans bestLength⟩

/-- This is exactly the no-shorter-order-preserving-subpath consequence used
by the minimal-path geometry. No status or ancestry invariance is inferred. -/
theorem closest_has_no_shorter_path {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    (x y : V) {xs ys : List V} (h : Closest G Z x y xs)
    (candidate : Path G Z x y ys) : ¬ ys.length < xs.length := by
  have bound := h.1.2 ys candidate
  omega

end RestrictedCausal.VertexActivePaths
