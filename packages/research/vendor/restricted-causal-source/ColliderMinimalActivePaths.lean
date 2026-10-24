import MinimalActivePaths

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The collider-count-first minimum used in the binary atomic-completeness
witness. It is NOT the shortest-length Closest predicate used for MAG MECs.
The activation-branch intersection/splicing theorems are not assumed here
and remain separate proof obligations. Classical attribution: Meek (1995),
Lemma 9, following Geiger--Verma--Pearl; explicit minimum proof by dot.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation DiscriminatingStatus

universe u

noncomputable def colliderCount {V : Type u} (G : MarkedGraph V) : List V → Nat
  | a :: b :: c :: xs =>
      (@ite Nat (Collider G a b c) (Classical.propDecidable _) 1 0) +
        colliderCount G (b :: c :: xs)
  | _ => 0

def ColliderMinimal {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    (x y : V) (xs : List V) : Prop :=
  Path G C x y xs ∧
    (∀ ys, Path G C x y ys → colliderCount G (x :: xs) ≤ colliderCount G (x :: ys)) ∧
    (∀ ys, Path G C x y ys → colliderCount G (x :: ys) = colliderCount G (x :: xs) →
      colliderPotential G C (x :: xs) ≤ colliderPotential G C (x :: ys))

theorem exists_collider_minimal {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G) (C : V → Prop) (x y : V)
    (connected : ActiveConnection G C x y) :
    ∃ xs, ColliderMinimal G C x y xs := by
  obtain ⟨initial, initialPath⟩ := active_connection_vertex_path G single C x y connected
  obtain ⟨sparse, sparsePath, sparseBound⟩ :=
    minimum_nat_measure (Path G C x y) (fun xs => colliderCount G (x :: xs))
      initial initialPath
  obtain ⟨best, ⟨bestPath, bestCount⟩, bestBound⟩ :=
    minimum_nat_measure
      (fun xs => Path G C x y xs ∧ colliderCount G (x :: xs) = colliderCount G (x :: sparse))
      (fun xs => colliderPotential G C (x :: xs)) sparse ⟨sparsePath, rfl⟩
  refine ⟨best, bestPath, ?_, ?_⟩
  · intro ys path
    rw [bestCount]
    exact sparseBound ys path
  · intro ys path equalCount
    exact bestBound ys ⟨path, equalCount.trans bestCount⟩

theorem collider_minimal_rejects_fewer {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) (x y : V) {xs ys : List V}
    (minimal : ColliderMinimal G C x y xs) (candidate : Path G C x y ys)
    (fewer : colliderCount G (x :: ys) < colliderCount G (x :: xs)) : False := by
  have bound := minimal.2.1 ys candidate
  omega

theorem collider_minimal_rejects_closer {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) (x y : V) {xs ys : List V}
    (minimal : ColliderMinimal G C x y xs) (candidate : Path G C x y ys)
    (sameCount : colliderCount G (x :: ys) = colliderCount G (x :: xs))
    (closer : colliderPotential G C (x :: ys) < colliderPotential G C (x :: xs)) : False := by
  have bound := minimal.2.2 ys candidate sameCount
  omega

end RestrictedCausal.VertexActivePaths
