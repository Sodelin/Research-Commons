import DirectedBranchSplices

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Exact reversal of the collider-count/distance minimum, needed to handle a
shortest activation branch's first hit on either side of its collider.
This uses literal traces and genuine active routes; it does not identify a
reversed walk with an unspecified simplified path or use length minimality.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation
open DiscriminatingStatus WeakInducing
open SourceSelection (AncestorOf)

universe u

theorem collider_reverse_iff {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (a b c : V) : Collider G a b c ↔ Collider G c b a := by
  constructor
  · rintro ⟨ma, mc, «first», last⟩
    exact ⟨mc, ma, symmetric _ _ _ _ last, symmetric _ _ _ _ «first»⟩
  · rintro ⟨mc, ma, «first», last⟩
    exact ⟨ma, mc, symmetric _ _ _ _ last, symmetric _ _ _ _ «first»⟩

theorem tripleCost_reverse {V : Type u} (f : V → V → V → Nat)
    (symmetric : ∀ a b c, f a b c = f c b a) (xs : List V) :
    tripleCost f xs.reverse = tripleCost f xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases xs with
      | nil => rfl
      | cons b xs =>
          cases xs with
          | nil => rfl
          | cons c rest =>
              have «split» := tripleCost_append_pair f rest.reverse [a] c b
              have reversedTail : tripleCost f (rest.reverse ++ [c, b]) =
                  tripleCost f (b :: c :: rest) := by
                simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih
              have flip := symmetric c b a
              simp only [tripleCost] at «split»
              change tripleCost f ((a :: b :: c :: rest).reverse) =
                f a b c + tripleCost f (b :: c :: rest)
              simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
              simp only [List.cons_append, List.nil_append] 
              rw [«split», reversedTail, flip]
              omega

theorem weightedColliders_reverse {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (w : V → Nat) (xs : List V) : weightedColliders G w xs.reverse = weightedColliders G w xs := by
  classical
  apply tripleCost_reverse
  intro a b c
  rw [propext (collider_reverse_iff G symmetric a b c)]

theorem colliderCount_reverse {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (xs : List V) : colliderCount G xs.reverse = colliderCount G xs := by
  simpa only [weightedColliders_eq_count] using weightedColliders_reverse G symmetric (fun _ => 1) xs

theorem colliderPotential_reverse {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C : V → Prop) (xs : List V) : colliderPotential G C xs.reverse = colliderPotential G C xs := by
  simpa only [weightedColliders_eq_potential] using
    weightedColliders_reverse G symmetric (directedDistance G C) xs

/-- Strengthen the existing path/route conversion by retaining the actual
vertex-list equality, required for exact cost transport. -/
theorem vertex_path_route_trace {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G) (C : V → Prop) (x y : V) {xs : List V}
    (path : Path G C x y xs) :
    ∃ last states, Route (RealStep G C) ⟨x, none⟩ states ⟨y, last⟩ ∧
      states.map Arrival.vertex = xs := by
  obtain ⟨route, nodup, good⟩ := path
  cases route with
  | nil => exact ⟨none, [], .nil _, rfl⟩
  | @cons x b y rest adjacent tail =>
      obtain ⟨«left», incoming, «first»⟩ := adjacent
      obtain ⟨last, states, restRoute, «trace»⟩ := build_after_first G single C tail x «left» incoming «first» good
      exact ⟨last, ⟨b, some incoming⟩ :: states,
        .cons ⟨«left», incoming, «first», rfl, trivial⟩ restRoute,
        by simpa only [List.map_cons, «trace»]⟩

theorem vertex_path_reverse_trace {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C : V → Prop) (x y : V) {xs : List V} (path : Path G C x y xs) :
    ∃ ys, Path G C y x ys ∧ y :: ys = (x :: xs).reverse := by
  obtain ⟨last, states, actual, «trace»⟩ := vertex_path_route_trace G single C x y path
  obtain ⟨reversedLast, reversedStates, reversed, ready, physical⟩ :=
    reverse_required_arrival_trace G symmetric C (AncestorOf G C) actual none trivial
  have physical' : y :: reversedStates.map Arrival.vertex = (x :: xs).reverse := by
    simpa only [List.map_cons, «trace»] using physical
  have simple : ((⟨y, none⟩ :: reversedStates).map Arrival.vertex).Nodup := by
    change (y :: reversedStates.map Arrival.vertex).Nodup
    rw [physical']
    exact List.nodup_reverse.mpr path.2.1
  exact ⟨reversedStates.map Arrival.vertex,
    active_route_vertex_path G single C y x reversed simple, physical'⟩

theorem collider_minimal_reverse_trace {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C : V → Prop) (x y : V) {xs : List V} (minimal : ColliderMinimal G C x y xs) :
    ∃ ys, ColliderMinimal G C y x ys ∧ y :: ys = (x :: xs).reverse := by
  obtain ⟨ys, reversePath, physical⟩ := vertex_path_reverse_trace G single symmetric C x y minimal.1
  refine ⟨ys, ⟨reversePath, ?_, ?_⟩, physical⟩
  · intro zs candidate
    obtain ⟨back, backPath, backTrace⟩ := vertex_path_reverse_trace G single symmetric C y x candidate
    have bound := minimal.2.1 back backPath
    rw [backTrace, colliderCount_reverse G symmetric] at bound
    rw [physical, colliderCount_reverse G symmetric]
    exact bound
  · intro zs candidate sameCount
    obtain ⟨back, backPath, backTrace⟩ := vertex_path_reverse_trace G single symmetric C y x candidate
    have backCount : colliderCount G (x :: back) = colliderCount G (x :: xs) := by
      rw [backTrace, colliderCount_reverse G symmetric]
      simpa only [physical, colliderCount_reverse G symmetric] using sameCount
    have bound := minimal.2.2 back backPath backCount
    rw [backTrace, colliderPotential_reverse G symmetric] at bound
    rw [physical, colliderPotential_reverse G symmetric]
    exact bound

end RestrictedCausal.VertexActivePaths
