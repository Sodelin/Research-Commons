import ActivationBranchPairExclusion

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual trek decomposition of a collider-free path in the original arrow
graph. It constructs the two outward directed arms and proves uniqueness
of the segment source under acyclicity. Singleton segments are included.
Splitting a whole minimum at its ordered colliders and assigning circuit
gates/ranks on the resulting disjoint segments remain separate work.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation OriginalProjection
open DiscriminatingStatus WeakInducing

universe u

theorem arrow_single_edges {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) : SingleEdges (arrowGraph D) := by
  intro a b ma mb na nb first second
  rcases first with ⟨ab, maTail, mbHead⟩ | ⟨ba, maHead, mbTail⟩
  · rcases second with ⟨_, naTail, nbHead⟩ | ⟨ba, _, _⟩
    · exact ⟨maTail.trans naTail.symm, mbHead.trans nbHead.symm⟩
    · have impossible := acyclic a [b, a] (.cons ab (.cons ba (.nil a)))
      cases impossible
  · rcases second with ⟨ab, _, _⟩ | ⟨_, naHead, nbTail⟩
    · have impossible := acyclic a [b, a] (.cons ab (.cons ba (.nil a)))
      cases impossible
    · exact ⟨maHead.trans naHead.symm, mbTail.trans nbTail.symm⟩

theorem arrow_directed_acyclic {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) :
    ∀ a xs, Route (Directed (arrowGraph D)) a xs a → xs = [] := by
  intro a xs route
  have raw := route.map id (fun p q edge => (arrow_directed_exact D p q).mp edge)
  have empty := acyclic a (xs.map id) raw
  simpa only [List.map_id] using empty

theorem arrow_adjacent_directions {V : Type u} (D : V → V → Prop) {a b : V}
    (adjacent : Adjacent (arrowGraph D) a b) : D a b ∨ D b a := by
  obtain ⟨ma, mb, edge⟩ := adjacent
  rcases edge with ⟨forward, _, _⟩ | ⟨backward, _, _⟩
  · exact Or.inl forward
  · exact Or.inr backward

theorem arrow_heads_collider {V : Type u} (D : V → V → Prop) {a b c : V}
    (left : D a b) (right : D c b) : Collider (arrowGraph D) a b c :=
  ⟨.tail, .tail, Or.inl ⟨left, rfl, rfl⟩, Or.inr ⟨right, rfl, rfl⟩⟩

theorem arrow_adjacent_colliders_impossible {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (a b c d : V)
    (atB : Collider (arrowGraph D) a b c) (atC : Collider (arrowGraph D) b c d) : False := by
  obtain ⟨ma, mc, _, right⟩ := atB
  obtain ⟨mb, md, left, _⟩ := atC
  have intoB : D c b := by
    rcases right with ⟨_, impossible, _⟩ | ⟨edge, _, _⟩
    · exact Mark.noConfusion impossible
    · exact edge
  have intoC : D b c := by
    rcases left with ⟨edge, _, _⟩ | ⟨_, _, impossible⟩
    · exact edge
    · exact Mark.noConfusion impossible
  have impossible := acyclic b [c, b] (.cons intoC (.cons intoB (.nil b)))
  cases impossible

theorem no_colliders_tail {V : Type u} (G : MarkedGraph V) (a : V) (xs : List V)
    (good : AllTriples (fun p q r => ¬ Collider G p q r) (a :: xs)) :
    AllTriples (fun p q r => ¬ Collider G p q r) xs := by
  cases xs with
  | nil => trivial
  | cons b xs =>
      cases xs with
      | nil => trivial
      | cons c rest => exact good.2

/-- Once a collider-free segment points forward, it cannot turn backward.
The proof derives each actual original arrow rather than selecting a new
orientation for the graph. -/
theorem collider_free_after_forward {V : Type u} (D : V → V → Prop)
    {b y : V} {xs : List V} (route : Route (Adjacent (arrowGraph D)) b xs y) :
    ∀ a, D a b → AllTriples (fun p q r => ¬ Collider (arrowGraph D) p q r) (a :: b :: xs) →
      Route D b xs y := by
  induction route with
  | nil b => intro _ _ _; exact .nil b
  | @cons b c y rest adjacent tail ih =>
      intro a incoming good
      have outgoing : D b c := by
        rcases arrow_adjacent_directions D adjacent with forward | backward
        · exact forward
        · exact (good.1 (arrow_heads_collider D incoming backward)).elim
      exact .cons outgoing (ih b outgoing good.2)

/-- The chosen source and both arms are constructed from the original
segment. `left` runs outward from the source to x, `right` to y. -/
theorem collider_free_trek {V : Type u} (D : V → V → Prop)
    {x y : V} {xs : List V} (route : Route (Adjacent (arrowGraph D)) x xs y)
    (good : AllTriples (fun p q r => ¬ Collider (arrowGraph D) p q r) (x :: xs)) :
    ∃ source left right, Route D source left x ∧ Route D source right y ∧
      x :: xs = (source :: left).reverse ++ right := by
  revert good
  induction route with
  | nil x => intro _; exact ⟨x, [], [], .nil x, .nil x, rfl⟩
  | @cons x next y rest adjacent tail ih =>
      intro good
      rcases arrow_adjacent_directions D adjacent with forward | backward
      · have directed := collider_free_after_forward D tail x forward good
        exact ⟨x, [], next :: rest, .nil x, .cons forward directed, rfl⟩
      · obtain ⟨source, left, right, leftRoute, rightRoute, trace⟩ :=
          ih (no_colliders_tail (arrowGraph D) x (next :: rest) good)
        refine ⟨source, left ++ [x], right,
          leftRoute.append (.cons backward (.nil x)), rightRoute, ?_⟩
        calc
          x :: next :: rest = x :: ((source :: left).reverse ++ right) := by rw [trace]
          _ = (source :: (left ++ [x])).reverse ++ right := by
            simp only [List.cons_append, List.reverse_append, List.reverse_cons,
              List.reverse_nil, List.nil_append, List.singleton_append, List.append_assoc]

theorem trek_source_reaches_each {V : Type u} (D : V → V → Prop)
    {source x y : V} {left right vertices : List V}
    (leftRoute : Route D source left x) (rightRoute : Route D source right y)
    (trace : vertices = (source :: left).reverse ++ right) :
    ∀ vertex ∈ vertices, ∃ path, Route D source path vertex := by
  intro vertex member
  rw [trace] at member
  rcases List.mem_append.mp member with onLeft | onRight
  · exact leftRoute.prefix_of_mem (List.mem_reverse.mp onLeft)
  · exact rightRoute.prefix_of_mem (List.mem_cons_of_mem _ onRight)

theorem raw_reach_antisymmetric {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) {a b : V}
    {outward backward : List V} (first : Route D a outward b) (last : Route D b backward a) : a = b := by
  have empty := acyclic a (outward ++ backward) (first.append last)
  cases outward with
  | nil => cases first; rfl
  | cons next rest => cases empty

/-- In an acyclic original graph this is the unique vertex of the segment
that can reach every segment vertex. Extra unused arrows are not deleted. -/
theorem collider_free_trek_unique_source {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = [])
    {x y : V} {xs : List V} (route : Route (Adjacent (arrowGraph D)) x xs y)
    (good : AllTriples (fun p q r => ¬ Collider (arrowGraph D) p q r) (x :: xs)) :
    ∃ source left right, Route D source left x ∧ Route D source right y ∧
      x :: xs = (source :: left).reverse ++ right ∧
      ∀ other ∈ x :: xs, (∀ vertex ∈ x :: xs, ∃ path, Route D other path vertex) → other = source := by
  obtain ⟨source, left, right, leftRoute, rightRoute, trace⟩ := collider_free_trek D route good
  refine ⟨source, left, right, leftRoute, rightRoute, trace, ?_⟩
  intro other member allReach
  have sourceMember : source ∈ x :: xs := by
    rw [trace]
    exact List.mem_append.mpr (Or.inl (List.mem_reverse.mpr List.mem_cons_self))
  obtain ⟨outward, forward⟩ := trek_source_reaches_each D leftRoute rightRoute trace other member
  obtain ⟨backward, reverse⟩ := allReach source sourceMember
  exact (raw_reach_antisymmetric D acyclic forward reverse).symm

end RestrictedCausal.VertexActivePaths
