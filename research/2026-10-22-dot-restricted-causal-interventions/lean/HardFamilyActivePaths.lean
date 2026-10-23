import HardFamilyGraphs

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

Concrete short active paths and first-edge separation certificates for
the original lower-family signature. The certificates use an explicitly
proved backward-closed set; neither d-separation nor the desired truth
table is assumed. All statements use the existing actual arrival-route
and physically-simple-path semantics.
-/

namespace RestrictedCausal.HardFamily

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation ProbabilitySource
open SourceSelection (AncestorOf)

universe u

theorem closed_contains_ancestors {V : Type u} (G : MarkedGraph V) (C A : V → Prop)
    (closed : BackwardClosed G A) (contains : ∀ v, C v → A v)
    {v : V} (ancestral : AncestorOf G C v) : A v := by
  obtain ⟨endpoint, ⟨vertices, route⟩, selected⟩ := ancestral
  have backward : ∀ {a b xs}, Route (Directed G) a xs b → A b → A a := by
    intro a b xs path
    induction path with
    | nil a => exact id
    | cons edge tail ih => intro last; exact closed _ _ edge (ih last)
  exact backward route (contains endpoint selected)

theorem active_route_in_closed_set {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C A : V → Prop) (closed : BackwardClosed G A) (contains : ∀ v, C v → A v)
    {p q : Arrival V} {xs : List (Arrival V)}
    (route : Route (RealStep G C) p xs q) (first : A p.vertex) (last : A q.vertex) :
    ∀ r ∈ p :: xs, A r.vertex :=
  route_ancestral_support G laws C (AncestorOf G C) A
    (fun _ => closed_contains_ancestors G C A closed contains) closed route first last

theorem separated_by_no_first_neighbor {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C A : V → Prop) (closed : BackwardClosed G A) (contains : ∀ v, C v → A v)
    (x y : V) (different : x ≠ y) (first : A x) (last : A y)
    (noNeighbor : ∀ z ma mb, G.edge x z ma mb → A z → False) :
    ¬ ActiveConnection G C x y := by
  rintro ⟨mark, vertices, route, simple⟩
  have support := active_route_in_closed_set G laws C A closed contains route first last
  cases route with
  | nil => exact different rfl
  | cons step rest =>
      obtain ⟨ma, mb, edge, _, _⟩ := step
      exact noNeighbor _ ma mb edge (support _ (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))

theorem separated_by_conditioned_first_tails {V : Type u} (G : MarkedGraph V)
    (laws : MixedLaws G) (C A : V → Prop) (closed : BackwardClosed G A)
    (contains : ∀ v, C v → A v) (x y : V) (different : x ≠ y)
    (first : A x) (last : A y) (yOutside : ¬ C y)
    (neighbors : ∀ z ma mb, G.edge x z ma mb → A z → C z ∧ mb = .tail) :
    ¬ ActiveConnection G C x y := by
  rintro ⟨mark, vertices, route, simple⟩
  have support := active_route_in_closed_set G laws C A closed contains route first last
  cases route with
  | nil => exact different rfl
  | @cons p next q rest step tail =>
      obtain ⟨ma, mb, edge, incoming, _⟩ := step
      have facts := neighbors next.vertex ma mb edge
        (support next (List.mem_cons_of_mem _ (List.mem_cons_self _ _)))
      cases tail with
      | nil => exact yOutside facts.1
      | cons nextStep remaining =>
          obtain ⟨outgoing, nextIncoming, nextEdge, nextMark, departure⟩ := nextStep
          have outside : ¬ C next.vertex := by
            cases outgoing <;> simpa [incoming, facts.2, ActiveAt] using departure
          exact outside facts.1

theorem single_edge_active {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {x y : V} (different : x ≠ y) (ma mb : Mark) (edge : G.edge x y ma mb) :
    ActiveConnection G C x y := by
  refine ⟨some mb, [⟨y, some mb⟩], .cons ⟨ma, mb, edge, rfl, trivial⟩ (.nil _), ?_⟩
  simpa only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
    List.nodup_singleton, and_true] using different

theorem two_edge_active {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    (x middle y : V) (different : x ≠ y) (leftDifferent : x ≠ middle) (rightDifferent : middle ≠ y)
    (ma mb nb nc : Mark) (left : G.edge x middle ma mb) (right : G.edge middle y nb nc)
    (active : ActiveAt C (AncestorOf G C) middle mb nb) : ActiveConnection G C x y := by
  refine ⟨some nc, [⟨middle, some mb⟩, ⟨y, some nc⟩],
    .cons ⟨ma, mb, left, rfl, trivial⟩ (.cons ⟨nb, nc, right, rfl, active⟩ (.nil _)), ?_⟩
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    List.mem_singleton, List.nodup_singleton, not_or, and_true]
  exact ⟨⟨leftDifferent, different⟩, rightDifferent⟩

theorem raw_fork_active {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : V → Prop)
    (x y parent : V) (different : x ≠ y)
    (left : D parent x) (right : D parent y) (outside : ¬ C parent) :
    ActiveConnection (arrowGraph D) C x y := by
  have laws := raw_arrow_mixed_laws D acyclic
  have hx : x ≠ parent := by
    intro same; subst x; exact laws.irreflexive _ .tail .head (Or.inl ⟨left, rfl, rfl⟩)
  have hy : parent ≠ y := by
    intro same; subst y; exact laws.irreflexive _ .tail .head (Or.inl ⟨right, rfl, rfl⟩)
  exact two_edge_active (arrowGraph D) C x parent y different hx hy .head .tail .tail .head
    (Or.inr ⟨left, rfl, rfl⟩) (Or.inl ⟨right, rfl, rfl⟩)
    (by simpa only [ActiveAt] using outside)

theorem raw_conditioned_collider_active {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : V → Prop)
    (x y child : V) (different : x ≠ y)
    (left : D x child) (right : D y child) (conditioned : C child) :
    ActiveConnection (arrowGraph D) C x y := by
  have laws := raw_arrow_mixed_laws D acyclic
  have hx : x ≠ child := by
    intro same; subst x; exact laws.irreflexive _ .tail .head (Or.inl ⟨left, rfl, rfl⟩)
  have hy : child ≠ y := by
    intro same; subst y; exact laws.irreflexive _ .tail .head (Or.inl ⟨right, rfl, rfl⟩)
  have ancestor : AncestorOf (arrowGraph D) C child := ⟨child, ⟨[], .nil _⟩, conditioned⟩
  exact two_edge_active (arrowGraph D) C x child y different hx hy .tail .head .head .tail
    (Or.inl ⟨left, rfl, rfl⟩) (Or.inr ⟨right, rfl, rfl⟩)
    (by simpa only [ActiveAt, if_pos ⟨rfl, rfl⟩] using ancestor)

end RestrictedCausal.HardFamily
