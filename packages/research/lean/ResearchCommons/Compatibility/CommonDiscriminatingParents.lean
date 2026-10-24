import OriginalMAGConnection


/- Pinned-context spelling variant: explicit original List.Sublist relation.
The actual terminal edge/arrival witnesses are named explicitly, and the
SAME cons/append identity normalizes the existing two Nodup witnesses.
Source predicates/headers/conclusion semantics are unchanged; original frozen. -/
/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Shared-separator version of the classical discriminating-prefix parent
transfer used in the order induction of Ali--Richardson--Spirtes (2009,
Lemmas 3.10 and 3.13). The prefix colliders are explicit premises, not assumed
to be invariant before the order induction. Full MAG-MEC sufficiency is not
asserted by this module.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem prefix_sublist_of_mem {V : Type u} {R : V → V → Prop}
    {a b p : V} {xs : List V} (h : Route R a xs b) (hp : p ∈ a :: xs) :
    ∃ ys, Route R a ys p ∧ List.Sublist (a :: ys) (a :: xs) := by
  revert hp
  induction h with
  | nil a =>
      intro hp
      have eq : p = a := by simpa only [List.mem_singleton] using hp
      subst p
      exact ⟨[], .nil a, List.Sublist.refl _⟩
  | @cons a «next» b xs step tail ih =>
      intro hp
      rcases List.mem_cons.mp hp with eq | mem
      · subst p
        exact ⟨[], .nil a, (List.nil_sublist _).cons_cons a⟩
      · obtain ⟨ys, route, sublist⟩ := ih mem
        exact ⟨«next» :: ys, .cons step route, sublist.cons_cons a⟩

theorem terminal_step_of_nonempty {V : Type u} {R : V → V → Prop}
    {a b : V} {xs : List V} (h : Route R a xs b) (hne : xs ≠ []) : ∃ p, R p b := by
  revert hne
  induction h with
  | nil => intro hne; exact (hne rfl).elim
  | @cons a «next» b xs step tail ih =>
      intro _
      cases xs with
      | nil => cases tail; exact ⟨a, step⟩
      | cons c cs => exact ih (by intro eq; cases eq)

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.DiscriminatingStatus

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open SourceSelection (AncestorOf)

universe u

def ColliderStep {V : Type u} (G : MarkedGraph V) (p q : Arrival V) : Prop :=
  ∃ outgoing incoming, G.edge p.vertex q.vertex outgoing incoming ∧ q.incoming = some incoming ∧
    (match p.incoming with | none => True | some previous => previous = .head ∧ outgoing = .head)

theorem collider_route_parentize {V : Type u} (G : MarkedGraph V) (y : V)
    {p q : Arrival V} {xs : List (Arrival V)} (h : Route (ColliderStep G) p xs q)
    (parents : ∀ r ∈ p :: xs, r.incoming ≠ none → Directed G r.vertex y) :
    Route (ColliderParentStep G y) p xs q := by
  revert parents
  induction h with
  | nil p => intro _; exact .nil p
  | @cons p «next» q rest step tail ih =>
      intro parents
      obtain ⟨outgoing, incoming, edge, mark, collider⟩ := step
      refine .cons ⟨outgoing, incoming, edge, mark, ?_⟩ (ih ?_)
      · cases hp : p.incoming with
        | none => trivial
        | some previous =>
            have heads : previous = .head ∧ outgoing = .head := by simpa only [hp] using collider
            exact ⟨heads.1, heads.2, parents p List.mem_cons_self (by simp [hp])⟩
      · intro r mem
        exact parents r (List.mem_cons_of_mem _ mem)

theorem collider_route_activate {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    {p q : Arrival V} {xs : List (Arrival V)} (h : Route (ColliderStep G) p xs q)
    (conditioned : ∀ r ∈ p :: xs, r.incoming ≠ none → Z r.vertex) : Route (RealStep G Z) p xs q := by
  revert conditioned
  induction h with
  | nil p => intro _; exact .nil p
  | @cons p «next» q rest step tail ih =>
      intro conditioned
      obtain ⟨outgoing, incoming, edge, mark, collider⟩ := step
      refine .cons ⟨outgoing, incoming, edge, mark, ?_⟩ (ih ?_)
      · cases hp : p.incoming with
        | none => trivial
        | some previous =>
            have heads : previous = .head ∧ outgoing = .head := by simpa only [hp] using collider
            have hz := conditioned p List.mem_cons_self (by simp [hp])
            simpa [ActiveAt, heads.1, heads.2] using conditioned_ancestor G Z p.vertex hz
      · intro r mem
        exact conditioned r (List.mem_cons_of_mem _ mem)

theorem parent_of_separated_terminal_conditioned {V : Type u} (G : MarkedGraph V)
    (Z : V → Prop) (x y : V) {p : Arrival V} {xs : List (Arrival V)}
    (h : Route (RealStep G Z) ⟨x, none⟩ xs p) (parent : Directed G p.vertex y)
    (nodup : (((⟨x, none⟩ :: xs).map Arrival.vertex) ++ [y]).Nodup)
    (sep : ¬ ActiveConnection G Z x y) : Z p.vertex := by
  classical
  by_contra notConditioned
  have ready : DepartureAllowed Z (AncestorOf G Z) p.vertex p.incoming .tail := by
    cases hp : p.incoming with
    | none => trivial
    | some previous => simpa [DepartureAllowed, hp, ActiveAt] using notConditioned
  have parentEdge : G.edge p.vertex y .tail .head := parent
  have finalStep : RealStep G Z p ⟨y, some .head⟩ :=
    ⟨.tail, .head, parentEdge, rfl, ready⟩
  apply sep
  refine ⟨some .head, xs ++ [⟨y, some .head⟩],
    h.append (.cons finalStep (.nil _)), ?_⟩
  simpa only [List.map_cons, List.map_append, List.map_nil, List.cons_append] using nodup

theorem real_terminal_head_incidence {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (Z : V → Prop) (x : V) {p : Arrival V} {xs : List (Arrival V)}
    (h : Route (RealStep G Z) ⟨x, none⟩ xs p) (head : p.incoming = some .head) :
    ∃ a m, G.edge p.vertex a .head m := by
  have nonempty : xs ≠ [] := by
    intro eq
    subst xs
    cases h
    cases head
  obtain ⟨before, outgoing, incoming, edge, mark, _⟩ := h.terminal_step_of_nonempty nonempty
  have eq : incoming = .head := Option.some.inj (mark.symm.trans head)
  subst incoming
  exact ⟨before.vertex, outgoing, symmetric _ _ _ _ edge⟩

theorem collider_prefix_parent_transfer {V : Type u} (G H : MarkedGraph V)
    (laws : AncestralLaws H) (Z : V → Prop) (x y : V)
    {p : Arrival V} {xs : List (Arrival V)}
    (prefixG : Route (ColliderStep G) ⟨x, none⟩ xs p)
    (prefixH : Route (ColliderStep H) ⟨x, none⟩ xs p)
    (heads : ∀ r ∈ xs, r.incoming = some .head)
    (parentsG : ∀ r ∈ xs, Directed G r.vertex y)
    (adjacentH : ∀ r ∈ xs, Adjacent H r.vertex y)
    (nodup : (((⟨x, none⟩ :: xs).map Arrival.vertex) ++ [y]).Nodup)
    (sepG : ¬ ActiveConnection G Z x y) (sepH : ¬ ActiveConnection H Z x y) :
    ∀ r ∈ xs, Directed H r.vertex y := by
  have parentPrefix := collider_route_parentize G y prefixG (by
    intro r mem notRoot
    rcases List.mem_cons.mp mem with eq | mem
    · subst r
      exact (notRoot rfl).elim
    · exact parentsG r mem)
  have activeG := collider_parent_prefix_activated G Z x y parentPrefix [] (.nil _) nodup sepG
  have allConditioned : ∀ r ∈ xs, Z r.vertex := by
    intro r mem
    obtain ⟨«prefix», route, sub⟩ := activeG.prefix_sublist_of_mem (List.mem_cons_of_mem _ mem)
    have shortNodup : (((⟨x, none⟩ :: «prefix»).map Arrival.vertex) ++ [y]).Nodup :=
      nodup.sublist ((sub.map Arrival.vertex).append (List.Sublist.refl [y]))
    exact parent_of_separated_terminal_conditioned G Z x y route (parentsG r mem) shortNodup sepG
  have activeH := collider_route_activate H Z prefixH (by
    intro r mem notRoot
    rcases List.mem_cons.mp mem with eq | mem
    · subst r
      exact (notRoot rfl).elim
    · exact allConditioned r mem)
  intro r mem
  obtain ⟨«prefix», route, sub⟩ := activeH.prefix_sublist_of_mem (List.mem_cons_of_mem _ mem)
  have shortNodup : (((⟨x, none⟩ :: «prefix»).map Arrival.vertex) ++ [y]).Nodup :=
    nodup.sublist ((sub.map Arrival.vertex).append (List.Sublist.refl [y]))
  obtain ⟨outgoing, incoming, edge⟩ := adjacentH r mem
  have outTail : outgoing = .tail := by
    cases outgoing with
    | tail => rfl
    | head =>
        apply False.elim
        apply sepH
        have ready : DepartureAllowed Z (AncestorOf H Z) r.vertex r.incoming .head := by
          simpa [DepartureAllowed, heads r mem, ActiveAt] using
            conditioned_ancestor H Z r.vertex (allConditioned r mem)
        refine ⟨some incoming, «prefix» ++ [⟨y, some incoming⟩],
          route.append (.cons ⟨.head, incoming, edge, rfl, ready⟩ (.nil _)), ?_⟩
        simpa only [List.map_cons, List.map_append, List.map_nil, List.cons_append] using shortNodup
  subst outgoing
  cases incoming with
  | head => exact edge
  | tail =>
      obtain ⟨a, m, incidence⟩ := real_terminal_head_incidence H laws.symmetric Z x route (heads r mem)
      exact (laws.undirected_no_heads r.vertex y a m edge incidence).elim

end RestrictedCausal.DiscriminatingStatus
