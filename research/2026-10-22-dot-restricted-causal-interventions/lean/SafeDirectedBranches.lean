import ActivationBranchDistances

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Directed activation branches as actual marked active routes, with exact
vertex traces and explicit head/tail changes at splices. These primitives
do not assert branch disjointness or the full nonzero-minor theorem.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation
open SourceSelection (AncestorOf)

universe u

def DeparturesOutside {V : Type u} (C : V → Prop) : V → List V → Prop
  | _, [] => True
  | a, b :: rest => ¬ C a ∧ DeparturesOutside C b rest

theorem minimum_directed_departures_outside {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) {a finish : V} {xs : List V}
    (path : MinimumDirectedPath G C a xs finish) : DeparturesOutside C a xs := by
  induction xs generalizing a with
  | nil => trivial
  | cons «next» rest ih =>
      exact ⟨minimum_directed_positive_outside G C path,
        ih (minimum_directed_tail G C path)⟩

theorem departures_outside_prefix {V : Type u} (C : V → Prop)
    (front back : List V) (a : V)
    (safe : DeparturesOutside C a (front ++ back)) : DeparturesOutside C a front := by
  induction front generalizing a with
  | nil => trivial
  | cons «next» rest ih => exact ⟨safe.1, ih «next» safe.2⟩

theorem directed_safe_head_route {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {a b : V} {xs : List V} (route : Route (Directed G) a xs b)
    (safe : DeparturesOutside C a xs) :
    Route (RealStep G C) ⟨a, some .head⟩
      (xs.map (fun v => (⟨v, some .head⟩ : Arrival V))) ⟨b, some .head⟩ := by
  revert safe
  induction route with
  | nil a => intro _; exact .nil _
  | @cons a «next» b rest edge tail ih =>
      intro safe
      refine .cons ⟨.tail, .head, edge, rfl, ?_⟩ (ih safe.2)
      simpa [ActiveAt] using safe.1

/-- Changing an internal arrival to a head either leaves a noncollider
outside C or creates a collider with an actual certified C descendant.
An original initial endpoint separately supplies its exclusion from C. -/
theorem head_replacement_departure {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) (v : V) (incoming : Option Mark) (outgoing : Mark)
    (activated : AncestorOf G C v)
    (original : DepartureAllowed C (AncestorOf G C) v incoming outgoing)
    (initialOutside : incoming = none → ¬ C v) :
    DepartureAllowed C (AncestorOf G C) v (some .head) outgoing := by
  cases outgoing with
  | head => simpa [DepartureAllowed, ActiveAt] using activated
  | tail =>
      have outside : ¬ C v := by
        cases incoming with
        | none => exact initialOutside rfl
        | some mark => simpa [DepartureAllowed, ActiveAt] using original
      simpa [DepartureAllowed, ActiveAt] using outside

theorem tail_replacement_departure {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) (v : V) (outgoing : Mark) (outside : ¬ C v) :
    DepartureAllowed C (AncestorOf G C) v (some .tail) outgoing := by
  simpa [DepartureAllowed, ActiveAt] using outside

/-- Retain every subsequent actual arrival state. Only the initial incoming
mark is changed; a zero-length suffix is allowed and requires no activity. -/
theorem rebuild_suffix_head {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {p q : Arrival V} {xs : List (Arrival V)} (route : Route (RealStep G C) p xs q)
    (activated : AncestorOf G C p.vertex)
    (initialOutside : p.incoming = none → ¬ C p.vertex) :
    ∃ last, Route (RealStep G C) ⟨p.vertex, some .head⟩ xs ⟨q.vertex, last⟩ := by
  cases route with
  | nil p => exact ⟨some .head, .nil _⟩
  | @cons p «next» q rest step tail =>
      obtain ⟨outgoing, incoming, edge, mark, active⟩ := step
      exact ⟨q.incoming, .cons ⟨outgoing, incoming, edge, mark,
        head_replacement_departure G C p.vertex p.incoming outgoing
          activated active initialOutside⟩ tail⟩

theorem rebuild_suffix_tail {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {p q : Arrival V} {xs : List (Arrival V)} (route : Route (RealStep G C) p xs q)
    (outside : ¬ C p.vertex) :
    ∃ last, Route (RealStep G C) ⟨p.vertex, some .tail⟩ xs ⟨q.vertex, last⟩ := by
  cases route with
  | nil p => exact ⟨some .tail, .nil _⟩
  | @cons p «next» q rest step tail =>
      obtain ⟨outgoing, incoming, edge, mark, _⟩ := step
      exact ⟨q.incoming, .cons ⟨outgoing, incoming, edge, mark,
        tail_replacement_departure G C p.vertex outgoing outside⟩ tail⟩

end RestrictedCausal.VertexActivePaths
