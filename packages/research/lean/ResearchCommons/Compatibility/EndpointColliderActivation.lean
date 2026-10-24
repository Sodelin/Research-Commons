import OriginalCanonicalSourceAdapter

/- Pinned proof compatibility: after the original cases hpm, its target incoming equality is already rewritten and is proved by rfl. All source/activity hypotheses and conclusions are unchanged. -/

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Classical inducing-path/separation proof component. A collider allowed merely
because it is ancestral to an endpoint is resolved by an actual endpoint
shortcut, not assumed to be activated by the conditioning set. This distinction
is essential for deriving the literal HPL MAG from the source adapter.
-/

namespace RestrictedCausal.InducingSeparation

open SelectedWalk CanonicalSelection LatentRoots
open SourceSelection (AncestorOf)

universe u

theorem reach_trans {V : Type u} {G : MarkedGraph V} {a b c : V}
    (hab : Reach G a b) (hbc : Reach G b c) : Reach G a c := by
  obtain ⟨xs, hx⟩ := hab
  obtain ⟨ys, hy⟩ := hbc
  exact ⟨xs ++ ys, hx.append hy⟩

theorem ancestor_mono {V : Type u} {G : MarkedGraph V} {C A : V → Prop}
    (hCA : ∀ v, C v → A v) {x : V} (hx : AncestorOf G C x) : AncestorOf G A x := by
  obtain ⟨z, hxz, hz⟩ := hx
  exact ⟨z, hxz, hCA z hz⟩

theorem ancestor_idempotent {V : Type u} {G : MarkedGraph V} {C : V → Prop}
    {x : V} (hx : AncestorOf G (AncestorOf G C) x) : AncestorOf G C x := by
  obtain ⟨y, hxy, z, hyz, hz⟩ := hx
  exact ⟨z, reach_trans hxy hyz, hz⟩

theorem not_ancestor_condition {V : Type u} {G : MarkedGraph V} {C : V → Prop}
    {x : V} (hx : ¬ AncestorOf G C x) : ¬ C x :=
  fun hc => hx ⟨x, ⟨[], .nil x⟩, hc⟩

theorem not_ancestor_successor {V : Type u} {G : MarkedGraph V} {C : V → Prop}
    {x y : V} (hxy : Directed G x y) (hx : ¬ AncestorOf G C x) :
    ¬ AncestorOf G C y := by
  rintro ⟨z, ⟨zs, hz⟩, hc⟩
  exact hx ⟨z, ⟨y :: zs, .cons hxy hz⟩, hc⟩

abbrev RealStep {V : Type u} (G : MarkedGraph V) (C : V → Prop) :=
  Transition G C (AncestorOf G C)

/-- A directed route from a nonancestor never touches the conditioning set.
Its first incidence is a tail, so any incoming arrival mark is permitted. -/
theorem directed_forward_active {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {a b : V} {xs : List V} (h : Route (Directed G) a xs b)
    (hn : ¬ AncestorOf G C a) (incoming : Option Mark) :
    ∃ last ys, Route (RealStep G C) ⟨a, incoming⟩ ys ⟨b, last⟩ := by
  revert incoming
  revert hn
  induction h with
  | nil a =>
      intro hn incoming
      exact ⟨incoming, [], .nil _⟩
  | @cons a b c xs hab hbc ih =>
      intro hn incoming
      have hnb := not_ancestor_successor hab hn
      obtain ⟨last, ys, hy⟩ := ih hnb (some .head)
      refine ⟨last, ⟨b, some .head⟩ :: ys, .cons ?_ hy⟩
      refine ⟨.tail, .head, hab, rfl, ?_⟩
      cases incoming with
      | none => trivial
      | some previous => simpa [ActiveAt] using not_ancestor_condition hn

/-- Reverse the same directed route, starting at its descendant endpoint.
The final arrival is either the initial `none` (zero length) or a tail.
This gives the precise replacement prefix for a closed endpoint collider. -/
theorem directed_reverse_active {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) {a b : V} {xs : List V} (h : Route (Directed G) a xs b)
    (hn : ¬ AncestorOf G C a) :
    ∃ last ys, Route (RealStep G C) ⟨b, none⟩ ys ⟨a, last⟩ ∧
      (last = none ∨ last = some .tail) := by
  revert hn
  induction h with
  | nil a =>
      intro hn
      exact ⟨none, [], .nil _, Or.inl rfl⟩
  | @cons a b c xs hab hbc ih =>
      intro hn
      have hnb := not_ancestor_successor hab hn
      obtain ⟨last, ys, hy, hlast⟩ := ih hnb
      have back : RealStep G C ⟨b, last⟩ ⟨a, some .tail⟩ := by
        refine ⟨.head, .tail, laws.symmetric _ _ _ _ hab, rfl, ?_⟩
        rcases hlast with rfl | rfl
        · trivial
        · simpa [ActiveAt] using not_ancestor_condition hnb
      exact ⟨some .tail, ys ++ [⟨a, some .tail⟩],
        hy.append (.cons back (.nil _)), Or.inr rfl⟩

def EndpointCondition {V : Type u} (C : V → Prop) (x y v : V) : Prop :=
  v = x ∨ v = y ∨ C v

def CompatibleArrival {V : Type u} (C : V → Prop) (p : Arrival V)
    (actual : Option Mark) : Prop :=
  actual = p.incoming ∨ actual = none ∨ (actual = some .tail ∧ ¬ C p.vertex)

def DepartureAllowed {V : Type u} (C A : V → Prop) (v : V)
    (incoming : Option Mark) (outgoing : Mark) : Prop :=
  match incoming with
  | none => True
  | some previous => ActiveAt C A v previous outgoing

/-- The only obstruction to using an original relaxed departure is an actual
head-head collider which is not an ancestor of the conditioning set. The
compatible replacement arrivals cannot introduce any other obstruction. -/
theorem departure_dichotomy {V : Type u} (G : MarkedGraph V) (C A : V → Prop)
    (p : Arrival V) (actual : Option Mark) (outgoing : Mark)
    (hc : CompatibleArrival C p actual)
    (ha : DepartureAllowed C A p.vertex p.incoming outgoing) :
    DepartureAllowed C (AncestorOf G C) p.vertex actual outgoing ∨
      (actual = some .head ∧ p.incoming = some .head ∧ outgoing = .head ∧
        A p.vertex ∧ ¬ AncestorOf G C p.vertex) := by
  classical
  rcases hc with heq | heq | ⟨heq, hn⟩
  · subst actual
    cases hpm : p.incoming with
    | none => exact Or.inl trivial
    | some previous =>
        by_cases hcol : previous = .head ∧ outgoing = .head
        · obtain ⟨rfl, rfl⟩ := hcol
          have hA : A p.vertex := by simpa [DepartureAllowed, hpm, ActiveAt] using ha
          by_cases hAn : AncestorOf G C p.vertex
          · exact Or.inl (by simpa [DepartureAllowed, hpm, ActiveAt] using hAn)
          · exact Or.inr ⟨rfl, rfl, rfl, hA, hAn⟩
        · exact Or.inl (by simpa [DepartureAllowed, hpm, ActiveAt, hcol] using ha)
  · subst actual
    exact Or.inl trivial
  · subst actual
    exact Or.inl (by simpa [DepartureAllowed, ActiveAt] using hn)

/-- Process the original finite route once. A closed collider ancestral to x
replaces the accumulated prefix by a reversed directed route from x. A closed
collider ancestral to y terminates along a directed route to y. All other
departures are copied. Thus no induction on a possibly lengthening shortcut
walk and no assumed inducing-path theorem is used. -/
theorem relaxed_route_activates {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) (x y : V) {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C (AncestorOf G (EndpointCondition C x y))) p xs q)
    (hq : q.vertex = y) (actual : Option Mark) («prefix» : List (Arrival V))
    (hp : Route (RealStep G C) ⟨x, none⟩ «prefix» ⟨p.vertex, actual⟩)
    (hc : CompatibleArrival C p actual) :
    ∃ last ys, Route (RealStep G C) ⟨x, none⟩ ys ⟨y, last⟩ := by
  revert hp hc
  revert actual «prefix»
  revert hq
  induction h with
  | nil p =>
      intro hq actual «prefix» hp hc
      exact ⟨actual, «prefix», by simpa only [hq] using hp⟩
  | @cons p «next» q rest hstep hrest ih =>
      intro hq actual «prefix» hp hc
      obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
      have hdeparture : DepartureAllowed C (AncestorOf G (EndpointCondition C x y))
          p.vertex p.incoming outgoing := hactive
      rcases departure_dichotomy G C _ p actual outgoing hc hdeparture with good | bad
      · have copied : RealStep G C ⟨p.vertex, actual⟩ «next» :=
          ⟨outgoing, incoming, hedge, hmark, good⟩
        exact ih hq «next».incoming («prefix» ++ [«next»])
          (hp.append (.cons copied (.nil _))) (Or.inl rfl)
      · obtain ⟨hactual, hphead, hout, hancestor, hnot⟩ := bad
        obtain ⟨endpoint, hreach, hendpoint⟩ := hancestor
        rcases hendpoint with hendpoint | hendpoint | hcondition
        · subst endpoint
          obtain ⟨directed, hdirected⟩ := hreach
          obtain ⟨arrival, replacement, hreplacement, harrival⟩ :=
            directed_reverse_active G laws C hdirected hnot
          have newstep : RealStep G C ⟨p.vertex, arrival⟩ «next» := by
            refine ⟨outgoing, incoming, hedge, hmark, ?_⟩
            rcases harrival with rfl | rfl
            · trivial
            · simpa [ActiveAt] using not_ancestor_condition hnot
          exact ih hq «next».incoming (replacement ++ [«next»])
            (hreplacement.append (.cons newstep (.nil _))) (Or.inl rfl)
        · subst endpoint
          obtain ⟨directed, hdirected⟩ := hreach
          obtain ⟨last, tail, htail⟩ := directed_forward_active G C hdirected hnot actual
          exact ⟨last, «prefix» ++ tail, hp.append htail⟩
        · exact (hnot ⟨endpoint, hreach, hcondition⟩).elim

theorem endpoint_relaxed_connection {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) (x y : V) {last : Option Mark} {xs : List (Arrival V)}
    (h : Route (Transition G C (AncestorOf G (EndpointCondition C x y)))
      ⟨x, none⟩ xs ⟨y, last⟩) : ActiveConnection G C x y := by
  obtain ⟨actualLast, ys, hy⟩ := relaxed_route_activates G laws C x y h rfl none []
    (.nil _) (Or.inl rfl)
  obtain ⟨r, zs, hz, hvertex, hnd⟩ := ActiveWalkReduction.active_walk_to_simple G laws C hy
  have heq : r = ⟨y, r.incoming⟩ := Arrival.eq_of_fields hvertex rfl
  rw [heq] at hz
  exact ⟨r.incoming, zs, hz, hnd⟩

end RestrictedCausal.InducingSeparation
