import MinimalActivePaths

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Ancestral-graph incidence geometry used in the classical minimal-path
argument (Ali--Richardson--Spirtes 2009, Lemmas 2.2, 2.4 and 3.19).
Undirected MAG edges are allowed; head incidence, rather than a false global
no-tail-tail premise, excludes an undirected edge during forward propagation.
-/

namespace RestrictedCausal.AncestralShortcutGeometry

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open SourceSelection (AncestorOf)

universe u

def HasHead {V : Type u} (G : MarkedGraph V) (x : V) : Prop := ∃ y m, G.edge x y .head m

theorem head_directed_triangle {V : Type u} (G : MarkedGraph V) (laws : AncestralLaws G)
    {a b c : V} {ma ac cc : Mark} (ab : G.edge a b ma .head)
    (bc : Directed G b c) (edge : G.edge a c ac cc) : cc = .head := by
  cases cc with
  | head => rfl
  | tail =>
      cases ac with
      | head =>
          have ca : Directed G c a := laws.symmetric a c .head .tail edge
          have reach : Reach G b a := ⟨[c, a], .cons bc (.cons ca (.nil a))⟩
          exact (laws.head_not_ancestor b a ma (laws.symmetric a b ma .head ab) reach).elim
      | tail =>
          have ca := laws.symmetric a c .tail .tail edge
          have cb := laws.symmetric b c .tail .head bc
          exact (laws.undirected_no_heads c a b .tail ca cb).elim

theorem head_nonancestor_directed_step {V : Type u} (G : MarkedGraph V) (laws : AncestralLaws G)
    (Z : V → Prop) {p q : Arrival V} (head : p.incoming = some .head)
    (incident : HasHead G p.vertex) (outside : ¬ AncestorOf G Z p.vertex)
    (step : RealStep G Z p q) : Directed G p.vertex q.vertex ∧ q.incoming = some .head ∧
      HasHead G q.vertex ∧ ¬ AncestorOf G Z q.vertex := by
  obtain ⟨outgoing, incoming, edge, mark, active⟩ := step
  have atP : ActiveAt Z (AncestorOf G Z) p.vertex .head outgoing := by
    simpa only [head] using active
  have outTail : outgoing = .tail := by
    cases outgoing with
    | tail => rfl
    | head => exact (outside (by simpa [ActiveAt] using atP)).elim
  subst outgoing
  have inHead : incoming = .head := by
    cases incoming with
    | head => rfl
    | tail =>
        obtain ⟨a, m, headEdge⟩ := incident
        exact (laws.undirected_no_heads p.vertex q.vertex a m edge headEdge).elim
  subst incoming
  exact ⟨edge, mark, ⟨p.vertex, .tail, laws.symmetric _ _ _ _ edge⟩,
    not_ancestor_successor edge outside⟩

theorem head_nonancestor_directed_route {V : Type u} (G : MarkedGraph V) (laws : AncestralLaws G)
    (Z : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (route : Route (RealStep G Z) p xs q) :
    p.incoming = some .head → HasHead G p.vertex → ¬ AncestorOf G Z p.vertex →
      Route (Directed G) p.vertex (xs.map Arrival.vertex) q.vertex ∧ q.incoming = some .head ∧
        HasHead G q.vertex ∧ ¬ AncestorOf G Z q.vertex := by
  induction route with
  | nil p => intro head incident outside; exact ⟨.nil _, head, incident, outside⟩
  | cons step tail ih =>
      intro head incident outside
      obtain ⟨directed, nextHead, nextIncident, nextOutside⟩ :=
        head_nonancestor_directed_step G laws Z head incident outside step
      obtain ⟨directedTail, lastHead, lastIncident, lastOutside⟩ := ih nextHead nextIncident nextOutside
      exact ⟨.cons directed directedTail, lastHead, lastIncident, lastOutside⟩

/-- A shortcut cannot create an inactive collider at its left join: if it
did, the original active section would be directed toward the chord's other
endpoint, contradicting the chord's head/nonancestor axiom. This is the
decisive first exclusion in the minimal-path chord lemma. -/
theorem shortcut_collider_activated {V : Type u} (G : MarkedGraph V) (laws : AncestralLaws G)
    (Z : V → Prop) {p q : Arrival V} {xs : List (Arrival V)} {m : Mark}
    («section» : Route (RealStep G Z) p xs q) (head : p.incoming = some .head)
    (chord : G.edge p.vertex q.vertex .head m) : AncestorOf G Z p.vertex := by
  classical
  by_contra outside
  obtain ⟨directed, _⟩ := head_nonancestor_directed_route G laws Z «section» head
    ⟨q.vertex, m, chord⟩ outside
  exact laws.head_not_ancestor p.vertex q.vertex m chord ⟨_, directed⟩

/-- If the left join blocks an otherwise literal shortcut, the join is
conditioned and the chord points away from it. The impossible inactive-new-
collider case is discharged above; the remaining undirected chord is
excluded using the original conditioned collider's actual outgoing head. -/
theorem blocked_left_shortcut_conditioned_parent {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (Z : V → Prop) {p q : Arrival V}
    {xs : List (Arrival V)} {outgoing incoming : Mark}
    («section» : Route (RealStep G Z) p xs q)
    (chord : G.edge p.vertex q.vertex outgoing incoming)
    (blocked : ¬ DepartureAllowed Z (AncestorOf G Z) p.vertex p.incoming outgoing) :
    Z p.vertex ∧ Directed G p.vertex q.vertex ∧ p.incoming = some .head := by
  classical
  cases hp : p.incoming with
  | none => exact (blocked (by simp [DepartureAllowed, hp])).elim
  | some previous =>
      by_cases collider : previous = .head ∧ outgoing = .head
      · have head : p.incoming = some .head := hp.trans (congrArg some collider.1)
        have activated := shortcut_collider_activated G laws Z «section» head (collider.2 ▸ chord)
        exact (blocked (by simpa [DepartureAllowed, hp, ActiveAt, collider.1, collider.2] using activated)).elim
      · have conditioned : Z p.vertex := by
          by_contra outside
          exact blocked (by simpa [DepartureAllowed, hp, ActiveAt, if_neg collider] using outside)
        cases «section» with
        | nil p => exact (laws.irreflexive p.vertex outgoing incoming chord).elim
        | @cons p «first» q rest firstStep tail =>
            obtain ⟨firstOut, firstIn, firstEdge, _, firstActive⟩ := firstStep
            have atP : ActiveAt Z (AncestorOf G Z) p.vertex previous firstOut := by
              simpa only [hp] using firstActive
            obtain ⟨previousHead, firstOutHead⟩ := ActiveWalkReduction.conditioned_active_heads conditioned atP
            have outTail : outgoing = .tail := by
              cases outgoing with
              | tail => rfl
              | head => exact (collider ⟨previousHead, rfl⟩).elim
            subst outgoing
            have inHead : incoming = .head := by
              cases incoming with
              | head => rfl
              | tail =>
                  exact (laws.undirected_no_heads p.vertex q.vertex «first».vertex firstIn chord
                    (firstOutHead ▸ firstEdge)).elim
            subst incoming
            exact ⟨conditioned, chord, hp.trans (congrArg some previousHead)⟩

theorem blocked_right_shortcut_conditioned_parent {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (Z : V → Prop) {p q : Arrival V}
    {xs : List (Arrival V)} {outgoing incoming following : Mark}
    («section» : Route (RealStep G Z) p xs q)
    (chord : G.edge p.vertex q.vertex outgoing incoming)
    (originalReady : DepartureAllowed Z (AncestorOf G Z) q.vertex q.incoming following)
    (blocked : ¬ ActiveAt Z (AncestorOf G Z) q.vertex incoming following) :
    Z q.vertex ∧ Directed G q.vertex p.vertex ∧ following = .head := by
  obtain ⟨last, ys, reversed, _⟩ := reverse_with_arrival G laws.symmetric Z (AncestorOf G Z)
    «section» (some following) originalReady
  have reverseBlocked : ¬ DepartureAllowed Z (AncestorOf G Z) q.vertex (some following) incoming := by
    intro ready
    exact blocked ((activeAt_swap Z (AncestorOf G Z) q.vertex following incoming).mp ready)
  obtain ⟨conditioned, parent, head⟩ := blocked_left_shortcut_conditioned_parent G laws Z reversed
    (laws.symmetric _ _ _ _ chord) reverseBlocked
  exact ⟨conditioned, parent, Option.some.inj head⟩

/-- Both joins cannot block the same chord. Otherwise each endpoint would
have to be a parent of the other. This supplies the exclusivity part of the
minimal-path chord classification without assuming the classification. -/
theorem shortcut_joins_not_both_blocked {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (Z : V → Prop) {p q : Arrival V}
    {xs : List (Arrival V)} {outgoing incoming following : Mark}
    («section» : Route (RealStep G Z) p xs q)
    (chord : G.edge p.vertex q.vertex outgoing incoming)
    (originalReady : DepartureAllowed Z (AncestorOf G Z) q.vertex q.incoming following) :
    ¬ ((¬ DepartureAllowed Z (AncestorOf G Z) p.vertex p.incoming outgoing) ∧
      (¬ ActiveAt Z (AncestorOf G Z) q.vertex incoming following)) := by
  rintro ⟨leftBlocked, rightBlocked⟩
  have forward := (blocked_left_shortcut_conditioned_parent G laws Z «section» chord leftBlocked).2.1
  have backward := (blocked_right_shortcut_conditioned_parent G laws Z «section» chord originalReady rightBlocked).2.1
  have «impossible» := laws.acyclic p.vertex [q.vertex, p.vertex]
    (.cons forward (.cons backward (.nil p.vertex)))
  cases «impossible»

end RestrictedCausal.AncestralShortcutGeometry
