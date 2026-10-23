import ConditionedEdgeWalks

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

One complete direction of the classical selected-MAG representation theorem:
an actual m-connecting MAG path lifts into the SAME original DAG given Z,S.
The proof constructs every edge walk and checks every join, then applies the
already proved original-DAG loop reduction. It does not assume the graph
adapter or m-separation representation. The converse remains separate.
-/

namespace RestrictedCausal.MAGLifting

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation FramedWalk EdgeWalks HPLTarget
open SourceSelection (AncestorOf)

universe u v w

theorem mag_ancestor_source_at_head {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) (m : Mark)
    (edge : (mag D).edge x y .head m) (h : AncestorOf (mag D) Z x) :
    AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) := by
  obtain ⟨z, ⟨zs, path⟩, hz⟩ := h
  exact ⟨Observed z, mag_directed_route_lifts D path (head_not_source_ancestor D edge).2, hz⟩

/-- Conditioned joins must retain two heads. At an unconditioned join, a
new raw collider can only arise if the source vertex is ancestral to Z,S:
otherwise each MAG tail would have been preserved by the edge construction.
If both MAG incidences are heads, its actual collider activity supplies the
source ancestry through the previous lemma. -/
theorem compatible_join_active {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X)
    (previous outgoing incoming rawPrevious rawOutgoing : Mark)
    (edge : (mag D).edge x y outgoing incoming)
    (active : ActiveAt Z (AncestorOf (mag D) Z) x previous outgoing)
    («left» : BoundaryCompatible D Z x previous rawPrevious)
    («right» : BoundaryCompatible D Z x outgoing rawOutgoing) :
    ActiveAt (SelectedCondition Z) (AncestorOf (arrowGraph D.arrow) (SelectedCondition Z))
      (Observed x) rawPrevious rawOutgoing := by
  classical
  by_cases rawCollider : rawPrevious = .head ∧ rawOutgoing = .head
  · have ancestor : AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) := by
      by_contra hn
      have hp : previous = .head := by
        cases previous with
        | head => rfl
        | tail => exact Mark.noConfusion ((«left».2 hn rfl).symm.trans rawCollider.1)
      have ho : outgoing = .head := by
        cases outgoing with
        | head => rfl
        | tail => exact Mark.noConfusion ((«right».2 hn rfl).symm.trans rawCollider.2)
      have magAncestor : AncestorOf (mag D) Z x := by simpa [hp, ho, ActiveAt] using active
      have headEdge : (mag D).edge x y .head incoming := by simpa only [ho] using edge
      exact hn (mag_ancestor_source_at_head D Z x y incoming headEdge magAncestor)
    simpa only [ActiveAt, if_pos rawCollider] using ancestor
  · have hn : ¬ Z x := fun hz => rawCollider ⟨«left».1 hz, «right».1 hz⟩
    simpa only [ActiveAt, if_neg rawCollider] using hn

def IncomingCompatible {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (p : Arrival X) (actual : Option Mark) : Prop :=
  match p.incoming, actual with
  | none, none => True
  | some magMark, some rawMark => BoundaryCompatible D Z p.vertex magMark rawMark
  | _, _ => False

theorem conditioned_next_mark {X : Type u} (G : MarkedGraph X) (Z : X → Prop)
    {p q : Arrival X} {xs : List (Arrival X)}
    (h : Route (RealStep G Z) p xs q) (y : X) (hq : q.vertex = y) (hy : ¬ Z y)
    (incoming : Mark) (hp : p.incoming = some incoming) : Z p.vertex → incoming = .head := by
  intro hz
  cases h with
  | nil => exact (hy (by simpa only [hq] using hz)).elim
  | cons «first» rest =>
      obtain ⟨outgoing, nextIncoming, _, _, active⟩ := «first»
      have activityAt : ActiveAt Z (AncestorOf G Z) p.vertex incoming outgoing := by
        simpa only [hp] using active
      exact (ActiveWalkReduction.conditioned_active_heads hz activityAt).1

/-- Fold actual edge realizations along the original MAG route. The prefix
stores one fixed original source and all executed incidences; the next join
uses exactly the incoming mark produced by the preceding edge walk. -/
theorem lift_mag_route_aux {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X)
    {p q : Arrival X} {xs : List (Arrival X)}
    (h : Route (RealStep (mag D) Z) p xs q) (hq : q.vertex = y) (hy : ¬ Z y)
    (noneUnconditioned : p.incoming = none → ¬ Z p.vertex)
    (actual : Option Mark) («prefix» : List (Arrival (SourceVertex X S L)))
    (hp : Route (RealStep (arrowGraph D.arrow) (SelectedCondition Z))
      ⟨Observed x, none⟩ «prefix» ⟨Observed p.vertex, actual⟩)
    (compatible : IncomingCompatible D Z p actual) :
    ∃ last ys, Route (RealStep (arrowGraph D.arrow) (SelectedCondition Z))
      ⟨Observed x, none⟩ ys ⟨Observed y, last⟩ := by
  revert hp compatible
  revert actual «prefix»
  revert noneUnconditioned
  revert hq
  induction h with
  | nil p =>
      intro hq noneUnconditioned actual «prefix» hp compatible
      exact ⟨actual, «prefix», by simpa only [hq] using hp⟩
  | @cons p «next» q rest hstep hrest ih =>
      intro hq noneUnconditioned actual «prefix» hp compatible
      obtain ⟨outgoing, incoming, edge, hmark, active⟩ := hstep
      have headP : Z p.vertex → outgoing = .head := by
        intro hz
        cases hm : p.incoming with
        | none => exact (noneUnconditioned hm hz).elim
        | some previous =>
            have activityAt : ActiveAt Z (AncestorOf (mag D) Z) p.vertex previous outgoing := by
              simpa only [hm] using active
            exact (ActiveWalkReduction.conditioned_active_heads hz activityAt).2
      have headNext := conditioned_next_mark (mag D) Z hrest y hq hy incoming hmark
      obtain ⟨«left», «right», walk, leftBound, rightBound⟩ :=
        mag_edge_boundary_walk D Z p.vertex «next».vertex outgoing incoming edge headP headNext
      have ready : DepartureAllowed (SelectedCondition Z)
          (AncestorOf (arrowGraph D.arrow) (SelectedCondition Z))
          (Observed p.vertex) actual «left» := by
        cases hm : p.incoming with
        | none =>
            cases actual with
            | none => trivial
            | some m =>
                have «impossible» : False := by simpa only [IncomingCompatible, hm] using compatible
                exact «impossible».elim
        | some previous =>
            cases actual with
            | none => trivial
            | some rawPrevious =>
                have prevBound : BoundaryCompatible D Z p.vertex previous rawPrevious := by
                  simpa only [IncomingCompatible, hm] using compatible
                have activityAt : ActiveAt Z (AncestorOf (mag D) Z) p.vertex previous outgoing := by
                  simpa only [hm] using active
                exact compatible_join_active D Z p.vertex «next».vertex previous outgoing incoming
                  rawPrevious «left» edge activityAt prevBound leftBound
      obtain ⟨«first», firstIncoming, tail, firstEdge, tailRoute⟩ := walk
      have segment : Route (RealStep (arrowGraph D.arrow) (SelectedCondition Z))
          ⟨Observed p.vertex, actual⟩ (⟨«first», some firstIncoming⟩ :: tail)
          ⟨Observed «next».vertex, some «right»⟩ :=
        .cons ⟨«left», firstIncoming, firstEdge, rfl, ready⟩ tailRoute
      apply ih hq (fun hn => ?_) (some «right»)
        («prefix» ++ (⟨«first», some firstIncoming⟩ :: tail)) (hp.append segment)
      · exact Option.noConfusion (hn.symm.trans hmark)
      · simpa only [IncomingCompatible, hmark] using rightBound

/-- Actual m-connection in the literal selected MAG implies actual original
DAG connection given the same observed conditioning set and all selection
vertices. This is one representation direction, not full equivalence. -/
theorem mag_connection_implies_original {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) (hx : ¬ Z x) (hy : ¬ Z y)
    (h : ActiveConnection (mag D) Z x y) :
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y) := by
  obtain ⟨last, xs, path, _⟩ := h
  obtain ⟨sourceLast, ys, sourceRoute⟩ := lift_mag_route_aux D Z x y path rfl hy
    (fun _ => hx) none [] (.nil _) trivial
  obtain ⟨q, zs, simple, endpoint, nodup⟩ := ActiveWalkReduction.active_walk_to_simple
    (arrowGraph D.arrow) (original_arrow_mixed_laws D) (SelectedCondition Z) sourceRoute
  have eq : q = ⟨Observed y, q.incoming⟩ := Arrival.eq_of_fields endpoint rfl
  rw [eq] at simple
  exact ⟨q.incoming, zs, simple, nodup⟩

end RestrictedCausal.MAGLifting
