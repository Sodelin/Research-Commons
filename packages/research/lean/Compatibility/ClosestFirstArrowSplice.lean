import ClosestFirstArrowFlank

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The actual two-boundary splice used in the remaining adjacent-boundaries
case. Reverse the right retained arm with its REQUIRED incoming mark,
retain its exact physical trace, and join the two arms through the first
directed child. No active-walk simplification for an undirected MAG is
assumed. The separate finite-list lemmas preserve vertex simplicity.
Classical attribution: Ali--Richardson--Spirtes (2009), Lemma 3.25.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing
open SourceSelection (AncestorOf)

universe u

theorem reverse_required_arrival_trace {V : Type u} (G : MarkedGraph V)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C A : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (route : Route (Transition G C A) p xs q) (actual : Option Mark)
    (ready : match actual with
      | none => True
      | some outgoing => DepartureAllowed C A q.vertex q.incoming outgoing) :
    ∃ last ys, Route (Transition G C A) ⟨q.vertex, actual⟩ ys ⟨p.vertex, last⟩ ∧
      (match p.incoming with
      | none => True
      | some previous => DepartureAllowed C A p.vertex last previous) ∧
      q.vertex :: ys.map Arrival.vertex = ((p :: xs).map Arrival.vertex).reverse := by
  revert ready actual
  induction route with
  | nil p =>
      intro actual ready
      refine ⟨actual, [], .nil _, ?_, ?_⟩
      · cases arrival : p.incoming with
        | none => trivial
        | some previous =>
            cases actual with
            | none => trivial
            | some outgoing =>
                have active : ActiveAt C A p.vertex previous outgoing := by
                  simpa only [DepartureAllowed, arrival] using ready
                exact (activeAt_swap C A p.vertex previous outgoing).mp active
      · simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append]
  | @cons p «next» q rest step tail ih =>
      intro actual ready
      obtain ⟨outgoing, incoming, edge, mark, active⟩ := step
      obtain ⟨last, ys, reversed, compatible, «trace»⟩ := ih actual ready
      have backward : Transition G C A ⟨«next».vertex, last⟩ ⟨p.vertex, some outgoing⟩ :=
        ⟨incoming, outgoing, symmetric _ _ _ _ edge, rfl, by cases last <;> simpa only [mark, DepartureAllowed] using compatible⟩
      refine ⟨some outgoing, ys ++ [⟨p.vertex, some outgoing⟩],
        reversed.append (.cons backward (.nil _)), ?_, ?_⟩
      · cases arrival : p.incoming with
        | none => trivial
        | some previous =>
            have atP : ActiveAt C A p.vertex previous outgoing := by simpa only [arrival] using active
            exact (activeAt_swap C A p.vertex previous outgoing).mp atP
      · calc
          q.vertex :: (ys ++ [({ vertex := p.vertex, incoming := some outgoing } : Arrival V)]).map Arrival.vertex =
              (q.vertex :: ys.map Arrival.vertex) ++ [p.vertex] := by
                simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append]
          _ = ((«next» :: rest).map Arrival.vertex).reverse ++ [p.vertex] := by rw [«trace»]
          _ = ((p :: «next» :: rest).map Arrival.vertex).reverse := by
            simp only [List.map_cons, List.reverse_cons]

theorem nodup_insert_fresh {V : Type u} («left» «right» : List V) (d : V)
    (simple : («left» ++ «right»).Nodup) (fresh : d ∉ «left» ++ «right») :
    («left» ++ (d :: «right»)).Nodup := by
  induction «left» with
  | nil => exact List.Nodup.cons fresh simple
  | cons a «left» ih =>
      obtain ⟨outside, tail⟩ := List.nodup_cons.mp simple
      refine List.Nodup.cons ?_ (ih tail (fun member => fresh (List.mem_cons_of_mem _ member)))
      intro member
      rcases List.mem_append.mp member with member | member
      · exact outside (List.mem_append.mpr (Or.inl member))
      · rcases List.mem_cons.mp member with same | member
        · apply fresh
          exact List.mem_cons.mpr (Or.inl same.symm)
        · exact outside (List.mem_append.mpr (Or.inr member))

/-- Construct the shorter candidate itself from two retained real arms.
The retained-vertex simplicity and child's freshness are explicit and are
later supplied by extraction from the original simple path. The source
query, original source graph and target endpoints remain unchanged. -/
theorem two_boundary_splice {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x y d : V)
    {a r : Arrival V} {«left» «right» : List (Arrival V)} {leftOut rightOut : Mark}
    (leftArm : Route (RealStep G Z) ⟨x, none⟩ «left» a)
    (rightArm : Route (RealStep G Z) ⟨y, none⟩ «right» r)
    (leftEdge : G.edge a.vertex d leftOut .head)
    (rightEdge : G.edge r.vertex d rightOut .head)
    (leftReady : DepartureAllowed Z (AncestorOf G Z) a.vertex a.incoming leftOut)
    (rightReady : DepartureAllowed Z (AncestorOf G Z) r.vertex r.incoming rightOut)
    (activated : AncestorOf G Z d)
    (simple : (((⟨x, none⟩ :: «left»).map Arrival.vertex) ++
      ((⟨y, none⟩ :: «right»).map Arrival.vertex).reverse).Nodup)
    (fresh : d ∉ (((⟨x, none⟩ :: «left»).map Arrival.vertex) ++
      ((⟨y, none⟩ :: «right»).map Arrival.vertex).reverse)) :
    ∃ vertices, Path G Z x y vertices ∧
      x :: vertices = ((⟨x, none⟩ :: «left»).map Arrival.vertex) ++
        [d] ++ ((⟨y, none⟩ :: «right»).map Arrival.vertex).reverse ∧
      vertices.length = «left».length + «right».length + 2 := by
  obtain ⟨last, reversed, rightRoute, _, rightTrace⟩ :=
    reverse_required_arrival_trace G laws.symmetric Z (AncestorOf G Z) rightArm (some rightOut) rightReady
  let childState : Arrival V := ⟨d, some .head⟩
  let rightState : Arrival V := ⟨r.vertex, some rightOut⟩
  have «first» : RealStep G Z a childState := ⟨leftOut, .head, leftEdge, rfl, leftReady⟩
  have second : RealStep G Z childState rightState :=
    ⟨.head, rightOut, laws.symmetric _ _ _ _ rightEdge, rfl, by
      simpa only [childState, ActiveAt, and_self, if_true] using activated⟩
  let states := «left» ++ (childState :: rightState :: reversed)
  have route : Route (RealStep G Z) ⟨x, none⟩ states ⟨y, last⟩ :=
    leftArm.append (.cons «first» (.cons second rightRoute))
  have «trace» : ((⟨x, none⟩ :: states).map Arrival.vertex) =
      ((⟨x, none⟩ :: «left»).map Arrival.vertex) ++ [d] ++
        ((⟨y, none⟩ :: «right»).map Arrival.vertex).reverse := by
    simpa only [states, childState, rightState, List.map_cons, List.map_append, List.map_nil,
      List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      congrArg (fun tail => ((⟨x, none⟩ :: «left»).map Arrival.vertex) ++ [d] ++ tail) rightTrace
  have candidateSimple : ((⟨x, none⟩ :: states).map Arrival.vertex).Nodup := by
    rw [«trace»]
    simpa only [List.append_assoc, List.singleton_append] using
      nodup_insert_fresh ((⟨x, none⟩ :: «left»).map Arrival.vertex)
        (((⟨y, none⟩ :: «right»).map Arrival.vertex).reverse) d simple fresh
  refine ⟨states.map Arrival.vertex, active_route_vertex_path G single Z x y route candidateSimple,
    by simpa only [List.map_cons] using «trace», ?_⟩
  have rightLength := congrArg List.length rightTrace
  simp only [List.length_cons, List.length_map, List.length_reverse] at rightLength
  simp only [states, List.length_map, List.length_append, List.length_cons]
  omega

end RestrictedCausal.VertexActivePaths
