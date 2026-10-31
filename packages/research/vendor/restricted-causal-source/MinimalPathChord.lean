import AncestralShortcutGeometry

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The global shortest-path chord obstruction, assembled from actual prefix,
section and suffix routes. Its shortened path is explicitly constructed and
its physical simplicity follows from a literal vertex sublist. This is a
classical MAG-equivalence proof component, not a new identifiability result.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem terminal_singleton_sublist {V : Type u} {R : V → V → Prop}
    {a b : V} {xs : List V} (h : Route R a xs b) (hne : xs ≠ []) : [b] <+ xs := by
  revert hne
  induction h with
  | nil => intro hne; exact (hne rfl).elim
  | @cons a «next» b xs step tail ih =>
      intro _
      cases xs with
      | nil => cases tail; exact List.Sublist.refl _
      | cons c cs => exact (ih (by intro eq; cases eq)).cons «next»

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.AncestralShortcutGeometry

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget DiscriminatingStatus
open SourceSelection (AncestorOf)
open VertexActivePaths

universe u

theorem shortest_chord_cannot_connect {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G) (Z : V → Prop) (x y : V)
    {p q : Arrival V} {«prefix» «section» suffix : List (Arrival V)} {last : Option Mark}
    {outgoing incoming : Mark}
    (hp : Route (RealStep G Z) ⟨x, none⟩ «prefix» p)
    (hs : Route (RealStep G Z) p «section» q) (long : 1 < «section».length)
    (chord : G.edge p.vertex q.vertex outgoing incoming)
    (leftReady : DepartureAllowed Z (AncestorOf G Z) p.vertex p.incoming outgoing)
    (rightRoute : Route (RealStep G Z) ⟨q.vertex, some incoming⟩ suffix ⟨y, last⟩)
    (minimal : Shortest G Z x y ((«prefix» ++ «section» ++ suffix).map Arrival.vertex)) : False := by
  have nonempty : «section» ≠ [] := by intro eq; simp only [eq, List.length_nil] at long; omega
  have middleSub : [q.vertex] <+ «section».map Arrival.vertex := by
    simpa only [List.map_cons, List.map_nil] using (hs.terminal_singleton_sublist nonempty).map Arrival.vertex
  have verticesSub : (x :: («prefix».map Arrival.vertex ++ [q.vertex] ++ suffix.map Arrival.vertex)) <+
      (x :: («prefix».map Arrival.vertex ++ «section».map Arrival.vertex ++ suffix.map Arrival.vertex)) :=
    ((middleSub.append_left («prefix».map Arrival.vertex)).append_right (suffix.map Arrival.vertex)).cons_cons x
  have sourceNodup : (x :: («prefix».map Arrival.vertex ++ «section».map Arrival.vertex ++
      suffix.map Arrival.vertex)).Nodup := by
    simpa only [List.map_append] using minimal.1.2.1
  have shortenedNodup : ((⟨x, none⟩ :: («prefix» ++ (⟨q.vertex, some incoming⟩ :: suffix))).map Arrival.vertex).Nodup := by
    simpa only [List.map_cons, List.map_append, List.map_nil, List.singleton_append, List.append_assoc] using
      sourceNodup.sublist verticesSub
  have chordStep : RealStep G Z p ⟨q.vertex, some incoming⟩ :=
    ⟨outgoing, incoming, chord, rfl, leftReady⟩
  have shortenedRoute := hp.append (.cons chordStep rightRoute)
  have shortenedPath := active_route_vertex_path G single Z x y shortenedRoute shortenedNodup
  have lengthBound := minimal.2 _ shortenedPath
  simp only [List.length_map, List.length_append, List.length_cons] at lengthBound
  omega

/-- Every nonconsecutive chord on a shortest m-connecting path is forced by
at least one conditioned endpoint, and points away from that endpoint. The
local lemmas also show that both endpoints cannot be blocking joins. This
form keeps endpoint cases explicit and is suitable for discriminating-
section construction without assuming a global graphical criterion. -/
theorem shortest_chord_conditioned_parent {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x y : V)
    {p q : Arrival V} {«prefix» «section» suffix : List (Arrival V)} {last : Option Mark}
    {outgoing incoming : Mark}
    (hp : Route (RealStep G Z) ⟨x, none⟩ «prefix» p)
    (hs : Route (RealStep G Z) p «section» q)
    (ht : Route (RealStep G Z) q suffix ⟨y, last⟩)
    (long : 1 < «section».length) (chord : G.edge p.vertex q.vertex outgoing incoming)
    (minimal : Shortest G Z x y ((«prefix» ++ «section» ++ suffix).map Arrival.vertex)) :
    (Z p.vertex ∧ Directed G p.vertex q.vertex) ∨ (Z q.vertex ∧ Directed G q.vertex p.vertex) := by
  classical
  by_cases leftReady : DepartureAllowed Z (AncestorOf G Z) p.vertex p.incoming outgoing
  · cases ht with
    | nil =>
        exact (shortest_chord_cannot_connect G single Z x y hp hs long chord leftReady (.nil _) minimal).elim
    | @cons q «next» end rest «first» tail =>
        obtain ⟨following, nextIncoming, edge, mark, originalReady⟩ := «first»
        by_cases rightReady : ActiveAt Z (AncestorOf G Z) q.vertex incoming following
        · have rebased : RealStep G Z ⟨q.vertex, some incoming⟩ «next» :=
            ⟨following, nextIncoming, edge, mark, rightReady⟩
          exact (shortest_chord_cannot_connect G single Z x y hp hs long chord leftReady
            (.cons rebased tail) minimal).elim
        · have blocked := blocked_right_shortcut_conditioned_parent G laws Z hs chord originalReady rightReady
          exact Or.inr ⟨blocked.1, blocked.2.1⟩
  · have blocked := blocked_left_shortcut_conditioned_parent G laws Z hs chord leftReady
    exact Or.inl ⟨blocked.1, blocked.2.1⟩

end RestrictedCausal.AncestralShortcutGeometry
