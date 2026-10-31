import MinimumDirectedPathTransfer

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Geometry used specifically in the missing closest-path first-arrow proof.
An outgoing child of an unconditioned collider cannot occur anywhere on
the same shortest active path. This is derived from actual route splits
and the proved chord obstruction, not imposed as an off-path assumption.
The boundary incidence lemma supplies the unchanged collider status at
each join of the proposed closer replacement. Classical attribution:
Ali--Richardson--Spirtes (2009), Lemma 3.25 and Corollary 3.27.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem split_at_mem {V : Type u} {R : V → V → Prop} {p q r : V} {xs : List V}
    (route : Route R p xs q) (member : r ∈ p :: xs) :
    ∃ front back, xs = front ++ back ∧ Route R p front r ∧ Route R r back q := by
  revert member
  induction route with
  | nil p =>
      intro member
      have same : r = p := by simpa only [List.mem_singleton] using member
      subst r
      exact ⟨[], [], rfl, .nil p, .nil p⟩
  | @cons p «next» q rest step tail ih =>
      intro member
      rcases List.mem_cons.mp member with same | member
      · subst r
        exact ⟨[], «next» :: rest, rfl, .nil p, .cons step tail⟩
      · obtain ⟨front, back, equation, before, after⟩ := ih member
        exact ⟨«next» :: front, back, by simpa only [List.cons_append, equation],
          .cons step before, after⟩

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing

universe u

theorem minimum_directed_positive_outside {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    {b d finish : V} {rest : List V}
    (path : MinimumDirectedPath G Z b (d :: rest) finish) : ¬ Z b := by
  intro conditioned
  have bound := path.minimal b [] (.nil b) conditioned
  simp only [List.length_cons, List.length_nil] at bound
  omega

theorem minimum_directed_distance_eq {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    {b finish : V} {vertices : List V} (path : MinimumDirectedPath G Z b vertices finish) :
    directedDistance G Z b = vertices.length := by
  have ancestor : SourceSelection.AncestorOf G Z b :=
    ⟨finish, ⟨vertices, path.route⟩, path.endpoint⟩
  obtain ⟨⟨last, shortest, route, endpoint, length⟩, bound⟩ := directedDistance_spec G Z b ancestor
  have lower := path.minimal last shortest route endpoint
  have upper := bound vertices.length ⟨finish, vertices, path.route, path.endpoint, rfl⟩
  omega

theorem minimum_directed_first_distance {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    {b d finish : V} {rest : List V}
    (path : MinimumDirectedPath G Z b (d :: rest) finish) :
    directedDistance G Z b = directedDistance G Z d + 1 := by
  rw [minimum_directed_distance_eq G Z path,
    minimum_directed_distance_eq G Z (minimum_directed_tail G Z path)]
  simp only [List.length_cons]

theorem directed_opposites_impossible {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) {b d : V} (forward : Directed G b d)
    (backward : Directed G d b) : False := by
  have «impossible» := laws.acyclic b [d, b] (.cons forward (.cons backward (.nil b)))
  cases «impossible»

/-- The entire actual prefix is excluded, including its starting endpoint.
The one-edge case uses the collider's real incoming head; the longer case
uses the existing global shortest-path chord theorem. -/
theorem outgoing_child_not_in_prefix {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x y d : V)
    {b : Arrival V} {«prefix» suffix : List (Arrival V)} {last : Option Mark}
    (before : Route (RealStep G Z) ⟨x, none⟩ «prefix» b)
    (after : Route (RealStep G Z) b suffix ⟨y, last⟩)
    (shortest : Shortest G Z x y ((«prefix» ++ suffix).map Arrival.vertex))
    (incoming : b.incoming = some .head) (outside : ¬ Z b.vertex)
    (child : Directed G b.vertex d) :
    ∀ q ∈ (⟨x, none⟩ :: «prefix»), q.vertex ≠ d := by
  intro q member equal
  obtain ⟨front, middle, equation, «first», «section»⟩ := before.split_at_mem member
  have reverseChild : G.edge q.vertex b.vertex .head .tail := by
    simpa only [equal] using laws.symmetric b.vertex d .tail .head child
  cases middle with
  | nil =>
      cases «section»
      exact laws.irreflexive b.vertex .tail .head (by simpa only [← equal, CanonicalSelection.Directed] using child)
  | cons «next» rest =>
      cases rest with
      | nil =>
          cases «section» with
          | cons step tail =>
              cases tail
              obtain ⟨«left», received, edge, mark, _⟩ := step
              have receivedHead : received = .head := Option.some.inj (mark.symm.trans incoming)
              have receivedTail := (single q.vertex b.vertex «left» received .head .tail edge reverseChild).2
              exact Mark.noConfusion (receivedHead.symm.trans receivedTail)
      | cons next2 rest =>
          have source : Shortest G Z x y ((front ++ («next» :: next2 :: rest) ++ suffix).map Arrival.vertex) := by
            simpa only [equation, List.append_assoc] using shortest
          rcases shortest_chord_conditioned_parent G laws single Z x y «first» «section» after
              (by simp only [List.length_cons]; omega) reverseChild source with blocked | blocked
          · exact directed_opposites_impossible G laws child (by simpa only [equal] using blocked.2)
          · exact outside blocked.1

/-- The dual exclusion uses the original outgoing collider head. The
source route remains in its original order, so no unproved reversal of a
closestness potential or a MAG walk-erasure theorem is required. -/
theorem outgoing_child_not_in_suffix {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x y d : V)
    {b : Arrival V} {«prefix» suffix : List (Arrival V)} {last : Option Mark}
    (before : Route (RealStep G Z) ⟨x, none⟩ «prefix» b)
    (after : Route (RealStep G Z) b suffix ⟨y, last⟩)
    (shortest : Shortest G Z x y ((«prefix» ++ suffix).map Arrival.vertex))
    (outgoing : match suffix with
      | [] => True
      | q :: _ => ∃ m, G.edge b.vertex q.vertex .head m)
    (outside : ¬ Z b.vertex) (child : Directed G b.vertex d) :
    ∀ q ∈ (b :: suffix), q.vertex ≠ d := by
  intro q member equal
  have outgoing_head : ∀ z zs, suffix = z :: zs → ∃ m, G.edge b.vertex z.vertex .head m := by
    intro z zs h
    subst suffix
    exact outgoing
  obtain ⟨middle, back, equation, «section», final⟩ := after.split_at_mem member
  have chord : G.edge b.vertex q.vertex .tail .head := by simpa only [equal, CanonicalSelection.Directed] using child
  cases middle with
  | nil =>
      cases «section»
      exact laws.irreflexive b.vertex .tail .head chord
  | cons «next» rest =>
      cases rest with
      | nil =>
          cases «section» with
          | cons step tail =>
              cases tail
              obtain ⟨m, edge⟩ := outgoing_head q back (by
                simpa only [List.cons_append, List.nil_append] using equation)
              exact Mark.noConfusion (single b.vertex q.vertex .head m .tail .head edge chord).1
      | cons next2 rest =>
          have source : Shortest G Z x y ((«prefix» ++ («next» :: next2 :: rest) ++ back).map Arrival.vertex) := by
            simpa only [equation, List.append_assoc] using shortest
          rcases shortest_chord_conditioned_parent G laws single Z x y before «section» final
              (by simp only [List.length_cons]; omega) chord source with blocked | blocked
          · exact outside blocked.1
          · exact directed_opposites_impossible G laws child (by simpa only [equal] using blocked.2)

/-- Local boundary incidence for the actual replacement. The old edge
enters a parent q of d; adjacency to d forces a head at d. If the new mark
at a is a head, the old mark at a was also a head, or a directed path a→q→d
would contradict that new arrowhead. If the new mark is a tail, the stopping
boundary's failure to be a collider-parent makes both collider statuses false.
This allows undirected edges elsewhere in the MAG. -/
theorem stopping_boundary_status {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) {p a q d : V}
    {«left» old : Mark} (previous : G.edge p a «left» old)
    (toward : ∃ m, G.edge a q m .head) (parent : Directed G q d)
    (adjacent : Adjacent G a d)
    (stopped : ¬ (Collider G p a q ∧ Directed G a d)) :
    ∃ atBoundary, G.edge a d atBoundary .head ∧
      (Collider G p a q ↔ Collider G p a d) := by
  obtain ⟨oldOut, towardEdge⟩ := toward
  obtain ⟨newOut, received, replacement⟩ := adjacent
  have receivedHead := head_directed_triangle G laws towardEdge parent replacement
  subst received
  refine ⟨newOut, replacement, ?_⟩
  have oldStatus := collider_iff_chosen_marks G single p a q «left» old oldOut .head previous towardEdge
  have newStatus := collider_iff_chosen_marks G single p a d «left» old newOut .head previous replacement
  cases newOut with
  | tail =>
      have oldNoncollider : ¬ Collider G p a q := fun collider => stopped ⟨collider, replacement⟩
      constructor
      · intro collider
        exact (oldNoncollider collider).elim
      · intro collider
        have «impossible» := (newStatus.mp collider).2
        cases «impossible»
  | head =>
      have oldHead : oldOut = .head := by
        cases oldOut with
        | head => rfl
        | tail =>
            exact (laws.head_not_ancestor a d .head replacement
              ⟨[q, d], .cons towardEdge (.cons parent (.nil d))⟩).elim
      rw [oldStatus, newStatus, oldHead]

/-- A genuine nonadjacent stopping boundary forces the first arrow using
the already proved local shared-separator transport. The prefix-collider
premise is precisely the restriction of shortest-path status invariance,
not an assumed common discriminating path. -/
theorem discriminating_flank_forces_first {V : Type u} (G H : MarkedGraph V)
    (lawsH : AncestralLaws H) (singleG : SingleEdges G) (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent G a b ↔ Adjacent H a b)
    (shared : SharedSeparators G H) {a b d : V}
    (w : DiscriminatingWitness G a b d) (firstG : Directed G b d)
    (prefixCollidersH : AllTriples (Collider H)
      (((⟨w.start, none⟩ :: w.parents).map Arrival.vertex) ++ [b]))
    (incomingH : ∃ m, H.edge a b m .head) : Directed H b d := by
  have status := witness_status_transfer G H lawsH singleG singleH skeleton shared w prefixCollidersH
  have noncolliderG : ¬ Collider G a b d := by
    intro collider
    obtain ⟨«left», «right», incoming, outgoing⟩ := collider
    have «impossible» := (singleG b d .head «right» .tail .head outgoing firstG).1
    cases «impossible»
  obtain ⟨m, incoming⟩ := incomingH
  exact head_noncollider_forces_directed H lawsH incoming
    ((skeleton b d).mp ⟨.tail, .head, firstG⟩)
    (fun collider => noncolliderG (status.mpr collider))

theorem unshielded_flank_forces_first {V : Type u} (G H : MarkedGraph V)
    (lawsH : AncestralLaws H) (singleG : SingleEdges G) (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent G a b ↔ Adjacent H a b)
    (shared : SharedSeparators G H) {a b d : V}
    (firstG : Directed G b d) (beforeG : Adjacent G a b)
    (distinct : a ≠ d) (simple : ([a, b, d] : List V).Nodup)
    (nonadjacent : ¬ Adjacent G a d) (incomingH : ∃ m, H.edge a b m .head) :
    Directed H b d := by
  have status := shared_separators_unshielded G H singleG singleH skeleton shared a b d
    distinct beforeG ⟨.tail, .head, firstG⟩ nonadjacent simple
  have noncolliderG : ¬ Collider G a b d := by
    intro collider
    obtain ⟨«left», «right», incoming, outgoing⟩ := collider
    have «impossible» := (singleG b d .head «right» .tail .head outgoing firstG).1
    cases «impossible»
  obtain ⟨m, incoming⟩ := incomingH
  exact head_noncollider_forces_directed H lawsH incoming
    ((skeleton b d).mp ⟨.tail, .head, firstG⟩)
    (fun collider => noncolliderG (status.mpr collider))

end RestrictedCausal.VertexActivePaths
