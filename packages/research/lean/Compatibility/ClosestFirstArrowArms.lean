import ClosestFirstArrowContradiction

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Construct the opposite orientation of an actual shortest active path at
the SAME collider state b. Both head incidences are explicit. Reversal is
performed on the real arms with their required arrival marks, and retains
both the complete reversed trace and the right-arm trace needed to splice
the two independently extracted stopping boundaries back into ONE path.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing
open SourceSelection (AncestorOf)

universe u

theorem reverse_collider_context {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x y : V)
    {b c : Arrival V} {«prefix» suffix : List (Arrival V)} {last : Option Mark}
    (before : Route (RealStep G Z) ⟨x, none⟩ «prefix» b)
    (bc : RealStep G Z b c) (following : Route (RealStep G Z) c suffix ⟨y, last⟩)
    (shortest : Shortest G Z x y ((«prefix» ++ (c :: suffix)).map Arrival.vertex))
    (headB : b.incoming = some .head) (atB : ColliderStep G b c) :
    ∃ «right» «next» back terminal,
      Route (RealStep G Z) ⟨y, none⟩ «right» b ∧ RealStep G Z b «next» ∧
      Route (RealStep G Z) «next» back ⟨x, terminal⟩ ∧ ColliderStep G b «next» ∧
      Shortest G Z y x ((«right» ++ («next» :: back)).map Arrival.vertex) ∧
      ((⟨y, none⟩ :: («right» ++ («next» :: back))).map Arrival.vertex) =
        ((⟨x, none⟩ :: («prefix» ++ (c :: suffix))).map Arrival.vertex).reverse ∧
      ((⟨y, none⟩ :: «right»).map Arrival.vertex) =
        ((b :: c :: suffix).map Arrival.vertex).reverse := by
  obtain ⟨outgoing, received, edge, markC, activeB⟩ := bc
  obtain ⟨colliderOut, colliderIn, colliderEdge, colliderMark, colliderDetails⟩ := atB
  have colliderHeads : Mark.head = .head ∧ colliderOut = .head := by
    simpa only [headB] using colliderDetails
  have outgoingHead : outgoing = .head :=
    (single b.vertex c.vertex outgoing received colliderOut colliderIn edge colliderEdge).1.trans colliderHeads.2
  subst outgoing
  have activatedB : AncestorOf G Z b.vertex := by
    simpa only [headB, ActiveAt, and_self, if_true] using activeB
  obtain ⟨rightArrival, rightTail, reverseFollowing, compatibleC, followingTrace⟩ :=
    reverse_required_arrival_trace G laws.symmetric Z (AncestorOf G Z) following none trivial
  have backToB : RealStep G Z ⟨c.vertex, rightArrival⟩ b :=
    ⟨received, .head, laws.symmetric _ _ _ _ edge, headB, by cases rightArrival <;> simpa only [markC, DepartureAllowed] using compatibleC⟩
  let «right» := rightTail ++ [b]
  have rightRoute : Route (RealStep G Z) ⟨y, none⟩ «right» b :=
    reverseFollowing.append (.cons backToB (.nil b))
  have rightTrace : ((⟨y, none⟩ :: «right»).map Arrival.vertex) =
      ((b :: c :: suffix).map Arrival.vertex).reverse := by
    calc
      ((⟨y, none⟩ :: «right»).map Arrival.vertex) =
          (y :: rightTail.map Arrival.vertex) ++ [b.vertex] := by
            simp only [«right», List.map_cons, List.map_append, List.map_nil, List.cons_append]
      _ = ((c :: suffix).map Arrival.vertex).reverse ++ [b.vertex] := by rw [followingTrace]
      _ = ((b :: c :: suffix).map Arrival.vertex).reverse := by
            simp only [List.map_cons, List.reverse_cons]
  have prefixNonempty : «prefix» ≠ [] := by
    intro empty
    subst «prefix»
    cases before
    cases headB
  obtain ⟨previous, earlier, prefixSplit, earlierRoute, previousStep⟩ := before.split_last prefixNonempty
  obtain ⟨previousOut, previousIn, previousEdge, previousMark, previousReady⟩ := previousStep
  have previousInHead : previousIn = .head := Option.some.inj (previousMark.symm.trans headB)
  subst previousIn
  obtain ⟨terminal, back, reverseEarlier, _, earlierTrace⟩ :=
    reverse_required_arrival_trace G laws.symmetric Z (AncestorOf G Z) earlierRoute
      (some previousOut) previousReady
  let «next» : Arrival V := ⟨previous.vertex, some previousOut⟩
  have reverseStep : RealStep G Z b «next» :=
    ⟨.head, previousOut, laws.symmetric _ _ _ _ previousEdge, rfl, by
      simpa only [headB, ActiveAt, and_self, if_true] using activatedB⟩
  have reverseCollider : ColliderStep G b «next» :=
    ⟨.head, previousOut, laws.symmetric _ _ _ _ previousEdge, rfl, by
      simpa only [headB] using (show Mark.head = .head ∧ Mark.head = .head from ⟨rfl, rfl⟩)⟩
  have leftTrace : b.vertex :: («next» :: back).map Arrival.vertex =
      ((⟨x, none⟩ :: «prefix»).map Arrival.vertex).reverse := by
    calc
      b.vertex :: («next» :: back).map Arrival.vertex =
          b.vertex :: (previous.vertex :: back.map Arrival.vertex) := rfl
      _ = b.vertex :: ((⟨x, none⟩ :: earlier).map Arrival.vertex).reverse := by rw [earlierTrace]
      _ = ((⟨x, none⟩ :: «prefix»).map Arrival.vertex).reverse := by
        simp only [prefixSplit, List.map_cons, List.map_append, List.map_nil, List.cons_append,
          List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  have fullTrace : ((⟨y, none⟩ :: («right» ++ («next» :: back))).map Arrival.vertex) =
      ((⟨x, none⟩ :: («prefix» ++ (c :: suffix))).map Arrival.vertex).reverse := by
    calc
      ((⟨y, none⟩ :: («right» ++ («next» :: back))).map Arrival.vertex) =
          ((⟨y, none⟩ :: «right»).map Arrival.vertex) ++ («next» :: back).map Arrival.vertex := by
            simp only [List.map_cons, List.map_append, List.cons_append]
      _ = ((c :: suffix).map Arrival.vertex).reverse ++
          (b.vertex :: («next» :: back).map Arrival.vertex) := by
            rw [rightTrace]
            simp [List.map_cons, List.reverse_cons, List.append_assoc]
      _ = ((c :: suffix).map Arrival.vertex).reverse ++
          ((⟨x, none⟩ :: «prefix»).map Arrival.vertex).reverse := by rw [leftTrace]
      _ = ((⟨x, none⟩ :: («prefix» ++ (c :: suffix))).map Arrival.vertex).reverse := by
        simp [List.map_cons, List.map_append, List.cons_append, List.reverse_append]
  obtain ⟨reversed, reversedShortest, reversedTrace, _⟩ :=
    reverse_shortest_path G single laws.symmetric Z x y shortest
  have sameTail : («right» ++ («next» :: back)).map Arrival.vertex = reversed := by
    exact (List.cons.inj (by simpa only [List.map_cons] using fullTrace.trans reversedTrace.symm)).2
  refine ⟨«right», «next», back, terminal, rightRoute, reverseStep, reverseEarlier,
    reverseCollider, ?_, fullTrace, rightTrace⟩
  rw [sameTail]
  exact reversedShortest

end RestrictedCausal.VertexActivePaths
