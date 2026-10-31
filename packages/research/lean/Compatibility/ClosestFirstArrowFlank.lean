import ClosestFirstArrowBoundary

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Turn the actual stopping segment into a genuine unshielded or discriminating
flank, and force the first arrow when that boundary is nonadjacent. Every
prefix collider in the other graph is obtained from the SAME original
path's proved status equivalences. No common-prefix or common-parent oracle
is introduced. Classical attribution: Ali--Richardson--Spirtes (2009),
Lemma 3.25 and Corollary 3.27.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem split_last {V : Type u} {R : V → V → Prop} {p q : V} {xs : List V}
    (route : Route R p xs q) (nonempty : xs ≠ []) :
    ∃ before front, xs = front ++ [q] ∧ Route R p front before ∧ R before q := by
  revert nonempty
  induction route with
  | nil => intro «impossible»; exact («impossible» rfl).elim
  | @cons p «next» q rest step tail ih =>
      intro _
      cases rest with
      | nil => cases tail; exact ⟨p, [], rfl, .nil p, step⟩
      | cons r rs =>
          obtain ⟨before, front, equation, «first», last⟩ := ih (by intro «impossible»; cases «impossible»)
          exact ⟨before, «next» :: front, by simpa only [List.cons_append, equation],
            .cons step «first», last⟩

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing

universe u

theorem all_triples_tail {V : Type u} (P : V → V → V → Prop) (a : V) (xs : List V)
    (h : AllTriples P (a :: xs)) : AllTriples P xs := by
  cases xs with
  | nil => trivial
  | cons b xs =>
      cases xs with
      | nil => trivial
      | cons c xs => exact h.2

theorem all_triples_drop_prefix {V : Type u} (P : V → V → V → Prop) (front xs : List V)
    (h : AllTriples P (front ++ xs)) : AllTriples P xs := by
  induction front with
  | nil => exact h
  | cons a front ih => exact ih (all_triples_tail P a (front ++ xs) h)

theorem all_triples_take_prefix {V : Type u} (P : V → V → V → Prop) (xs back : List V)
    (h : AllTriples P (xs ++ back)) : AllTriples P xs := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
      cases xs with
      | nil => trivial
      | cons b xs =>
          cases xs with
          | nil => trivial
          | cons c xs => exact ⟨h.1, ih h.2⟩

theorem all_triples_subsegment {V : Type u} (P : V → V → V → Prop)
    (front middle back : List V) (h : AllTriples P (front ++ middle ++ back)) :
    AllTriples P middle :=
  all_triples_take_prefix P middle back
    (all_triples_drop_prefix P front (middle ++ back) (by simpa only [List.append_assoc] using h))

theorem all_triples_transport {V : Type u} (P Q : V → V → V → Prop) (xs : List V)
    (equivalent : AllTriples (fun a b c => P a b c ↔ Q a b c) xs)
    (source : AllTriples P xs) : AllTriples Q xs := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
      cases xs with
      | nil => trivial
      | cons b xs =>
          cases xs with
          | nil => trivial
          | cons c xs => exact ⟨equivalent.1.mp source.1, ih equivalent.2 source.2⟩

theorem nodup_append_fresh {V : Type u} (xs : List V) (d : V)
    (simple : xs.Nodup) (fresh : d ∉ xs) : (xs ++ [d]).Nodup := by
  induction xs with
  | nil => exact List.nodup_singleton d
  | cons a xs ih =>
      obtain ⟨outside, tail⟩ := List.nodup_cons.mp simple
      refine List.Nodup.cons ?_ (ih tail (fun member => fresh (List.mem_cons_of_mem _ member)))
      intro member
      rcases List.mem_append.mp member with member | equal
      · exact outside member
      · have same : a = d := by simpa only [List.mem_singleton] using equal
        apply fresh
        exact List.mem_cons.mpr (Or.inl same.symm)

theorem collider_route_triples {V : Type u} (G : MarkedGraph V)
    {p q : Arrival V} {xs : List (Arrival V)} (route : Route (ColliderStep G) p xs q) :
    AllTriples (Collider G) ((p :: xs).map Arrival.vertex) := by
  induction route with
  | nil => trivial
  | @cons p «next» q rest «first» tail ih =>
      cases rest with
      | nil => trivial
      | cons following rest =>
          cases tail with
          | cons second remainder =>
              obtain ⟨«left», incoming, firstEdge, mark, _⟩ := «first»
              obtain ⟨outgoing, «right», lastEdge, _, details⟩ := second
              have heads : incoming = .head ∧ outgoing = .head := by
                simpa only [mark] using details
              exact ⟨⟨«left», «right», heads.1 ▸ firstEdge, heads.2 ▸ lastEdge⟩, ih⟩

/-- Reset only the boundary's arrival: it is an endpoint of the new flank.
All genuine interior collider-parent incidences remain unchanged. -/
theorem boundary_parent_route {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (d : V)
    {a «next» b : Arrival V} {rest : List (Arrival V)} (step : RealStep G Z a «next»)
    (after : Route (fun p q => RealStep G Z p q ∧ StrictParentStep G d p q) «next» rest b) :
    Route (ColliderParentStep G d) ⟨a.vertex, none⟩ («next» :: rest) b := by
  obtain ⟨outgoing, incoming, edge, mark, _⟩ := step
  exact .cons ⟨outgoing, incoming, edge, mark, trivial⟩ (strict_parent_route_forget G Z d after)

/-- This is the nonadjacent-boundary half of the actual first-arrow proof.
The local segment is derived from a literal original-route decomposition.
The child d is proved absent from that prefix by shortest-path geometry;
the target prefix colliders are obtained by restricting whole-path status
invariance. Positive and zero parent-interior cases are both explicit. -/
theorem nonadjacent_boundary_forces_first {V : Type u} (G H : MarkedGraph V)
    (lawsG : AncestralLaws G) (lawsH : AncestralLaws H)
    (singleG : SingleEdges G) (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent G a b ↔ Adjacent H a b) (shared : SharedSeparators G H)
    (Z : V → Prop) (x y d : V)
    {a «next» b c : Arrival V} {«prefix» front rest suffix : List (Arrival V)} {last : Option Mark}
    (originalBefore : Route (RealStep G Z) ⟨x, none⟩ «prefix» b)
    (bc : RealStep G Z b c) (following : Route (RealStep G Z) c suffix ⟨y, last⟩)
    (shortest : Shortest G Z x y ((«prefix» ++ (c :: suffix)).map Arrival.vertex))
    (invariant : AllTriples (fun p q r => Collider G p q r ↔ Collider H p q r)
      ((⟨x, none⟩ :: («prefix» ++ (c :: suffix))).map Arrival.vertex))
    (incoming : b.incoming = some .head) (atB : ColliderStep G b c)
    (outside : ¬ Z b.vertex) (child : Directed G b.vertex d)
    (equation : «prefix» = front ++ («next» :: rest))
    (before : Route (RealStep G Z) ⟨x, none⟩ front a)
    (boundary : RealStep G Z a «next»)
    (after : Route (fun p q => RealStep G Z p q ∧ StrictParentStep G d p q) «next» rest b)
    (nonadjacent : ¬ Adjacent G a.vertex d) : Directed H b.vertex d := by
  let flankVertices : List V := (a :: «next» :: rest).map Arrival.vertex
  obtain ⟨dropped, endEquation⟩ := before.full_list_ends
  have prefixEquation : (⟨x, none⟩ :: «prefix») = dropped ++ (a :: «next» :: rest) := by
    rw [equation]
    calc
      (⟨x, none⟩ :: (front ++ («next» :: rest))) =
          (⟨x, none⟩ :: front) ++ («next» :: rest) := by simp only [List.cons_append]
      _ = (dropped ++ [a]) ++ («next» :: rest) := by rw [endEquation]
      _ = dropped ++ (a :: «next» :: rest) := by simp only [List.append_assoc, List.singleton_append]
  have fullEquation : ((⟨x, none⟩ :: («prefix» ++ (c :: suffix))).map Arrival.vertex) =
      dropped.map Arrival.vertex ++ (flankVertices ++ [c.vertex]) ++ suffix.map Arrival.vertex := by
    have e := congrArg (fun states => (states ++ (c :: suffix)).map Arrival.vertex) prefixEquation
    simpa only [flankVertices, List.map_append, List.map_cons, List.map_nil, List.cons_append,
      List.append_assoc, List.singleton_append, List.nil_append] using e
  have localSimple : flankVertices.Nodup := by
    have fullSimple := shortest.1.2.1
    change ((⟨x, none⟩ :: («prefix» ++ (c :: suffix))).map Arrival.vertex).Nodup at fullSimple
    rw [fullEquation] at fullSimple
    apply List.Nodup.sublist _ fullSimple
    have prefixSub := (List.nil_sublist (dropped.map Arrival.vertex)).append (List.Sublist.refl flankVertices)
    have extended := (prefixSub.append (List.nil_sublist [c.vertex])).append
      (List.nil_sublist (suffix.map Arrival.vertex))
    simpa only [List.nil_append, List.append_nil, List.append_assoc] using extended
  have fresh : d ∉ flankVertices := by
    intro member
    have mappedMember : d ∈ (⟨x, none⟩ :: «prefix»).map Arrival.vertex := by
      rw [prefixEquation, List.map_append]
      exact List.mem_append.mpr (Or.inr member)
    obtain ⟨q, member, same⟩ := List.mem_map.mp mappedMember
    exact outgoing_child_not_in_prefix G lawsG singleG Z x y d originalBefore
      (.cons bc following) shortest incoming outside child q member same
  have extendedSimple := nodup_append_fresh flankVertices d localSimple fresh
  have parentRoute := boundary_parent_route G Z d boundary after
  have sourceColliders := collider_route_triples G
    ((parent_route_forget G d parentRoute).append (.cons atB (.nil c)))
  have localInvariant := all_triples_subsegment
    (fun p q r => Collider G p q r ↔ Collider H p q r)
    (dropped.map Arrival.vertex) (flankVertices ++ [c.vertex]) (suffix.map Arrival.vertex)
    (by rw [← fullEquation]; exact invariant)
  have targetColliders : AllTriples (Collider H) (flankVertices ++ [c.vertex]) :=
    all_triples_transport (Collider G) (Collider H) _ localInvariant (by
      simpa only [flankVertices, List.map_cons, List.map_append, List.map_nil, List.cons_append,
        List.append_assoc] using sourceColliders)
  cases rest with
  | nil =>
      cases after
      have targetAtB : Collider H a.vertex «next».vertex c.vertex := targetColliders.1
      obtain ⟨«left», «right», firstH, _⟩ := targetAtB
      obtain ⟨oldLeft, oldRight, firstG, _, _⟩ := boundary
      have distinct : a.vertex ≠ d := by
        intro equal
        apply fresh
        exact List.mem_cons.mpr (Or.inl equal.symm)
      exact unshielded_flank_forces_first G H lawsH singleG singleH skeleton shared child
        ⟨oldLeft, oldRight, firstG⟩ distinct extendedSimple nonadjacent ⟨«left», firstH⟩
  | cons «first» rest =>
      obtain ⟨penultimate, parents, «split», parentTail, finalStep⟩ :=
        after.split_last (by intro «impossible»; cases «impossible»)
      obtain ⟨oldLeft, oldRight, oldEdge, oldMark, _⟩ := boundary
      have parentsRoute : Route (ColliderParentStep G d) ⟨a.vertex, none⟩
          («next» :: parents) penultimate :=
        .cons ⟨oldLeft, oldRight, oldEdge, oldMark, trivial⟩
          (strict_parent_route_forget G Z d parentTail)
      let w : DiscriminatingWitness G penultimate.vertex b.vertex d := {
        start := a.vertex, before := penultimate, terminal := b, parents := «next» :: parents,
        before_vertex := rfl, terminal_vertex := rfl,
        parent_prefix := parentsRoute, last_parent_step := finalStep.2.1,
        terminal_adjacent := ⟨.tail, .head, child⟩,
        nonempty := by simp,
        simple := by simpa only [flankVertices, «split», List.cons_append, List.map_cons,
          List.map_append, List.map_nil, List.append_assoc] using extendedSimple,
        nonadjacent := nonadjacent }
      have prefixH : AllTriples (Collider H)
          (((⟨w.start, none⟩ :: w.parents).map Arrival.vertex) ++ [b.vertex]) := by
        have «prefix» := all_triples_take_prefix (Collider H) flankVertices [c.vertex] targetColliders
        simpa only [w, flankVertices, «split», List.map_cons, List.map_append, List.map_nil,
          List.cons_append, List.append_assoc] using «prefix»
      obtain ⟨earlier, ends⟩ := parentsRoute.full_list_ends
      have localEnds : flankVertices = earlier.map Arrival.vertex ++ [penultimate.vertex, b.vertex] := by
        have endsMap := congrArg (List.map Arrival.vertex) ends
        simp only [List.map_append, List.map_cons, List.map_nil] at endsMap
        simp only [flankVertices, «split», List.map_cons, List.map_append, List.map_nil,
          List.cons_append, List.append_assoc]
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using
          congrArg (fun nodes => nodes ++ [b.vertex]) endsMap
      have lastTriple : AllTriples (Collider H) [penultimate.vertex, b.vertex, c.vertex] := by
        apply all_triples_subsegment (Collider H) (earlier.map Arrival.vertex)
          [penultimate.vertex, b.vertex, c.vertex] []
        simpa only [localEnds, List.append_assoc, List.cons_append, List.nil_append,
          List.append_nil] using targetColliders
      obtain ⟨«left», «right», firstH, _⟩ := lastTriple.1
      exact discriminating_flank_forces_first G H lawsH singleG singleH skeleton shared
        w child prefixH ⟨«left», firstH⟩

end RestrictedCausal.VertexActivePaths
