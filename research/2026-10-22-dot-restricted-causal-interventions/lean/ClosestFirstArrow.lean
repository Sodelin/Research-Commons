import ClosestFirstArrowArms

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Compose the actual two oriented collider contexts, stopping scans, shared-
separator flank transport, and closer-path contradiction. This proves the
first arrow for an arbitrary collider on a closest path in the ORIGINAL
source's literal selected MAG. Neither a common discriminating-path axiom
nor an assumed first-arrow oracle occurs in the statement.
Classical attribution: Ali--Richardson--Spirtes (2009), Lemma 3.25 and
Corollary 3.27. This is not a novelty or Lean-verification claim.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing OriginalProjection
open IndexedDiscriminatingSections
open SourceSelection (AncestorOf)

universe u v w

theorem closest_collider_first_arrow {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (H : MarkedGraph X) (lawsH : AncestralLaws H)
    (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent (mag D) a b ↔ Adjacent H a b)
    (shared : SharedSeparators (mag D) H)
    (Z : X → Prop) (x y d : X)
    {b c : Arrival X} {«prefix» suffix : List (Arrival X)} {last : Option Mark}
    {directedTail : List X} {finish : X}
    (before : Route (RealStep (mag D) Z) ⟨x, none⟩ «prefix» b)
    (bc : RealStep (mag D) Z b c)
    (following : Route (RealStep (mag D) Z) c suffix ⟨y, last⟩)
    (closest : Closest (mag D) Z x y ((«prefix» ++ (c :: suffix)).map Arrival.vertex))
    (notStart : ¬ Z x) (notEnd : ¬ Z y)
    (headB : b.incoming = some .head) (atB : ColliderStep (mag D) b c)
    (directed : MinimumDirectedPath (mag D) Z b.vertex (d :: directedTail) finish) :
    Directed H b.vertex d := by
  classical
  let G := mag D
  have lawsG := (literal_mag_valid D).1
  have singleG := mag_single_edges D
  have child : Directed G b.vertex d := by cases directed.route with | cons «first» tail => exact «first»
  have outside := minimum_directed_positive_outside G Z directed
  have distance := minimum_directed_first_distance G Z directed
  have activated : AncestorOf G Z d :=
    ⟨finish, ⟨directedTail, (minimum_directed_tail G Z directed).route⟩, directed.endpoint⟩
  have forwardInvariant := shortest_path_status_invariant D H lawsH singleH skeleton shared
    Z x y closest.1 notStart notEnd
  obtain ⟨rightPrefix, reverseNext, reverseSuffix, reverseLast, rightRoute, reverseStep,
      reverseFollowing, reverseCollider, reverseShortest, _, rightTrace⟩ :=
    reverse_collider_context G lawsG singleG Z x y before bc following closest.1 headB atB
  have reverseInvariant := shortest_path_status_invariant D H lawsH singleH skeleton shared
    Z y x reverseShortest notEnd notStart
  obtain ⟨a, leftNext, leftFront, leftRest, leftSplit, leftArm, leftBoundary,
      leftStopped, leftAfter⟩ := extract_first_arrow_boundary G Z x d before headB
  obtain ⟨r, rightNext, rightFront, rightRest, rightSplit, rightArm, rightBoundary,
      rightStopped, rightAfter⟩ := extract_first_arrow_boundary G Z y d rightRoute headB
  by_cases leftAdjacent : Adjacent G a.vertex d
  · by_cases rightAdjacent : Adjacent G r.vertex d
    · obtain ⟨leftOut, leftEdge, leftReady⟩ := stopped_boundary_replacement G lawsG singleG Z d
        leftBoundary leftStopped leftAfter headB child leftAdjacent
      obtain ⟨rightOut, rightEdge, rightReady⟩ := stopped_boundary_replacement G lawsG singleG Z d
        rightBoundary rightStopped rightAfter headB child rightAdjacent
      obtain ⟨leftInside, leftEnds⟩ := leftAfter.full_list_ends
      obtain ⟨rightInside, rightEnds⟩ := rightAfter.full_list_ends
      let keptRight : List X := ((⟨y, none⟩ :: rightFront).map Arrival.vertex).reverse
      have rightSuffixTrace : (c :: suffix).map Arrival.vertex =
          (rightInside.map Arrival.vertex).reverse ++ keptRight := by
        have reversed := congrArg List.reverse rightTrace
        have consEquation : b.vertex :: ((rightInside.map Arrival.vertex).reverse ++ keptRight) =
            b.vertex :: (c :: suffix).map Arrival.vertex := by
          simpa only [rightSplit, rightEnds, keptRight, List.map_cons, List.map_append, List.map_nil,
            List.cons_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.singleton_append, List.append_assoc, List.reverse_reverse] using reversed
        exact (List.cons.inj consEquation).2.symm
      have originalTrace : x :: («prefix» ++ (c :: suffix)).map Arrival.vertex =
          ((⟨x, none⟩ :: leftFront).map Arrival.vertex) ++ leftInside.map Arrival.vertex ++
          [b.vertex] ++ (rightInside.map Arrival.vertex).reverse ++ keptRight := by
        simp only [List.map_append]
        rw [rightSuffixTrace, leftSplit, leftEnds]
        simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.append_assoc]
      have leftStop : leftInside.map Arrival.vertex = [] →
          RealStep G Z a b ∧ ¬ StrictParentStep G d a b := by
        intro empty
        have insideEmpty : leftInside = [] := by
          cases leftInside with
          | nil => rfl
          | cons p ps => cases empty
        have ends : leftNext :: leftRest = [b] := by simpa only [insideEmpty, List.nil_append] using leftEnds
        obtain ⟨same, restEmpty⟩ := List.cons.inj ends
        subst leftNext
        exact ⟨leftBoundary, leftStopped⟩
      have rightStop : (rightInside.map Arrival.vertex).reverse = [] →
          RealStep G Z r b ∧ ¬ StrictParentStep G d r b := by
        intro empty
        have length := congrArg List.length empty
        simp only [List.length_reverse, List.length_map, List.length_nil] at length
        have insideEmpty : rightInside = [] := by
          cases rightInside with
          | nil => rfl
          | cons p ps => simp only [List.length_cons] at length; omega
        have ends : rightNext :: rightRest = [b] := by simpa only [insideEmpty, List.nil_append] using rightEnds
        obtain ⟨same, restEmpty⟩ := List.cons.inj ends
        subst rightNext
        exact ⟨rightBoundary, rightStopped⟩
      have after : Route (RealStep G Z) b (c :: suffix) ⟨y, last⟩ := .cons bc following
      have sourceHead : ∃ m, G.edge b.vertex c.vertex .head m := by
        obtain ⟨outgoing, received, edge, mark, details⟩ := atB
        have heads : Mark.head = .head ∧ outgoing = .head := by simpa only [headB] using details
        exact ⟨received, heads.2 ▸ edge⟩
      have offLeft := outgoing_child_not_in_prefix G lawsG singleG Z x y d before after
        closest.1 headB outside child
      have offRight := outgoing_child_not_in_suffix G lawsG singleG Z x y d before after
        closest.1 sourceHead outside child
      have fresh : d ∉ x :: («prefix» ++ (c :: suffix)).map Arrival.vertex := by
        intro member
        have mapped : d ∈ ((⟨x, none⟩ :: («prefix» ++ (c :: suffix))).map Arrival.vertex) := member
        obtain ⟨q, member, same⟩ := List.mem_map.mp mapped
        have splitMember : q ∈ (⟨x, none⟩ :: «prefix») ++ (c :: suffix) := by
          simpa only [List.cons_append] using member
        rcases List.mem_append.mp splitMember with member | member
        · exact offLeft q member same
        · exact offRight q (List.mem_cons_of_mem _ member) same
      exact (adjacent_boundaries_contradict_closest G lawsG singleG Z x y d
        (leftInside.map Arrival.vertex) ((rightInside.map Arrival.vertex).reverse)
        closest leftArm rightArm originalTrace leftStop rightStop headB child
        leftEdge rightEdge leftReady rightReady activated fresh distance).elim
    · exact nonadjacent_boundary_forces_first G H lawsG lawsH singleG singleH skeleton shared
        Z y x d rightRoute reverseStep reverseFollowing reverseShortest reverseInvariant headB reverseCollider
        outside child rightSplit rightArm rightBoundary rightAfter rightAdjacent
  · exact nonadjacent_boundary_forces_first G H lawsG lawsH singleG singleH skeleton shared
      Z x y d before bc following closest.1 forwardInvariant headB atB outside child
      leftSplit leftArm leftBoundary leftAfter leftAdjacent

end RestrictedCausal.VertexActivePaths
