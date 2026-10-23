import ClosestFirstArrowIncidence

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The complete two-adjacent-boundaries contradiction for actual retained
arms of a closest active path. Build the competing path first. Shortestness
forces BOTH deleted side interiors to be empty. The actual stopping
incidences then supply neighboring status invariance, and the proved exact
one-unit potential decrease contradicts closestness. The arm extraction
and reversal assembly for an arbitrary original collider remain a separate
final composition step, not an assumption hidden in this theorem.
Classical attribution: Ali--Richardson--Spirtes (2009), Lemma 3.25.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing
open IndexedDiscriminatingSections (collider_swap_iff)
open SourceSelection (AncestorOf)

universe u

theorem adjacent_boundaries_contradict_closest {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x y d : V)
    {a r b : Arrival V} {«left» «right» : List (Arrival V)}
    (leftInside rightInside : List V) {old : List V} {leftOut rightOut : Mark}
    (closest : Closest G Z x y old)
    (leftArm : Route (RealStep G Z) ⟨x, none⟩ «left» a)
    (rightArm : Route (RealStep G Z) ⟨y, none⟩ «right» r)
    (oldTrace : x :: old = ((⟨x, none⟩ :: «left»).map Arrival.vertex) ++ leftInside ++
      [b.vertex] ++ rightInside ++ ((⟨y, none⟩ :: «right»).map Arrival.vertex).reverse)
    (leftStop : leftInside = [] → RealStep G Z a b ∧ ¬ StrictParentStep G d a b)
    (rightStop : rightInside = [] → RealStep G Z r b ∧ ¬ StrictParentStep G d r b)
    (headB : b.incoming = some .head) (child : Directed G b.vertex d)
    (leftEdge : G.edge a.vertex d leftOut .head)
    (rightEdge : G.edge r.vertex d rightOut .head)
    (leftReady : DepartureAllowed Z (AncestorOf G Z) a.vertex a.incoming leftOut)
    (rightReady : DepartureAllowed Z (AncestorOf G Z) r.vertex r.incoming rightOut)
    (activated : AncestorOf G Z d) (fresh : d ∉ x :: old)
    (distance : directedDistance G Z b.vertex = directedDistance G Z d + 1) : False := by
  let keptLeft : List V := (⟨x, none⟩ :: «left»).map Arrival.vertex
  let keptRight : List V := ((⟨y, none⟩ :: «right»).map Arrival.vertex).reverse
  have retainedSub : keptLeft ++ keptRight <+ x :: old := by
    rw [oldTrace]
    have sub := ((List.sublist_append_right (leftInside ++ [b.vertex] ++ rightInside) keptRight)
      .append_left keptLeft)
    simpa only [keptLeft, keptRight, List.append_assoc] using sub
  have retainedSimple := closest.1.1.2.1.sublist retainedSub
  have retainedFresh : d ∉ keptLeft ++ keptRight := fun member => fresh (retainedSub.subset member)
  obtain ⟨new, candidate, newTrace, newLength⟩ := two_boundary_splice G laws single Z x y d
    leftArm rightArm leftEdge rightEdge leftReady rightReady activated retainedSimple retainedFresh
  have oldLength := congrArg List.length oldTrace
  simp only [List.length_cons, List.length_map, List.length_append, List.length_reverse,
    List.length_nil] at oldLength
  have shortestBound := closest.1.2 new candidate
  have leftZero : leftInside.length = 0 := by omega
  have rightZero : rightInside.length = 0 := by omega
  have leftEmpty : leftInside = [] := by
    cases leftInside with
    | nil => rfl
    | cons p ps => simp only [List.length_cons] at leftZero; omega
  have rightEmpty : rightInside = [] := by
    cases rightInside with
    | nil => rfl
    | cons p ps => simp only [List.length_cons] at rightZero; omega
  obtain ⟨leftBoundary, leftStopped⟩ := leftStop leftEmpty
  obtain ⟨rightBoundary, rightStopped⟩ := rightStop rightEmpty
  have leftStable := retained_left_status G laws single Z x d leftArm leftBoundary leftStopped
    headB child ⟨leftOut, .head, leftEdge⟩
  have rightStable : ∀ c q rest, keptRight = c :: q :: rest →
      (Collider G b.vertex c q ↔ Collider G d c q) := by
    intro c q rest equation
    have reversed := congrArg List.reverse equation
    have armTrace : (⟨y, none⟩ :: «right»).map Arrival.vertex = rest.reverse ++ [q, c] := by
      simpa only [keptRight, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
        List.append_assoc, List.cons_append, List.nil_append] using reversed
    have status := retained_left_status G laws single Z y d rightArm rightBoundary rightStopped
      headB child ⟨rightOut, .head, rightEdge⟩ rest.reverse q c armTrace
    exact (collider_swap_iff G laws.symmetric b.vertex c q).trans
      (status.trans (collider_swap_iff G laws.symmetric q c d))
  have central : ∀ front p q rest, keptLeft = front ++ [p] → keptRight = q :: rest →
      Collider G p b.vertex q ∧ Collider G p d q := by
    intro front p q rest leftEquation rightEquation
    have leftLabel : a.vertex = p := retained_arm_terminal x leftArm leftEquation
    obtain ⟨rightBefore, rightEnds⟩ := rightArm.full_list_ends
    have reversed := congrArg (fun states => (states.map Arrival.vertex).reverse) rightEnds
    have rightStarts : keptRight = r.vertex :: (rightBefore.map Arrival.vertex).reverse := by
      simpa only [keptRight, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] using reversed
    have rightLabel : r.vertex = q := (List.cons.inj (rightStarts.symm.trans rightEquation)).1
    obtain ⟨oldLeft, leftReceived, firstOld, leftMark, _⟩ := leftBoundary
    obtain ⟨oldRight, rightReceived, lastOld, rightMark, _⟩ := rightBoundary
    have leftHead : leftReceived = .head := Option.some.inj (leftMark.symm.trans headB)
    have rightHead : rightReceived = .head := Option.some.inj (rightMark.symm.trans headB)
    refine ⟨⟨oldLeft, oldRight, ?_, ?_⟩, ⟨leftOut, rightOut, ?_, ?_⟩⟩
    · simpa only [leftLabel, leftHead] using firstOld
    · simpa only [rightLabel, rightHead] using laws.symmetric _ _ _ _ lastOld
    · simpa only [leftLabel] using leftEdge
    · simpa only [rightLabel] using laws.symmetric _ _ _ _ rightEdge
  apply closest_rejects_equal_length_replacement G Z x y b.vertex d keptLeft keptRight
    closest candidate
  · simpa only [keptLeft, keptRight, leftEmpty, rightEmpty, List.append_nil,
      List.nil_append, List.append_assoc, List.singleton_append] using oldTrace
  · simpa only [keptLeft, keptRight, List.append_assoc, List.singleton_append] using newTrace
  · exact distance
  · exact leftStable
  · exact rightStable
  · exact central
  · intro empty
    have «impossible» := congrArg List.length empty
    simp only [keptLeft, List.length_map, List.length_cons, List.length_nil] at «impossible»
    omega
  · intro empty
    have «impossible» := congrArg List.length empty
    simp only [keptRight, List.length_reverse, List.length_map, List.length_cons, List.length_nil] at «impossible»
    omega

end RestrictedCausal.VertexActivePaths
