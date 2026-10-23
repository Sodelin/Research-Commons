import ColliderMinimumReversal

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

First-hit extraction from the literal original active path. This file
assembles forward splicing and exact reversal to exclude every later
main-path vertex from a shortest activation branch of a collider-count /
distance-minimal path. It is the geometric Lemma A of the binary witness,
not branch/branch exclusion, a probability law or faithfulness itself.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u v

theorem split_at_mapped_vertex {A : Type u} {B : Type v} {R : A → A → Prop}
    (f : A → B) {p q : A} {xs : List A} (route : Route R p xs q)
    (left right : List B) (b : B) (trace : f p :: xs.map f = left ++ b :: right) :
    ∃ at before after, f at = b ∧ xs = before ++ after ∧
      Route R p before at ∧ Route R at after q ∧
      f p :: before.map f = left ++ [b] ∧ after.map f = right := by
  revert p xs route trace
  induction left with
  | nil =>
      intro p xs route trace
      have equal := List.cons.inj trace
      exact ⟨p, [], xs, equal.1, rfl, .nil p, route, by simp only [List.map_nil, equal.1], equal.2⟩
  | cons a left ih =>
      intro p xs route trace
      have equal := List.cons.inj trace
      cases route with
      | nil p =>
          have impossible := congrArg List.length equal.2
          simp only [List.map_nil, List.length_nil, List.length_append, List.length_cons] at impossible
          omega
      | @cons p next q rest step tail =>
          obtain ⟨at, before, after, atVertex, original, prefix, suffix, physical, final⟩ :=
            ih next rest tail (by simpa only [List.map_cons] using equal.2)
          refine ⟨at, next :: before, after, atVertex, ?_, .cons step prefix, suffix, ?_, final⟩
          · simpa only [List.cons_append, original]
          · simpa only [List.map_cons, List.cons_append, equal.1] using congrArg (a :: ·) physical

theorem nonempty_ends_at {A : Type u} {R : A → A → Prop} {p q : A}
    {xs : List A} (route : Route R p xs q) (nonempty : xs ≠ []) :
    ∃ before, xs = before ++ [q] := by
  revert nonempty
  induction route with
  | nil p => intro nonempty; exact (nonempty rfl).elim
  | @cons p next q rest step tail ih =>
      intro _
      cases rest with
      | nil => cases tail; exact ⟨[], rfl⟩
      | cons a rest =>
          obtain ⟨before, trace⟩ := ih (by intro impossible; cases impossible)
          exact ⟨next :: before, by simpa only [List.cons_append, trace]⟩

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation
open DiscriminatingStatus WeakInducing
open SourceSelection (AncestorOf)

universe u

theorem append_singleton_cancel {V : Type u} (left right : List V) (v : V)
    (equal : left ++ [v] = right ++ [v]) : left = right := by
  have reversed := congrArg List.reverse equal
  simp only [List.reverse_concat] at reversed
  exact List.reverse_inj.mp (List.cons.inj reversed).2

/-- A vertex-list formulation of the forward contradiction. Its retained
arms, actual arrival states, endpoint mark, and first-hit simplicity are
all obtained from the original path, not supplied as a new path oracle. -/
theorem collider_minimal_no_right_hit {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (acyclic : ∀ a xs, Route (Directed G) a xs a → xs = [])
    (C : V → Prop) (x y a b v finish : V)
    (left middle right branch remaining : List V) {old : List V}
    (minimal : ColliderMinimal G C x y old)
    (original : x :: old = left ++ a :: b :: (middle ++ v :: right))
    (atCollider : ∀ c rest, middle ++ v :: right = c :: rest → Collider G a b c)
    (shortest : MinimumDirectedPath G C b ((branch ++ [v]) ++ remaining) finish)
    (directed : Route (Directed G) b (branch ++ [v]) v)
    (suffix : Route (Directed G) v remaining finish)
    (firstHit : ∀ q ∈ branch, q ∉ x :: old) : False := by
  obtain ⟨last, states, route, physical⟩ := vertex_path_route_trace G single C x y minimal.1
  have splitB : x :: states.map Arrival.vertex = (left ++ [a]) ++ b :: (middle ++ v :: right) := by
    rw [physical, original]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨bState, before, rest, bVertex, wholeTrace, beforeRoute, restRoute, beforeTrace, restTrace⟩ :=
    route.split_at_mapped_vertex Arrival.vertex (left ++ [a]) (middle ++ v :: right) b splitB
  have splitV : bState.vertex :: rest.map Arrival.vertex = (b :: middle) ++ v :: right := by
    rw [bVertex, restTrace]
    rfl
  obtain ⟨vState, between, after, vVertex, restStates, betweenRoute, afterRoute, betweenTrace, afterTrace⟩ :=
    restRoute.split_at_mapped_vertex Arrival.vertex (b :: middle) right v splitV
  have middleTrace : between.map Arrival.vertex = middle ++ [v] := by
    have equality : b :: between.map Arrival.vertex = b :: (middle ++ [v]) := by
      simpa only [bVertex, List.cons_append] using betweenTrace
    exact (List.cons.inj equality).2
  have nonempty : between ≠ [] := by
    intro empty
    rw [empty, List.map_nil] at middleTrace
    have lengths := congrArg List.length middleTrace
    simp only [List.length_nil, List.length_append, List.length_singleton] at lengths
    omega
  obtain ⟨middleStates, middleEnd⟩ := betweenRoute.nonempty_ends_at nonempty
  have middlePhysical : middleStates.map Arrival.vertex = middle := by
    apply append_singleton_cancel _ _ v
    simpa only [middleEnd, List.map_append, List.map_cons, List.map_nil, vVertex] using middleTrace
  have oldPhysical : old = before.map Arrival.vertex ++ middleStates.map Arrival.vertex ++
      v :: after.map Arrival.vertex := by
    rw [← physical, wholeTrace, restStates, middleEnd]
    simp only [List.map_append, List.map_cons, List.map_nil, vVertex,
      List.append_assoc, List.singleton_append]
  have prefixPhysical : x :: before.map Arrival.vertex = left ++ [a, b] := by
    simpa only [List.append_assoc, List.singleton_append] using beforeTrace
  have firstEdge : Adjacent G a b := by
    -- The edge is also forced by the original collider at b.
    cases middle with
    | nil =>
        obtain ⟨ma, mc, first, _⟩ := atCollider v right rfl
        exact ⟨ma, .head, first⟩
    | cons c rest =>
        obtain ⟨ma, mc, first, _⟩ := atCollider c (rest ++ v :: right) rfl
        exact ⟨ma, .head, first⟩
  obtain ⟨leftMark, incoming, first⟩ := firstEdge
  have sourceMinimal : ColliderMinimal G C x y
      (before.map Arrival.vertex ++ middleStates.map Arrival.vertex ++ v :: after.map Arrival.vertex) := by
    simpa only [oldPhysical] using minimal
  have sourceCollider : ∀ c tail,
      middleStates.map Arrival.vertex ++ v :: after.map Arrival.vertex = c :: tail → Collider G a b c := by
    intro c tail equation
    exact atCollider c tail (by simpa only [middlePhysical, afterTrace] using equation)
  have sourceFirstHit : ∀ q ∈ branch, q ∉
      x :: (before.map Arrival.vertex ++ middleStates.map Arrival.vertex ++ v :: after.map Arrival.vertex) := by
    simpa only [oldPhysical] using firstHit
  exact collider_minimal_no_forward_branch_hit G single acyclic C x y a b v finish
    before middleStates after left branch remaining bState.incoming vState.incoming last leftMark incoming
    (by simpa only [← bVertex] using beforeRoute)
    (by simpa only [middleEnd, ← bVertex, ← vVertex] using betweenRoute)
    (by simpa only [← vVertex] using afterRoute)
    prefixPhysical first sourceCollider sourceMinimal shortest directed suffix sourceFirstHit

/-- Every shortest activation branch of every collider of this specific
minimum avoids the entire main path after its start, including endpoints,
other colliders, and conditioned colliders. No original source-size bound
or independent branch realization is assumed. -/
theorem shortest_activation_avoids_main_path {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (acyclic : ∀ a xs, Route (Directed G) a xs a → xs = [])
    (C : V → Prop) (x y a b c finish : V) (left right : List V) {old branch : List V}
    (minimal : ColliderMinimal G C x y old)
    (original : x :: old = left ++ a :: b :: c :: right)
    (collider : Collider G a b c)
    (shortest : MinimumDirectedPath G C b branch finish) :
    ∀ v ∈ branch, v ∉ x :: old := by
  intro hit member onMain
  obtain ⟨v, front, back, branchTrace, prefix, suffix, vOnMain, first⟩ :=
    shortest.route.first_hit_after_start (fun q => q ∈ x :: old) ⟨hit, member, onMain⟩
  have shortest' : MinimumDirectedPath G C b ((front ++ [v]) ++ back) finish := by
    simpa only [branchTrace, List.append_assoc, List.singleton_append] using shortest
  have notStart : v ≠ b := by
    intro same
    have simple := shortest.route.acyclic_trace_nodup acyclic
    have outside := (List.nodup_cons.mp simple).1
    apply outside
    rw [branchTrace]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl same.symm)))
  have location : v ∈ left ++ [a] ∨ v ∈ c :: right := by
    rw [original] at vOnMain
    have split : v ∈ (left ++ [a]) ++ b :: c :: right := by
      simpa only [List.append_assoc, List.singleton_append] using vOnMain
    rcases List.mem_append.mp split with before | after
    · exact Or.inl before
    · rcases List.mem_cons.mp after with same | later
      · exact (notStart same).elim
      · exact Or.inr later
  rcases location with before | after
  · obtain ⟨reversed, reverseMinimal, reverseTrace⟩ :=
      collider_minimal_reverse_trace G single symmetric C x y minimal
    have reverseLiteral : y :: reversed = right.reverse ++ c :: b :: a :: left.reverse := by
      rw [reverseTrace, original]
      simp only [List.reverse_append, List.reverse_cons, List.append_assoc, List.singleton_append]
    have onSuffix : v ∈ a :: left.reverse := by
      have reversedMember := List.mem_reverse.mpr before
      simpa only [List.reverse_concat] using reversedMember
    obtain ⟨middle, tail, tailTrace⟩ := List.mem_iff_append.mp onSuffix
    have reversedCollider := (collider_reverse_iff G symmetric a b c).mp collider
    apply collider_minimal_no_right_hit G single acyclic C y x c b v finish
      right.reverse middle tail front back reverseMinimal
    · rw [reverseLiteral, ← tailTrace]
    · intro next rest equation
      have head : a = next := (List.cons.inj (tailTrace.trans equation)).1
      simpa only [← head] using reversedCollider
    · exact shortest'
    · exact prefix
    · exact suffix
    · intro q inFront onReversed
      apply first q inFront
      rw [reverseTrace] at onReversed
      exact List.mem_reverse.mp onReversed
  · obtain ⟨middle, tail, tailTrace⟩ := List.mem_iff_append.mp after
    apply collider_minimal_no_right_hit G single acyclic C x y a b v finish
      left middle tail front back minimal
    · rw [original, ← tailTrace]
    · intro next rest equation
      have head : c = next := (List.cons.inj (tailTrace.trans equation)).1
      simpa only [← head] using collider
    · exact shortest'
    · exact prefix
    · exact suffix
    · exact first

end RestrictedCausal.VertexActivePaths
