import ActivationBranchPairSplice

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Ordered two-collider branch exclusion from the same actual minimum path.
Choose the first meeting along the second branch, so its proper prefix is
disjoint from the entire first branch. All new vertices are off the main
path by Lemma A. This supplies the physical simple splice before invoking
the two-versus-one collider count contradiction. No probability claim.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation
open DiscriminatingStatus WeakInducing
open SourceSelection (AncestorOf)

universe u

theorem shortest_activation_branches_disjoint_ordered {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (acyclic : ∀ a xs, Route (Directed G) a xs a → xs = [])
    (C : V → Prop) (x y a b d e c finishB finishE : V)
    («left» middle «right» : List V) {old branchB branchE : List V}
    (minimal : ColliderMinimal G C x y old)
    (original : x :: old = «left» ++ a :: b :: (middle ++ d :: e :: c :: «right»))
    (atB : ∀ «next» rest, middle ++ d :: e :: c :: «right» = «next» :: rest → Collider G a b «next»)
    (atE : Collider G d e c)
    (shortestB : MinimumDirectedPath G C b branchB finishB)
    (shortestE : MinimumDirectedPath G C e branchE finishE) :
    ∀ z ∈ branchB, z ∉ branchE := by
  intro z inB inE
  have avoidB : ∀ q ∈ branchB, q ∉ x :: old := by
    cases middle with
    | nil =>
        exact shortest_activation_avoids_main_path G single symmetric acyclic C x y a b d finishB
          «left» (e :: c :: «right») minimal original (atB d (e :: c :: «right») rfl) shortestB
    | cons «next» rest =>
        exact shortest_activation_avoids_main_path G single symmetric acyclic C x y a b «next» finishB
          «left» (rest ++ d :: e :: c :: «right») minimal original
          (atB «next» (rest ++ d :: e :: c :: «right») rfl) shortestB
  have eOriginal : x :: old = («left» ++ a :: b :: middle) ++ d :: e :: c :: «right» := by
    rw [original]
    simp only [List.append_assoc, List.cons_append]
  have avoidE := shortest_activation_avoids_main_path G single symmetric acyclic C x y d e c finishE
    («left» ++ a :: b :: middle) «right» minimal eOriginal atE shortestE
  obtain ⟨v, rightFront, rightBack, rightWhole, rightPrefix, rightSuffix, vInB, rightFirst⟩ :=
    shortestE.route.first_hit_after_start (fun q => q ∈ branchB) ⟨z, inE, inB⟩
  obtain ⟨v', leftFront, leftBack, leftWhole, leftPrefix, leftSuffix, equalV, leftFirst⟩ :=
    shortestB.route.first_hit_after_start (fun q => q = v) ⟨v, vInB, rfl⟩
  subst v'
  have minB : MinimumDirectedPath G C b ((leftFront ++ [v]) ++ leftBack) finishB := by
    simpa only [leftWhole, List.append_assoc, List.singleton_append] using shortestB
  have minE : MinimumDirectedPath G C e ((rightFront ++ [v]) ++ rightBack) finishE := by
    simpa only [rightWhole, List.append_assoc, List.singleton_append] using shortestE
  have leftSubset : ∀ q ∈ leftFront ++ [v], q ∈ branchB := by
    intro q member
    rw [leftWhole]
    simpa only [List.append_assoc, List.singleton_append] using
      (List.mem_append.mpr (Or.inl member) : q ∈ (leftFront ++ [v]) ++ leftBack)
  have rightSubset : ∀ q ∈ rightFront, q ∈ branchE := by
    intro q member
    rw [rightWhole]
    exact List.mem_append.mpr (Or.inl member)
  have leftSimple : (leftFront ++ [v]).Nodup :=
    (List.nodup_cons.mp (leftPrefix.acyclic_trace_nodup acyclic)).2
  have rightSimple : rightFront.Nodup :=
    (List.nodup_cons.mp (rightPrefix.acyclic_trace_nodup acyclic)).2.sublist
      (List.sublist_append_left rightFront [v])
  have freshSimple : ((leftFront ++ [v]) ++ rightFront.reverse).Nodup := by
    have result := nodup_insert_fresh_list (leftFront ++ [v]) rightFront.reverse []
      (by simpa only [List.append_nil] using leftSimple) rightSimple.reverse
      (by
        intro q member inLeft
        apply rightFirst q (List.mem_reverse.mp member)
        apply leftSubset q
        simpa only [List.append_nil] using inLeft)
    simpa only [List.append_nil] using result
  have freshOutside : ∀ q ∈ (leftFront ++ [v]) ++ rightFront.reverse, q ∉ x :: old := by
    intro q member
    rcases List.mem_append.mp member with inLeft | inRight
    · exact avoidB q (leftSubset q inLeft)
    · exact avoidE q (rightSubset q (List.mem_reverse.mp inRight))
  have vertexSimple : ((«left» ++ [a, b]) ++ ((leftFront ++ [v]) ++ rightFront.reverse) ++
      e :: c :: «right»).Nodup := by
    apply nodup_fresh_replacement («left» ++ [a, b]) (middle ++ [d])
      ((leftFront ++ [v]) ++ rightFront.reverse) (e :: c :: «right»)
    · have simple := minimal.1.2.1
      rw [original] at simple
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using simple
    · exact freshSimple
    · intro q member
      have outside := freshOutside q member
      rw [original] at outside
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using outside
  have leftSafe := departures_outside_prefix C (leftFront ++ [v]) leftBack b
    (minimum_directed_departures_outside G C minB)
  have rightSafe := departures_outside_prefix C (rightFront ++ [v]) rightBack e
    (minimum_directed_departures_outside G C minE)
  have eOutside : ¬ C e := by
    cases rightFront with
    | nil => exact rightSafe.1
    | cons «next» rest => exact rightSafe.1
  have eActivated : AncestorOf G C e := ⟨finishE, ⟨branchE, shortestE.route⟩, shortestE.endpoint⟩
  have vActivated : AncestorOf G C v := ⟨finishB, ⟨leftBack, leftSuffix⟩, shortestB.endpoint⟩
  obtain ⟨last, states, actual, physical⟩ := vertex_path_route_trace G single C x y minimal.1
  have splitB : x :: states.map Arrival.vertex =
      («left» ++ [a]) ++ b :: (middle ++ d :: e :: c :: «right») := by
    rw [physical, original]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨bState, before, restStates, bVertex, wholeStates, beforeRoute, restRoute, beforeTrace, restTrace⟩ :=
    actual.split_at_mapped_vertex Arrival.vertex («left» ++ [a]) (middle ++ d :: e :: c :: «right») b splitB
  have splitE : bState.vertex :: restStates.map Arrival.vertex = (b :: middle ++ [d]) ++ e :: c :: «right» := by
    rw [bVertex, restTrace]
    simp only [List.cons_append, List.append_assoc, List.singleton_append]
  obtain ⟨eState, between, after, eVertex, middleStates, betweenRoute, afterRoute, betweenTrace, afterTrace⟩ :=
    restRoute.split_at_mapped_vertex Arrival.vertex (b :: middle ++ [d]) (c :: «right») e splitE
  have beforePhysical : x :: before.map Arrival.vertex = «left» ++ [a, b] := by
    simpa only [List.append_assoc, List.singleton_append] using beforeTrace
  have actualSimple : ((x :: before.map Arrival.vertex) ++ leftFront ++
      v :: rightFront.reverse ++ e :: after.map Arrival.vertex).Nodup := by
    rw [beforePhysical, afterTrace]
    simpa only [List.append_assoc, List.singleton_append, List.cons_append] using vertexSimple
  obtain ⟨new, candidate, «trace»⟩ := two_activation_branch_splice G single symmetric C x y b e v
    leftFront rightFront (by simpa only [← bVertex] using beforeRoute)
    (by simpa only [← eVertex] using afterRoute) leftPrefix rightPrefix leftSafe rightSafe
    eOutside eActivated vActivated actualSimple
  have newLiteral : x :: new = «left» ++ a :: b ::
      (leftFront ++ v :: rightFront.reverse ++ e :: c :: «right») := by
    rw [«trace», beforePhysical, afterTrace]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact collider_minimal_rejects_two_branch_splice G single symmetric C x y a b d e c v
    «left» middle «right» leftFront rightFront minimal candidate original newLiteral atB atE leftPrefix rightPrefix

end RestrictedCausal.VertexActivePaths
