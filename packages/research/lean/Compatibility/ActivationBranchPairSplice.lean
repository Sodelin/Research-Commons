import ActivationMainPathExclusion

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The genuine two-directed-arm replacement at a shared activation vertex.
Both old colliders lose their collider status; the common vertex contributes
at most one. Actual route reversal retains every branch vertex. First-hit
branch disjointness and its ordered extraction are still downstream facts,
not encoded as an atomic-completeness or faithful-law premise.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation OriginalProjection
open DiscriminatingStatus WeakInducing
open SourceSelection (AncestorOf)

universe u

theorem activated_outside_departure {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    (v : V) (incoming : Option Mark) (outgoing : Mark)
    (outside : ¬ C v) (activated : AncestorOf G C v) :
    DepartureAllowed C (AncestorOf G C) v incoming outgoing := by
  cases incoming with
  | none => trivial
  | some mark =>
      cases mark <;> cases outgoing <;> simp [DepartureAllowed, ActiveAt, outside, activated]

theorem rebuild_suffix_activated_outside {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {p q : Arrival V} {xs : List (Arrival V)} (route : Route (RealStep G C) p xs q)
    (outside : ¬ C p.vertex) (activated : AncestorOf G C p.vertex) (incoming : Option Mark) :
    ∃ last, Route (RealStep G C) ⟨p.vertex, incoming⟩ xs ⟨q.vertex, last⟩ := by
  cases route with
  | nil p => exact ⟨incoming, .nil _⟩
  | @cons p «next» q rest step tail =>
      obtain ⟨outgoing, received, edge, mark, _⟩ := step
      exact ⟨q.incoming, .cons ⟨outgoing, received, edge, mark,
        activated_outside_departure G C p.vertex incoming outgoing outside activated⟩ tail⟩

/-- Construct a real active path along b -> ... -> v <- ... <- e,
retaining the original outer arms. The full physical simplicity premise
will be furnished by first-hit disjointness and main-path exclusion. -/
theorem two_activation_branch_splice {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C : V → Prop) (x y b e v : V) (leftBranch rightBranch : List V)
    {atB atE last : Option Mark} {«left» «right» : List (Arrival V)}
    (before : Route (RealStep G C) ⟨x, none⟩ «left» ⟨b, atB⟩)
    (after : Route (RealStep G C) ⟨e, atE⟩ «right» ⟨y, last⟩)
    (leftDirected : Route (Directed G) b (leftBranch ++ [v]) v)
    (rightDirected : Route (Directed G) e (rightBranch ++ [v]) v)
    (leftSafe : DeparturesOutside C b (leftBranch ++ [v]))
    (rightSafe : DeparturesOutside C e (rightBranch ++ [v]))
    (eOutside : ¬ C e) (eActivated : AncestorOf G C e) (vActivated : AncestorOf G C v)
    (simple : ((x :: «left».map Arrival.vertex) ++ leftBranch ++
      v :: rightBranch.reverse ++ e :: «right».map Arrival.vertex).Nodup) :
    ∃ new, Path G C x y new ∧ x :: new = (x :: «left».map Arrival.vertex) ++ leftBranch ++
      v :: rightBranch.reverse ++ e :: «right».map Arrival.vertex := by
  have positive (branch : List V) : branch ++ [v] ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
    omega
  have leftRoute := directed_safe_initial_route G C leftDirected leftSafe atB (positive leftBranch)
  have rightRoute := directed_safe_initial_route G C rightDirected rightSafe none (positive rightBranch)
  obtain ⟨arrivalAtE, backward, reversed, compatible, backwardTrace⟩ :=
    reverse_required_arrival_trace G symmetric C (AncestorOf G C) rightRoute (some .head)
      (by simpa [DepartureAllowed, ActiveAt] using vActivated)
  have backwardVertices : backward.map Arrival.vertex = rightBranch.reverse ++ [e] := by
    have physical : v :: backward.map Arrival.vertex = v :: (rightBranch.reverse ++ [e]) := by
      simpa [Function.comp_def, List.reverse_cons, List.reverse_concat, List.cons_append] using backwardTrace
    exact (List.cons.inj physical).2
  obtain ⟨newLast, suffix⟩ :=
    rebuild_suffix_activated_outside G C after eOutside eActivated arrivalAtE
  let states := «left» ++ (leftBranch ++ [v]).map
    (fun q => (⟨q, some .head⟩ : Arrival V)) ++ backward ++ «right»
  have route : Route (RealStep G C) ⟨x, none⟩ states ⟨y, newLast⟩ :=
    ((before.append leftRoute).append reversed).append suffix
  have «trace» : (⟨x, none⟩ :: states).map Arrival.vertex =
      (x :: «left».map Arrival.vertex) ++ leftBranch ++
        v :: rightBranch.reverse ++ e :: «right».map Arrival.vertex := by
    simp only [states, List.map_cons, List.map_append, List.map_map, List.map_id_fun,
      List.map_id, backwardVertices, List.append_assoc, List.singleton_append, List.cons_append, Function.comp_def, List.nil_append]
    simp
  have routeSimple : ((⟨x, none⟩ :: states).map Arrival.vertex).Nodup := by rw [«trace»]; exact simple
  exact ⟨states.map Arrival.vertex, active_route_vertex_path G single C x y route routeSimple,
    by simpa only [List.map_cons] using «trace»⟩

/-- Both boundary collider payments occur on the literal original trace.
The middle d may equal a vertex next to b, but b and e are distinct centers. -/
theorem old_two_collider_count_lower {V : Type u} (G : MarkedGraph V)
    («left» middle «right» : List V) (a b d e c : V)
    (atB : ∀ «next» rest, middle ++ d :: e :: c :: «right» = «next» :: rest → Collider G a b «next»)
    (atE : Collider G d e c) :
    colliderCount G («left» ++ [a, b]) + 2 + colliderCount G (e :: c :: «right») ≤
      colliderCount G («left» ++ a :: b :: (middle ++ d :: e :: c :: «right»)) := by
  classical
  have bound := weighted_old_splice_lower G (fun _ => 1) «left» middle (e :: c :: «right») a b d atB
  simp only [weightedColliders_eq_count, colliderCount, if_pos atE] at bound
  omega

/-- The two directed arms have zero interior count. Only their shared
vertex v remains between the unchanged outer prefix and suffix. -/
theorem new_two_branch_count_upper {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    («left» «right» leftBranch rightBranch : List V) (a b e c v : V)
    (leftMark leftIn rightMark rightIn : Mark)
    (leftEdge : G.edge a b leftMark leftIn) (rightEdge : G.edge c e rightMark rightIn)
    (leftDirected : Route (Directed G) b (leftBranch ++ [v]) v)
    (rightDirected : Route (Directed G) e (rightBranch ++ [v]) v) :
    colliderCount G («left» ++ a :: b :: (leftBranch ++ v :: rightBranch.reverse ++ e :: c :: «right»)) ≤
      colliderCount G («left» ++ [a, b]) + 1 + colliderCount G (e :: c :: «right») := by
  classical
  let f := fun p q r => if Collider G p q r then 1 else 0
  have leftZero : tripleCost f (a :: b :: (leftBranch ++ [v])) = 0 :=
    weightedColliders_zero G (fun _ => 1) _
      (directed_branch_no_colliders G single leftDirected a leftMark leftIn leftEdge)
  have rightZeroForward : colliderCount G (c :: e :: (rightBranch ++ [v])) = 0 := by
    simpa only [weightedColliders_eq_count] using
      weightedColliders_zero G (fun _ => 1) _
        (directed_branch_no_colliders G single rightDirected c rightMark rightIn rightEdge)
  have rightZero : tripleCost f (v :: (rightBranch.reverse ++ [e, c])) = 0 := by
    have reversed := colliderCount_reverse G symmetric (c :: e :: (rightBranch ++ [v]))
    rw [rightZeroForward] at reversed
    change weightedColliders G (fun _ => 1) (v :: (rightBranch.reverse ++ [e, c])) = 0
    rw [weightedColliders_eq_count]
    simpa [List.reverse_cons, List.reverse_concat, List.append_assoc] using reversed
  have middleBound := tripleCost_join_le f (a :: b :: leftBranch)
    (rightBranch.reverse ++ [e, c]) v 1 (by intro p r; dsimp [f]; split_ifs <;> omega)
  change tripleCost f (a :: b :: (leftBranch ++ v :: (rightBranch.reverse ++ [e, c]))) ≤
    tripleCost f (a :: b :: (leftBranch ++ [v])) + 1 +
      tripleCost f (v :: (rightBranch.reverse ++ [e, c])) at middleBound
  rw [leftZero, rightZero] at middleBound
  rw [← weightedColliders_eq_count, ← weightedColliders_eq_count, ← weightedColliders_eq_count]
  change tripleCost f («left» ++ a :: b :: (leftBranch ++ v :: rightBranch.reverse ++ e :: c :: «right»)) ≤
    tripleCost f («left» ++ [a, b]) + 1 + tripleCost f (e :: c :: «right»)
  rw [tripleCost_append_pair f «left»]
  have inner := tripleCost_append_pair f (a :: b :: (leftBranch ++ v :: rightBranch.reverse)) «right» e c
  simp only [List.cons_append, List.append_assoc] at inner ⊢
  rw [inner]
  omega

theorem collider_minimal_rejects_two_branch_splice {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    (C : V → Prop) (x y a b d e c v : V)
    («left» middle «right» leftBranch rightBranch : List V) {old new : List V}
    (minimal : ColliderMinimal G C x y old) (candidate : Path G C x y new)
    (oldTrace : x :: old = «left» ++ a :: b :: (middle ++ d :: e :: c :: «right»))
    (newTrace : x :: new = «left» ++ a :: b :: (leftBranch ++ v :: rightBranch.reverse ++ e :: c :: «right»))
    (atB : ∀ «next» rest, middle ++ d :: e :: c :: «right» = «next» :: rest → Collider G a b «next»)
    (atE : Collider G d e c)
    (leftDirected : Route (Directed G) b (leftBranch ++ [v]) v)
    (rightDirected : Route (Directed G) e (rightBranch ++ [v]) v) : False := by
  have «first» : Adjacent G a b := by
    cases middle with
    | nil =>
        obtain ⟨ma, mc, edge, _⟩ := atB d (e :: c :: «right») rfl
        exact ⟨ma, .head, edge⟩
    | cons «next» rest =>
        obtain ⟨ma, mc, edge, _⟩ := atB «next» (rest ++ d :: e :: c :: «right») rfl
        exact ⟨ma, .head, edge⟩
  obtain ⟨leftMark, leftIn, leftEdge⟩ := «first»
  have lower := old_two_collider_count_lower G «left» middle «right» a b d e c atB atE
  obtain ⟨fromD, toC, intoE, fromE⟩ := atE
  have upper := new_two_branch_count_upper G single symmetric «left» «right» leftBranch rightBranch a b e c v
    leftMark leftIn toC .head leftEdge (symmetric _ _ _ _ fromE) leftDirected rightDirected
  have bound := minimal.2.1 new candidate
  rw [oldTrace, newTrace] at bound
  omega

end RestrictedCausal.VertexActivePaths
