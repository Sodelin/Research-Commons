import ColliderSpliceCosts


/- Pinned-context spelling variant: explicit original List.Sublist relation.
All proof scripts outside these annotation spellings, source predicates and
conclusion semantics are unchanged; frozen original retained separately. -/
/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Construct the genuine forward activation-branch splice, retaining exact
arrival-state and physical vertex traces. The branch has no collider even
at its departure join. The final join is activated by an actual C-descendant.
Freshness/simplicity and the original literal split remain visible premises;
their first-hit extraction, the leftward case and the branch-pair exclusion
are not silently replaced by this local construction.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation
open DiscriminatingStatus WeakInducing
open SourceSelection (AncestorOf)

universe u

theorem nodup_insert_fresh_list {V : Type u} («left» fresh «right» : List V)
    (retained : («left» ++ «right»).Nodup) (simple : fresh.Nodup)
    (outside : ∀ v ∈ fresh, v ∉ «left» ++ «right») : («left» ++ fresh ++ «right»).Nodup := by
  revert simple outside
  induction fresh with
  | nil => intro _ _; simpa only [List.append_nil] using retained
  | cons a fresh ih =>
      intro simple outside
      obtain ⟨notInTail, tailSimple⟩ := List.nodup_cons.mp simple
      have tailNodup := ih tailSimple (fun v member => outside v (List.mem_cons_of_mem _ member))
      have newOutside : a ∉ «left» ++ (fresh ++ «right») := by
        intro member
        rcases List.mem_append.mp member with inLeft | member
        · exact outside a List.mem_cons_self (List.mem_append.mpr (Or.inl inLeft))
        · rcases List.mem_append.mp member with inFresh | inRight
          · exact notInTail inFresh
          · exact outside a List.mem_cons_self (List.mem_append.mpr (Or.inr inRight))
      have inserted := nodup_insert_fresh «left» (fresh ++ «right») a
        (by simpa only [List.append_assoc] using tailNodup) newOutside
      simpa only [List.cons_append, List.append_assoc] using inserted

theorem nodup_fresh_replacement {V : Type u} («left» old fresh «right» : List V)
    (original : («left» ++ old ++ «right»).Nodup) (simple : fresh.Nodup)
    (outside : ∀ v ∈ fresh, v ∉ «left» ++ old ++ «right») :
    («left» ++ fresh ++ «right»).Nodup := by
  have retainedSub : List.Sublist («left» ++ «right») («left» ++ (old ++ «right»)) :=
    (List.sublist_append_right old «right»).append_left «left»
  have retained : («left» ++ «right»).Nodup :=
    (by simpa only [List.append_assoc] using original : («left» ++ (old ++ «right»)).Nodup).sublist retainedSub
  apply nodup_insert_fresh_list «left» fresh «right» retained simple
  intro v member inRetained
  apply outside v member
  have originalMember := retainedSub.subset inRetained
  simpa only [List.append_assoc] using originalMember

theorem directed_branch_no_colliders {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G) {b v : V} {xs : List V}
    (branch : Route (Directed G) b xs v) :
    ∀ a «left» incoming, G.edge a b «left» incoming →
      AllTriples (fun p q r => ¬ Collider G p q r) (a :: b :: xs) := by
  induction branch with
  | nil b => intro _ _ _ _; trivial
  | @cons b c v rest directed tail ih =>
      intro a «left» incoming «first»
      refine ⟨?_, ih b .tail .head directed⟩
      intro collider
      have «impossible» :=
        ((collider_iff_chosen_marks G single a b c «left» incoming .tail .head
          «first» directed).mp collider).2
      exact Mark.noConfusion «impossible»

/-- Any initial incoming mark can depart down a directed edge when its
vertex is unconditioned. This includes a retained endpoint with mark none. -/
theorem directed_safe_initial_route {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {b v : V} {xs : List V} (branch : Route (Directed G) b xs v)
    (safe : DeparturesOutside C b xs) (incoming : Option Mark) (positive : xs ≠ []) :
    Route (RealStep G C) ⟨b, incoming⟩
      (xs.map (fun q => (⟨q, some .head⟩ : Arrival V))) ⟨v, some .head⟩ := by
  cases branch with
  | nil b => exact (positive rfl).elim
  | @cons b «next» v rest edge tail =>
      refine .cons ⟨.tail, .head, edge, rfl, ?_⟩
        (directed_safe_head_route G C tail safe.2)
      cases incoming with
      | none => trivial
      | some mark => simpa [DepartureAllowed, ActiveAt] using safe.1

/-- This produces an actual path, not merely a plausible vertex diagram.
Both endpoint and zero-length retained suffix cases are included. -/
theorem forward_branch_splice {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G) (C : V → Prop) (x y b v : V)
    {atB atV : Option Mark} {last : Option Mark}
    {«left» «right» : List (Arrival V)} {branch : List V}
    (before : Route (RealStep G C) ⟨x, none⟩ «left» ⟨b, atB⟩)
    (after : Route (RealStep G C) ⟨v, atV⟩ «right» ⟨y, last⟩)
    (directed : Route (Directed G) b (branch ++ [v]) v)
    (safe : DeparturesOutside C b (branch ++ [v]))
    (activated : AncestorOf G C v) (initialOutside : atV = none → ¬ C v)
    (simple : ((x :: «left».map Arrival.vertex) ++ branch ++ v :: «right».map Arrival.vertex).Nodup) :
    ∃ new, Path G C x y new ∧
      x :: new = (x :: «left».map Arrival.vertex) ++ branch ++ v :: «right».map Arrival.vertex := by
  have positive : branch ++ [v] ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
    omega
  have middle := directed_safe_initial_route G C directed safe atB positive
  obtain ⟨newLast, suffix⟩ := rebuild_suffix_head G C after activated initialOutside
  let states := «left» ++ (branch ++ [v]).map
    (fun q => (⟨q, some .head⟩ : Arrival V)) ++ «right»
  have actual : Route (RealStep G C) ⟨x, none⟩ states ⟨y, newLast⟩ :=
    (before.append middle).append suffix
  have «trace» : (⟨x, none⟩ :: states).map Arrival.vertex =
      (x :: «left».map Arrival.vertex) ++ branch ++ v :: «right».map Arrival.vertex := by
    simp only [states, List.map_cons, List.map_append, List.map_map, List.map_nil,
      List.map_id_fun, List.map_id, List.cons_append, List.append_assoc,
      List.singleton_append]
  have actualSimple : ((⟨x, none⟩ :: states).map Arrival.vertex).Nodup := by
    rw [«trace»]
    exact simple
  exact ⟨states.map Arrival.vertex, active_route_vertex_path G single C x y actual actualSimple,
    by simpa only [List.map_cons] using «trace»⟩

/-- A first later hit lying to the right of the old collider is impossible.
Freshness is precisely the first-hit prefix property, not a global branch-
disjointness assumption. The shortest-branch suffix supplies both activation
at v and the strict potential decrease. Its endpoint may equal v itself.
The leftward first-hit case still needs reversal/order extraction. -/
theorem collider_minimal_no_forward_branch_hit {V : Type u} (G : MarkedGraph V)
    (single : SingleEdges G)
    (acyclic : ∀ a xs, Route (Directed G) a xs a → xs = [])
    (C : V → Prop) (x y a b v finish : V)
    («left» middle «right» : List (Arrival V)) (oldPrefix branch remaining : List V)
    (atB atV last : Option Mark) (leftMark incoming : Mark)
    (before : Route (RealStep G C) ⟨x, none⟩ «left» ⟨b, atB⟩)
    (between : Route (RealStep G C) ⟨b, atB⟩
      (middle ++ [⟨v, atV⟩]) ⟨v, atV⟩)
    (after : Route (RealStep G C) ⟨v, atV⟩ «right» ⟨y, last⟩)
    (prefixTrace : x :: «left».map Arrival.vertex = oldPrefix ++ [a, b])
    (firstEdge : G.edge a b leftMark incoming)
    (atCollider : ∀ c rest, middle.map Arrival.vertex ++ v :: «right».map Arrival.vertex = c :: rest →
      Collider G a b c)
    (minimal : ColliderMinimal G C x y
      («left».map Arrival.vertex ++ middle.map Arrival.vertex ++ v :: «right».map Arrival.vertex))
    (shortest : MinimumDirectedPath G C b ((branch ++ [v]) ++ remaining) finish)
    (directed : Route (Directed G) b (branch ++ [v]) v)
    (suffix : Route (Directed G) v remaining finish)
    (firstHit : ∀ q ∈ branch, q ∉
      x :: («left».map Arrival.vertex ++ middle.map Arrival.vertex ++ v :: «right».map Arrival.vertex)) :
    False := by
  have positive : branch ++ [v] ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
    omega
  have safe := departures_outside_prefix C (branch ++ [v]) remaining b
    (minimum_directed_departures_outside G C shortest)
  have activated : AncestorOf G C v := ⟨finish, ⟨remaining, suffix⟩, shortest.endpoint⟩
  have closer := minimum_directed_distance_strict_after_prefix G C shortest directed suffix positive
  have branchNodup : branch.Nodup := by
    have full := directed.acyclic_trace_nodup acyclic
    have tail := (List.nodup_cons.mp full).2
    exact tail.sublist (List.sublist_append_left branch [v])
  have simple : ((x :: «left».map Arrival.vertex) ++ branch ++ v :: «right».map Arrival.vertex).Nodup := by
    apply nodup_fresh_replacement (x :: «left».map Arrival.vertex) (middle.map Arrival.vertex)
      branch (v :: «right».map Arrival.vertex)
    · simpa only [List.cons_append, List.append_assoc] using minimal.1.2.1
    · exact branchNodup
    · intro q member
      simpa only [List.cons_append, List.append_assoc] using firstHit q member
  have initialOutside : atV = none → ¬ C v := by
    intro initial
    have nonempty : middle ++ [⟨v, atV⟩] ≠ [] := by
      intro empty
      have lengths := congrArg List.length empty
      simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
      omega
    obtain ⟨p, outgoing, received, edge, mark, active⟩ := between.terminal_step_of_nonempty nonempty
    have «impossible» : (none : Option Mark) = some received := initial.symm.trans mark
    cases «impossible»
  obtain ⟨new, candidate, newTrace⟩ := forward_branch_splice G single C x y b v before after
    directed safe activated initialOutside simple
  have oldTrace :
      x :: («left».map Arrival.vertex ++ middle.map Arrival.vertex ++ v :: «right».map Arrival.vertex) =
        oldPrefix ++ a :: b :: (middle.map Arrival.vertex ++ v :: «right».map Arrival.vertex) := by
    calc
      _ = (x :: «left».map Arrival.vertex) ++
        (middle.map Arrival.vertex ++ v :: «right».map Arrival.vertex) := by
          simp only [List.cons_append, List.append_assoc]
      _ = _ := by rw [prefixTrace]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  have newLiteral : x :: new = oldPrefix ++ a :: b :: (branch ++ v :: «right».map Arrival.vertex) := by
    rw [newTrace, prefixTrace]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact collider_minimal_rejects_branch_replacement G C x y a b v oldPrefix
    (middle.map Arrival.vertex) branch («right».map Arrival.vertex) minimal candidate oldTrace
    newLiteral atCollider
    (directed_branch_no_colliders G single directed a leftMark incoming firstEdge) closer

end RestrictedCausal.VertexActivePaths
