import FiniteDependencyInduction

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual local shared-separator status transport. Prefix collider invariance
is an explicit induction premise. The target prefix is reconstructed with
real edge marks; its parent arrows are then derived from the shared
separator. Neither discriminating-path invariance nor parent invariance is
postulated. Attribution: Ali--Richardson--Spirtes (2009), Lemmas 3.10--3.13.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem endpoint_mem_of_nonempty {V : Type u} {R : V → V → Prop}
    {a b : V} {xs : List V} (route : Route R a xs b) (nonempty : xs ≠ []) : b ∈ xs := by
  revert nonempty
  induction route with
  | nil => intro «impossible»; exact («impossible» rfl).elim
  | @cons a «next» b rest step tail ih =>
      intro _
      cases rest with
      | nil => cases tail; exact List.mem_cons_self
      | cons r rs => exact List.mem_cons_of_mem _ (ih (by intro «impossible»; cases «impossible»))

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.DiscriminatingStatus

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open VertexActivePaths WeakInducing

universe u

theorem parent_step_forget {V : Type u} (G : MarkedGraph V) (y : V)
    {p q : Arrival V} (step : ColliderParentStep G y p q) : ColliderStep G p q := by
  obtain ⟨outgoing, incoming, edge, mark, details⟩ := step
  refine ⟨outgoing, incoming, edge, mark, ?_⟩
  cases previous : p.incoming with
  | none => trivial
  | some m =>
      have all : m = .head ∧ outgoing = .head ∧ Directed G p.vertex y := by
        simpa only [previous] using details
      exact ⟨all.1, all.2.1⟩

theorem parent_route_forget {V : Type u} (G : MarkedGraph V) (y : V)
    {p q : Arrival V} {xs : List (Arrival V)} (route : Route (ColliderParentStep G y) p xs q) :
    Route (ColliderStep G) p xs q := by
  induction route with
  | nil p => exact .nil p
  | cons step tail ih => exact .cons (parent_step_forget G y step) ih

theorem extended_parent_details {V : Type u} (G : MarkedGraph V) (y : V)
    {p q r : Arrival V} {xs : List (Arrival V)}
    (route : Route (ColliderParentStep G y) p xs q) (last : ColliderParentStep G y q r) :
    ∀ state ∈ xs, state.incoming = some .head ∧ Directed G state.vertex y := by
  revert r
  induction route with
  | nil p => intro r last state mem; cases mem
  | @cons p «next» q rest step tail ih =>
      intro r last
      have departure : ∃ after, ColliderParentStep G y «next» after := by
        cases tail with
        | nil => exact ⟨r, last⟩
        | cons nextStep remaining => exact ⟨_, nextStep⟩
      obtain ⟨_, incoming, _, mark, _⟩ := step
      obtain ⟨after, outgoing, nextIncoming, _, _, details⟩ := departure
      have current : incoming = .head ∧ outgoing = .head ∧ Directed G «next».vertex y := by
        simpa only [mark] using details
      intro state mem
      rcases List.mem_cons.mp mem with eq | mem
      · subst state
        exact ⟨mark.trans (congrArg some current.1), current.2.2⟩
      · exact ih r last state mem

/-- Rebuild the head-arrival part of the target prefix. Two consecutive
collider triples determine both incidences of each edge between parents;
the final edge to b retains its possibly different arrival mark. -/
theorem rebuild_head_prefix {V : Type u} {R : Arrival V → Arrival V → Prop}
    (H : MarkedGraph V) (single : SingleEdges H) {p q : Arrival V} {xs : List (Arrival V)}
    (shape : Route R p xs q) :
    ∀ (previous b : V), p.incoming = some .head →
      (∀ r ∈ xs, r.incoming = some .head) →
      AllTriples (Collider H) (previous :: ((p :: xs).map Arrival.vertex ++ [b])) →
      Route (ColliderStep H) p xs q ∧ ∃ incoming, H.edge q.vertex b .head incoming := by
  induction shape with
  | nil p =>
      intro previous b head allHeads colliders
      obtain ⟨«left», «right», «first», last⟩ := colliders.1
      exact ⟨.nil p, «right», last⟩
  | @cons p «next» q rest sourceStep tail ih =>
      intro previous b head allHeads colliders
      have nextHead := allHeads «next» List.mem_cons_self
      have tailResult := ih p.vertex b nextHead
        (fun r mem => allHeads r (List.mem_cons_of_mem _ mem)) colliders.2
      obtain ⟨_, incoming, _, firstOutgoing⟩ := colliders.1
      have nextCollider : ∃ following, Collider H p.vertex «next».vertex following := by
        cases rest with
        | nil => exact ⟨b, colliders.2.1⟩
        | cons after remaining => exact ⟨after.vertex, colliders.2.1⟩
      obtain ⟨following, «left», «right», secondIncoming, _⟩ := nextCollider
      have incomingHead : incoming = .head :=
        (single p.vertex «next».vertex .head incoming «left» .head firstOutgoing secondIncoming).2
      refine ⟨.cons ?_ tailResult.1, tailResult.2⟩
      refine ⟨.head, .head, incomingHead ▸ firstOutgoing, nextHead, ?_⟩
      simpa only [head] using (show Mark.head = .head ∧ Mark.head = .head from ⟨rfl, rfl⟩)

theorem rebuild_parent_prefix {V : Type u} {R : Arrival V → Arrival V → Prop}
    (H : MarkedGraph V) (single : SingleEdges H) (x b : V)
    {q : Arrival V} {xs : List (Arrival V)} (shape : Route R ⟨x, none⟩ xs q)
    (nonempty : xs ≠ []) (allHeads : ∀ r ∈ xs, r.incoming = some .head)
    (colliders : AllTriples (Collider H) ((⟨x, none⟩ :: xs).map Arrival.vertex ++ [b])) :
    Route (ColliderStep H) ⟨x, none⟩ xs q ∧ ∃ incoming, H.edge q.vertex b .head incoming := by
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons «first» rest =>
      cases shape with
      | cons step tail =>
          have firstHead := allHeads «first» List.mem_cons_self
          have result := rebuild_head_prefix H single tail x b firstHead
            (fun r mem => allHeads r (List.mem_cons_of_mem _ mem)) colliders
          have firstCollider : ∃ following, Collider H x «first».vertex following := by
            cases rest with
            | nil => exact ⟨b, colliders.1⟩
            | cons «next» remaining => exact ⟨«next».vertex, colliders.1⟩
          obtain ⟨following, outgoing, incoming, edge, _⟩ := firstCollider
          exact ⟨.cons ⟨outgoing, .head, edge, firstHead, trivial⟩ result.1, result.2⟩

theorem witness_start_ne_finish {V : Type u} {G : MarkedGraph V} {a b c : V}
    (w : DiscriminatingWitness G a b c) : w.start ≠ c := by
  intro equal
  have simple : (w.start :: ((w.parents ++ [w.terminal]).map Arrival.vertex ++ [c])).Nodup := by
    simpa only [List.map_cons, List.cons_append] using w.simple
  apply (List.nodup_cons.mp simple).1
  exact List.mem_append.mpr (Or.inr (by simpa only [List.mem_singleton] using equal))

/-- Once the earlier prefix colliders are invariant, one shared separator
forces the terminal triple's collider status to agree. The actual target
prefix, all of its parent arrows, and its possibly changed terminal arrival
mark are constructed here. This is the local step used by well-founded path
induction, not an assumption that every discriminating path is shared. -/
theorem witness_status_transfer {V : Type u} (G H : MarkedGraph V)
    (lawsH : AncestralLaws H) (singleG : SingleEdges G) (singleH : SingleEdges H)
    (skeleton : ∀ x y, Adjacent G x y ↔ Adjacent H x y)
    (shared : SharedSeparators G H) {a b c : V}
    (w : DiscriminatingWitness G a b c)
    (prefixColliders : AllTriples (Collider H)
      (((⟨w.start, none⟩ :: w.parents).map Arrival.vertex) ++ [b])) :
    Collider G a b c ↔ Collider H a b c := by
  have details := extended_parent_details G c w.parent_prefix w.last_parent_step
  have heads : ∀ r ∈ w.parents, r.incoming = some .head := fun r mem => (details r mem).1
  have parents : ∀ r ∈ w.parents, Directed G r.vertex c := fun r mem => (details r mem).2
  have sourcePrefix := parent_route_forget G c w.parent_prefix
  obtain ⟨targetPrefix, terminalIncoming, targetLast⟩ :=
    rebuild_parent_prefix H singleH w.start b w.parent_prefix w.nonempty heads prefixColliders
  obtain ⟨Z, notStart, notEnd, sepG, sepH⟩ := shared w.start c (witness_start_ne_finish w) w.nonadjacent
  have shorterSimple : (((⟨w.start, none⟩ :: w.parents).map Arrival.vertex) ++ [c]).Nodup := by
    apply prefix_terminal_nodup _ [w.terminal.vertex] c
    simpa only [List.map_cons, List.map_append, List.map_nil, List.cons_append, List.append_assoc] using w.simple
  have targetParents := collider_prefix_parent_transfer G H lawsH Z w.start c sourcePrefix targetPrefix
    heads parents (by
      intro r mem
      exact (skeleton r.vertex c).mp ⟨.tail, .head, parents r mem⟩) shorterSimple sepG sepH
  have targetParentPrefix := collider_route_parentize H c targetPrefix (by
    intro r mem notRoot
    rcases List.mem_cons.mp mem with equal | mem
    · subst r
      exact (notRoot rfl).elim
    · exact targetParents r mem)
  have beforeMem : w.before ∈ w.parents := w.parent_prefix.endpoint_mem_of_nonempty w.nonempty
  let targetTerminal : Arrival V := ⟨b, some terminalIncoming⟩
  have finalParentStep : ColliderParentStep H c w.before targetTerminal :=
    ⟨.head, terminalIncoming, targetLast, rfl, by
      simpa only [heads w.before beforeMem] using
        (show Mark.head = .head ∧ Mark.head = .head ∧ Directed H w.before.vertex c from
          ⟨rfl, rfl, targetParents w.before beforeMem⟩)⟩
  have fullTarget := targetParentPrefix.append (.cons finalParentStep (.nil _))
  obtain ⟨outG, inG, lastG⟩ := w.terminal_adjacent
  obtain ⟨outH, inH, lastH⟩ := (skeleton b c).mp w.terminal_adjacent
  have simpleH : (((⟨w.start, none⟩ :: (w.parents ++ [targetTerminal])).map Arrival.vertex) ++ [c]).Nodup := by
    simpa only [targetTerminal, List.map_cons, List.map_append, List.map_nil, w.terminal_vertex] using w.simple
  have status := shared_separator_terminal_agreement G H Z w.start c b w.terminal_vertex rfl
    w.prefix fullTarget outG inG outH inH (by simpa only [w.terminal_vertex] using lastG)
    lastH w.simple simpleH sepG sepH
  obtain ⟨leftG, arrivalG, edgeG, markG, _⟩ := w.last_parent_step
  have edgeG' : G.edge a b leftG arrivalG := by
    simpa only [w.before_vertex, w.terminal_vertex] using edgeG
  have edgeH' : H.edge a b .head terminalIncoming := by
    simpa only [w.before_vertex] using targetLast
  have fromG : Collider G a b c ↔ TerminalCollider w.terminal outG := by
    simpa only [TerminalCollider, markG, Option.some.injEq] using
      collider_iff_chosen_marks G singleG a b c leftG arrivalG outG inG edgeG' lastG
  have fromH : Collider H a b c ↔ TerminalCollider targetTerminal outH := by
    simpa only [TerminalCollider, targetTerminal, Option.some.injEq] using
      collider_iff_chosen_marks H singleH a b c .head terminalIncoming outH inH edgeH' lastH
  exact fromG.trans (status.trans fromH.symm)

end RestrictedCausal.DiscriminatingStatus
