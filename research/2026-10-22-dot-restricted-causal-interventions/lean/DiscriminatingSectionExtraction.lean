import MinimalPathChord

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Finite last-failure extraction and the backward parent propagation needed
for genuine discriminating sections of shortest active paths. All path
pieces remain in the same actual marked graph. Classical attribution:
Ali--Richardson--Spirtes (2009), Lemma 3.20.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem last_failure_suffix {V : Type u} {R : V → V → Prop} (P : V → Prop)
    {p q : V} {xs : List V} (h : Route R p xs q) :
    (∀ r ∈ p :: xs, P r) ∨ ∃ b prefix suffix,
      Route R p prefix b ∧ Route R b suffix q ∧ xs = prefix ++ suffix ∧ ¬ P b ∧
      (∀ r ∈ suffix, P r) ∧ (b :: suffix) <+ (p :: xs) := by
  classical
  induction h with
  | nil p =>
      by_cases hp : P p
      · exact Or.inl (by
          intro r hr
          have eq : r = p := by simpa only [List.mem_singleton] using hr
          exact eq.symm ▸ hp)
      · exact Or.inr ⟨p, [], [], .nil p, .nil p, rfl, hp,
          by intro r hr; cases hr, List.Sublist.refl _⟩
  | @cons p next q xs step tail ih =>
      rcases ih with all | ⟨b, prefix, suffix, first, last, eq, bad, rest, sub⟩
      · by_cases hp : P p
        · exact Or.inl (by
            intro r hr
            rcases List.mem_cons.mp hr with same | mem
            · exact same.symm ▸ hp
            · exact all r mem)
        · exact Or.inr ⟨p, [], next :: xs, .nil p, .cons step tail, rfl, hp, all, List.Sublist.refl _⟩
      · refine Or.inr ⟨b, next :: prefix, suffix, .cons step first, last, ?_, bad, rest, sub.cons p⟩
        simpa only [List.cons_append, eq]

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.AncestralShortcutGeometry

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget DiscriminatingStatus
open SourceSelection (AncestorOf)
open VertexActivePaths

universe u

def ParentConditioned {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (y : V)
    (p : Arrival V) : Prop := Z p.vertex ∧ Directed G p.vertex y

theorem conditioned_incoming_head {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    {p q r : Arrival V} {xs : List (Arrival V)} (incoming : RealStep G Z p q)
    (continuation : Route (RealStep G Z) q xs r) (nonempty : xs ≠ []) (conditioned : Z q.vertex) :
    q.incoming = some .head := by
  obtain ⟨left, received, edge, mark, _⟩ := incoming
  cases continuation with
  | nil => exact (nonempty rfl).elim
  | cons first tail =>
      obtain ⟨outgoing, nextIncoming, _, _, active⟩ := first
      have atQ : ActiveAt Z (AncestorOf G Z) q.vertex received outgoing := by simpa only [mark] using active
      have head := (ActiveWalkReduction.conditioned_active_heads conditioned atQ).1
      exact mark.trans (congrArg some head)

/-- Backward propagation along the actual prefix. If the next vertex is a
conditioned parent of y and the current vertex is adjacent to y, then the
current vertex is also a conditioned parent. The reverse-parent alternative
of the chord theorem is excluded by the directed-triangle head at y. -/
theorem parent_conditioned_predecessor {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x z : V)
    {a next q b y : Arrival V} {front back suffix : List (Arrival V)} {last : Option Mark}
    (hp : Route (RealStep G Z) ⟨x, none⟩ front a) (step : RealStep G Z a next)
    (hq : Route (RealStep G Z) next back q) (qb : RealStep G Z q b) (byStep : RealStep G Z b y)
    (ht : Route (RealStep G Z) y suffix ⟨z, last⟩)
    (minimal : Shortest G Z x z ((front ++ (next :: back) ++ [b, y] ++ suffix).map Arrival.vertex))
    (good : ParentConditioned G Z y.vertex next) (adjacent : Adjacent G a.vertex y.vertex) :
    ParentConditioned G Z y.vertex a := by
  have continuation := hq.append (.cons qb (.nil b))
  have nonempty : back ++ [b] ≠ [] := by
    intro eq
    have length := congrArg List.length eq
    simp only [List.length_append, List.length_cons, List.length_nil] at length
    omega
  have nextHead := conditioned_incoming_head G Z step continuation nonempty good.1
  have originalStep := step
  obtain ⟨left, received, edge, mark, _⟩ := step
  have receivedHead : received = .head := Option.some.inj (mark.symm.trans nextHead)
  subst received
  obtain ⟨outgoing, incoming, chord⟩ := adjacent
  have incomingHead := head_directed_triangle G laws edge good.2 chord
  have section : Route (RealStep G Z) a ((next :: back) ++ [b, y]) y :=
    (.cons originalStep hq).append (.cons qb (.cons byStep (.nil y)))
  have long : 1 < ((next :: back) ++ [b, y]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have shortest : Shortest G Z x z ((front ++ ((next :: back) ++ [b, y]) ++ suffix).map Arrival.vertex) := by
    simpa only [List.append_assoc] using minimal
  rcases shortest_chord_conditioned_parent G laws single Z x z hp section ht long chord shortest with forward | backward
  · exact forward
  · have reversed := laws.symmetric a.vertex y.vertex outgoing incoming chord
    have conflict := (single y.vertex a.vertex incoming outgoing .tail .head reversed backward.2).1
    have impossible : Mark.head = Mark.tail := incomingHead.symm.trans conflict
    exact (Mark.noConfusion impossible).elim

theorem conditioned_parent_route {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (y : V)
    {p q : Arrival V} {xs : List (Arrival V)} (h : Route (RealStep G Z) p xs q)
    (good : ∀ r ∈ p :: xs, ParentConditioned G Z y r) : Route (ColliderParentStep G y) p xs q := by
  revert good
  induction h with
  | nil p => intro _; exact .nil p
  | @cons p next q rest step tail ih =>
      intro good
      obtain ⟨outgoing, incoming, edge, mark, active⟩ := step
      refine .cons ⟨outgoing, incoming, edge, mark, ?_⟩ (ih ?_)
      · cases hp : p.incoming with
        | none => trivial
        | some previous =>
            have atP : ActiveAt Z (AncestorOf G Z) p.vertex previous outgoing := by
              simpa only [hp] using active
            obtain ⟨prevHead, outHead⟩ := ActiveWalkReduction.conditioned_active_heads (good p List.mem_cons_self).1 atP
            exact ⟨prevHead, outHead, (good p List.mem_cons_self).2⟩
      · intro r mem
        exact good r (List.mem_cons_of_mem _ mem)

/-- Oriented discriminating-section extraction. The shortest-path chord
lemma supplies either this left-parent case or its reversed counterpart.
The returned path has a nonempty collider-parent interior, the actual
terminal b, and an endpoint genuinely nonadjacent to y. -/
theorem extract_left_discriminating_section {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x z : V)
    {q b y : Arrival V} {prefix suffix : List (Arrival V)} {last : Option Mark}
    (hp : Route (RealStep G Z) ⟨x, none⟩ prefix q)
    (qb : RealStep G Z q b) (byStep : RealStep G Z b y)
    (ht : Route (RealStep G Z) y suffix ⟨z, last⟩)
    (minimal : Shortest G Z x z ((prefix ++ [b, y] ++ suffix).map Arrival.vertex))
    (notConditionedStart : ¬ Z x) (qGood : ParentConditioned G Z y.vertex q) :
    ∃ start nodes, Route (ColliderParentStep G y.vertex) ⟨start, none⟩ nodes b ∧
      (((⟨start, none⟩ :: nodes).map Arrival.vertex) ++ [y.vertex]).Nodup ∧
      ¬ Adjacent G start y.vertex ∧ 2 ≤ nodes.length := by
  classical
  rcases hp.last_failure_suffix (ParentConditioned G Z y.vertex) with all |
      ⟨stop, front, tail, first, lastRoute, decomposition, stopBad, allGood, sub⟩
  · exact (notConditionedStart (all ⟨x, none⟩ List.mem_cons_self).1).elim
  · have nonempty : tail ≠ [] := by
      intro eq
      subst tail
      cases lastRoute
      exact stopBad qGood
    cases lastRoute with
    | nil => exact (nonempty rfl).elim
    | @cons stop next q rest step back =>
        have nonadjacent : ¬ Adjacent G stop.vertex y.vertex := by
          intro adjacent
          apply stopBad
          apply parent_conditioned_predecessor G laws single Z x z first step back qb byStep ht
          · simpa only [decomposition, List.append_assoc] using minimal
          · exact allGood next List.mem_cons_self
          · exact adjacent
        have parentBack := conditioned_parent_route G Z y.vertex back allGood
        have parentLast : ColliderParentStep G y.vertex q b := by
          obtain ⟨outgoing, incoming, edge, mark, active⟩ := qb
          refine ⟨outgoing, incoming, edge, mark, ?_⟩
          cases hq : q.incoming with
          | none => trivial
          | some previous =>
              have atQ : ActiveAt Z (AncestorOf G Z) q.vertex previous outgoing := by
                simpa only [hq] using active
              obtain ⟨prevHead, outHead⟩ := ActiveWalkReduction.conditioned_active_heads qGood.1 atQ
              exact ⟨prevHead, outHead, qGood.2⟩
        obtain ⟨outgoing, incoming, edge, mark, _⟩ := step
        have parentPath : Route (ColliderParentStep G y.vertex) ⟨stop.vertex, none⟩
            ((next :: rest) ++ [b]) b :=
          .cons ⟨outgoing, incoming, edge, mark, trivial⟩
            (parentBack.append (.cons parentLast (.nil b)))
        have fullNodup : ((((⟨x, none⟩ :: prefix).map Arrival.vertex) ++ [b.vertex, y.vertex]) ++
            suffix.map Arrival.vertex).Nodup := by
          simpa only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.append_assoc] using
            minimal.1.2.1
        have shortSub := (sub.map Arrival.vertex).append (List.Sublist.refl [b.vertex, y.vertex])
        have addSuffix : (((⟨x, none⟩ :: prefix).map Arrival.vertex) ++ [b.vertex, y.vertex]) <+
            ((((⟨x, none⟩ :: prefix).map Arrival.vertex) ++ [b.vertex, y.vertex]) ++ suffix.map Arrival.vertex) := by
          simpa only [List.append_nil] using
            (List.Sublist.refl (((⟨x, none⟩ :: prefix).map Arrival.vertex) ++ [b.vertex, y.vertex])).append
              (List.nil_sublist (suffix.map Arrival.vertex))
        refine ⟨stop.vertex, (next :: rest) ++ [b], parentPath, ?_, nonadjacent, ?_⟩
        · simpa only [List.map_append, List.map_cons, List.map_nil, List.cons_append,
            List.append_assoc, List.singleton_append] using fullNodup.sublist (shortSub.trans addSuffix)
        · simp only [List.length_append, List.length_cons, List.length_nil]
          omega

end RestrictedCausal.AncestralShortcutGeometry
