import BinaryPathConstraintPropagation

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Incidences are actual consecutive occurrences in one simple original
vertex trace. This develops the uniqueness needed to assign fair/copy/XOR
gates, without adding an assumed component decomposition or a new graph.
-/

namespace RestrictedCausal.ProbabilitySource

open SelectedWalk WeakInducing VertexActivePaths CanonicalSelection LatentRoots
open OriginalProjection DiscriminatingStatus

universe u

inductive NextOn {V : Type u} : List V → V → V → Prop
  | here (a b : V) (rest : List V) : NextOn (a :: b :: rest) a b
  | there (head : V) {rest : List V} {a b : V} :
      NextOn rest a b → NextOn (head :: rest) a b

inductive TripleOn {V : Type u} : List V → V → V → V → Prop
  | here (a b c : V) (rest : List V) : TripleOn (a :: b :: c :: rest) a b c
  | there (head : V) {rest : List V} {a b c : V} :
      TripleOn rest a b c → TripleOn (head :: rest) a b c

namespace NextOn

theorem members {V : Type u} {vertices : List V} {a b : V}
    (h : NextOn vertices a b) : a ∈ vertices ∧ b ∈ vertices := by
  induction h with
  | here a b rest => simp
  | there head h ih => exact ⟨List.mem_cons_of_mem _ ih.1, List.mem_cons_of_mem _ ih.2⟩

theorem second_in_tail {V : Type u} {head a b : V} {rest : List V}
    (h : NextOn (head :: rest) a b) : b ∈ rest := by
  cases h with
  | here => exact List.mem_cons_self
  | there _ h => exact h.members.2

theorem preceding_of_mem {V : Type u} (head vertex : V) (rest : List V)
    (member : vertex ∈ rest) : ∃ parent, NextOn (head :: rest) parent vertex := by
  revert head member
  induction rest with
  | nil => intro head member; cases member
  | cons «next» rest ih =>
      intro head member
      rcases List.mem_cons.mp member with same | later
      · subst vertex; exact ⟨head, .here _ _ _⟩
      · obtain ⟨parent, occurrence⟩ := ih «next» later
        exact ⟨parent, .there head occurrence⟩

theorem no_into_head {V : Type u} {head a : V} {rest : List V}
    (simple : (head :: rest).Nodup) : ¬ NextOn (head :: rest) a head := by
  intro h
  cases h with
  | here => exact (List.nodup_cons.mp simple).1 List.mem_cons_self
  | there _ h => exact (List.nodup_cons.mp simple).1 h.members.2

theorem from_head {V : Type u} {head «next» b : V} {rest : List V}
    (simple : (head :: «next» :: rest).Nodup)
    (h : NextOn (head :: «next» :: rest) head b) : b = «next» := by
  cases h with
  | here => rfl
  | there _ h => exact ((List.nodup_cons.mp simple).1 h.members.1).elim

theorem unique_right {V : Type u} {vertices : List V} {a b c : V}
    («first» : NextOn vertices a b) (simple : vertices.Nodup) (second : NextOn vertices a c) : b = c := by
  revert simple second
  induction «first» with
  | here a b rest => intro simple second; exact (from_head simple second).symm
  | @there head rest a b «first» ih =>
      intro simple second
      cases second with
      | here => exact ((List.nodup_cons.mp simple).1 «first».members.1).elim
      | there _ second => exact ih (List.nodup_cons.mp simple).2 second

theorem unique_left {V : Type u} {vertices : List V} {a b c : V}
    («first» : NextOn vertices a b) (simple : vertices.Nodup) (second : NextOn vertices c b) : a = c := by
  revert simple second
  induction «first» with
  | here a b rest =>
      intro simple second
      cases second with
      | here => rfl
      | there _ second => exact (no_into_head (List.nodup_cons.mp simple).2 second).elim
  | @there head rest a b «first» ih =>
      intro simple second
      cases second with
      | here => exact (no_into_head (List.nodup_cons.mp simple).2 «first»).elim
      | there _ second => exact ih (List.nodup_cons.mp simple).2 second

theorem distinct {V : Type u} {vertices : List V} {a b : V}
    (simple : vertices.Nodup) (h : NextOn vertices a b) : a ≠ b := by
  revert simple
  induction h with
  | here a b rest =>
      intro simple
      intro same
      subst b
      exact (List.nodup_cons.mp simple).1 List.mem_cons_self
  | there head h ih => intro simple; exact ih (List.nodup_cons.mp simple).2

theorem not_from_last {V : Type u} (front : List V) (last «next» : V)
    (simple : (front ++ [last]).Nodup) : ¬ NextOn (front ++ [last]) last «next» := by
  revert simple
  induction front with
  | nil => intro _ h; cases h with | there _ h => cases h
  | cons head front ih =>
      intro simple
      intro h
      have lastTail : last ∈ front ++ [last] := by simp
      have tailSimple := (List.nodup_cons.mp simple).2
      cases front with
      | nil =>
          cases h with
          | here => exact (List.nodup_cons.mp simple).1 lastTail
          | there _ h => exact ih tailSimple h
      | cons a rest =>
          cases h with
          | here => exact (List.nodup_cons.mp simple).1 lastTail
          | there _ h => exact ih tailSimple h

end NextOn

theorem route_next_edge {V : Type u} {D : V → V → Prop}
    {start finish : V} {vertices : List V} (route : Route D start vertices finish) :
    ∀ a b, NextOn (start :: vertices) a b → D a b := by
  induction route with
  | nil start => intro a b h; cases h with | there _ h => cases h
  | @cons start «next» finish rest edge tail ih =>
      intro a b h
      cases h with
      | here => exact edge
      | there _ h => exact ih a b h

theorem route_terminal_trace {V : Type u} {D : V → V → Prop}
    {start finish : V} {vertices : List V} (route : Route D start vertices finish) :
    ∃ front, start :: vertices = front ++ [finish] := by
  induction route with
  | nil start => exact ⟨[], rfl⟩
  | @cons start «next» finish rest edge tail ih =>
      obtain ⟨front, equation⟩ := ih
      exact ⟨start :: front, by simpa only [List.cons_append, equation]⟩

namespace TripleOn

theorem «left» {V : Type u} {vertices : List V} {a b c : V}
    (h : TripleOn vertices a b c) : NextOn vertices a b := by
  induction h with
  | here a b c rest => exact .here _ _ _
  | there head h ih => exact .there head ih

theorem «right» {V : Type u} {vertices : List V} {a b c : V}
    (h : TripleOn vertices a b c) : NextOn vertices b c := by
  induction h with
  | here a b c rest => exact .there a (.here _ _ _)
  | there head h ih => exact .there head ih

theorem literal {V : Type u} {vertices : List V} {a b c : V}
    (h : TripleOn vertices a b c) : ∃ front rest, vertices = front ++ a :: b :: c :: rest := by
  induction h with
  | here a b c rest => exact ⟨[], rest, rfl⟩
  | there head h ih =>
      obtain ⟨front, rest, equation⟩ := ih
      exact ⟨head :: front, rest, by simp only [List.cons_append, equation]⟩

theorem of_literal {V : Type u} (front rest : List V) (a b c : V) :
    TripleOn (front ++ a :: b :: c :: rest) a b c := by
  induction front with
  | nil => exact .here _ _ _ _
  | cons head front ih => exact .there head ih

theorem property {V : Type u} {P : V → V → V → Prop} {vertices : List V} {a b c : V}
    (h : TripleOn vertices a b c) (all : AllTriples P vertices) : P a b c := by
  revert all
  induction h with
  | here a b c rest => intro all; exact all.1
  | there head h ih => intro all; exact ih (allTriples_tail P head _ all)

end TripleOn

theorem route_member_position {V : Type u} {D : V → V → Prop}
    {start finish : V} {vertices : List V} (route : Route D start vertices finish) :
    ∀ vertex ∈ start :: vertices,
      vertex = start ∨ vertex = finish ∨ ∃ a c, TripleOn (start :: vertices) a vertex c := by
  induction route with
  | nil start =>
      intro vertex member
      exact Or.inl (by simpa only [List.mem_singleton] using member)
  | @cons start «next» finish rest edge tail ih =>
      intro vertex member
      rcases List.mem_cons.mp member with same | member
      · exact Or.inl same
      · rcases ih vertex member with atNext | atFinish | interior
        · subst vertex
          cases tail with
          | nil => exact Or.inr (Or.inl rfl)
          | cons last suffix => exact Or.inr (Or.inr ⟨start, _, .here _ _ _ _⟩)
        · exact Or.inr (Or.inl atFinish)
        · obtain ⟨a, c, occurrence⟩ := interior
          exact Or.inr (Or.inr ⟨a, c, .there start occurrence⟩)

theorem triple_of_next {V : Type u} {vertices : List V} {a b c : V}
    (simple : vertices.Nodup) («left» : NextOn vertices a b) («right» : NextOn vertices b c) :
    TripleOn vertices a b c := by
  revert simple «right»
  induction «left» with
  | here a b rest =>
      intro simple «right»
      cases rest with
      | nil =>
          cases «right» with
          | here => exact ((List.nodup_cons.mp simple).1 List.mem_cons_self).elim
          | there _ «right» => cases «right» with | there _ «right» => cases «right»
      | cons «next» rest =>
          cases «right» with
          | here => exact ((List.nodup_cons.mp simple).1 List.mem_cons_self).elim
          | there _ «right» =>
              have same := NextOn.from_head (List.nodup_cons.mp simple).2 «right»
              subst c
              exact .here _ _ _ _
  | @there head rest a b «left» ih =>
      intro simple «right»
      cases «right» with
      | here => exact ((List.nodup_cons.mp simple).1 «left».members.2).elim
      | there _ «right» => exact .there head (ih (List.nodup_cons.mp simple).2 «right»)

theorem allPairs_of_next {V : Type u} (P : V → V → Prop) (vertices : List V)
    (each : ∀ a b, NextOn vertices a b → P a b) : AllPairs P vertices := by
  revert each
  induction vertices with
  | nil => intro _; trivial
  | cons a rest ih =>
      intro each
      cases rest with
      | nil => trivial
      | cons b rest => exact ⟨each a b (.here _ _ _), ih (fun p q h => each p q (.there a h))⟩

theorem allTriples_of_triple {V : Type u} (P : V → V → V → Prop) (vertices : List V)
    (each : ∀ a b c, TripleOn vertices a b c → P a b c) : AllTriples P vertices := by
  revert each
  induction vertices with
  | nil => intro _; trivial
  | cons a rest ih =>
      intro each
      cases rest with
      | nil => trivial
      | cons b rest =>
          cases rest with
          | nil => trivial
          | cons c rest => exact ⟨each a b c (.here _ _ _ _),
              ih (fun p q r h => each p q r (.there a h))⟩

def TraceCollider {V : Type u} (D : V → V → Prop) (vertices : List V) (b : V) : Prop :=
  ∃ a c, TripleOn vertices a b c ∧ D a b ∧ D c b

def MainParent {V : Type u} (D : V → V → Prop) (vertices : List V) (parent child : V) : Prop :=
  (NextOn vertices parent child ∨ NextOn vertices child parent) ∧ D parent child

def TrekRoot {V : Type u} (D : V → V → Prop) (vertices : List V) (vertex : V) : Prop :=
  vertex ∈ vertices ∧ ¬ TraceCollider D vertices vertex ∧ ¬ ∃ parent, MainParent D vertices parent vertex

theorem arrow_collider_arrows {V : Type u} (D : V → V → Prop) {a b c : V}
    (collider : Collider (arrowGraph D) a b c) : D a b ∧ D c b := by
  obtain ⟨ma, mc, «left», «right»⟩ := collider
  constructor
  · rcases «left» with ⟨edge, _, _⟩ | ⟨_, _, «impossible»⟩
    · exact edge
    · exact Mark.noConfusion «impossible»
  · rcases «right» with ⟨_, «impossible», _⟩ | ⟨edge, _, _⟩
    · exact Mark.noConfusion «impossible»
    · exact edge

theorem trace_collider_original {V : Type u} (D : V → V → Prop)
    {vertices : List V} {a b c : V} (simple : vertices.Nodup)
    (triple : TripleOn vertices a b c) (collider : TraceCollider D vertices b) :
    D a b ∧ D c b := by
  obtain ⟨p, q, occurrence, «left», «right»⟩ := collider
  have sameA := triple.left.unique_left simple occurrence.left
  have sameC := triple.right.unique_right simple occurrence.right
  exact ⟨sameA.symm ▸ «left», sameC.symm ▸ «right»⟩

theorem mainParent_unique {V : Type u} (D : V → V → Prop)
    {vertices : List V} {vertex a b : V} (simple : vertices.Nodup)
    (ordinary : ¬ TraceCollider D vertices vertex)
    («first» : MainParent D vertices a vertex) (second : MainParent D vertices b vertex) : a = b := by
  rcases «first» with ⟨beforeA | afterA, edgeA⟩ <;>
    rcases second with ⟨beforeB | afterB, edgeB⟩
  · exact beforeA.unique_left simple beforeB
  · exact (ordinary ⟨a, b, triple_of_next simple beforeA afterB, edgeA, edgeB⟩).elim
  · exact (ordinary ⟨b, a, triple_of_next simple beforeB afterA, edgeB, edgeA⟩).elim
  · exact afterA.unique_right simple afterB

theorem collider_incident_incoming {V : Type u} (D : V → V → Prop)
    {vertices : List V} {b v : V} (simple : vertices.Nodup)
    (collider : TraceCollider D vertices b)
    (beside : NextOn vertices v b ∨ NextOn vertices b v) : D v b := by
  obtain ⟨a, c, triple, «left», «right»⟩ := collider
  rcases beside with before | after
  · have same := before.unique_left simple triple.left
    exact same.symm ▸ «left»
  · have same := after.unique_right simple triple.right
    exact same.symm ▸ «right»

theorem mainParent_ordinary {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = [])
    {vertices : List V} {parent child : V} (simple : vertices.Nodup)
    (edge : MainParent D vertices parent child) : ¬ TraceCollider D vertices parent := by
  intro collider
  have reverse := collider_incident_incoming D simple collider edge.1.symm
  have empty := acyclic parent [child, parent] (.cons edge.2 (.cons reverse (.nil parent)))
  cases empty

theorem mainParent_member {V : Type u} (D : V → V → Prop)
    {vertices : List V} {parent child : V} (edge : MainParent D vertices parent child) : parent ∈ vertices := by
  rcases edge.1 with before | after
  · exact before.members.1
  · exact after.members.2

theorem trace_collider_isolated {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = [])
    {vertices : List V} {a b : V} (simple : vertices.Nodup) («next» : NextOn vertices a b) :
    ¬ (TraceCollider D vertices a ∧ TraceCollider D vertices b) := by
  intro both
  have intoA := collider_incident_incoming D simple both.1 (Or.inr «next»)
  have intoB := collider_incident_incoming D simple both.2 (Or.inl «next»)
  have empty := acyclic a [b, a] (.cons intoB (.cons intoA (.nil a)))
  cases empty

theorem trace_first_not_collider {V : Type u} (D : V → V → Prop)
    (head : V) (rest : List V) (simple : (head :: rest).Nodup) :
    ¬ TraceCollider D (head :: rest) head := by
  rintro ⟨a, c, triple, _, _⟩
  exact NextOn.no_into_head simple triple.left

theorem trace_last_not_collider {V : Type u} (D : V → V → Prop)
    (front : List V) (last : V) (simple : (front ++ [last]).Nodup) :
    ¬ TraceCollider D (front ++ [last]) last := by
  rintro ⟨a, c, triple, _, _⟩
  exact NextOn.not_from_last front last c simple triple.right

def OrderedCenters {V : Type u} (vertices : List V) (b e : V) : Prop :=
  ∃ «left» a middle d c «right», vertices = «left» ++ a :: b :: (middle ++ d :: e :: c :: «right»)

/-- Distinct nonadjacent interior centers have one literal order. The
gap is allowed to be empty, corresponding to exactly one ordinary vertex
between the two colliders. -/
theorem triple_centers_ordered {V : Type u} {vertices : List V} {a b c d e f : V}
    («first» : TripleOn vertices a b c) (second : TripleOn vertices d e f)
    (distinct : b ≠ e) (notNext : ¬ NextOn vertices b e) (notPrev : ¬ NextOn vertices e b) :
    OrderedCenters vertices b e ∨ OrderedCenters vertices e b := by
  induction vertices generalizing a b c d e f with
  | nil => cases «first»
  | cons head rest ih =>
      cases «first» with
      | here a b c tail =>
          cases second with
          | here => exact (distinct rfl).elim
          | there _ second =>
              cases second with
              | here => exact (notNext (.there head (.here _ _ _))).elim
              | there _ second =>
                  obtain ⟨middle, «right», equation⟩ := second.literal
                  exact Or.inl ⟨[], head, middle, d, f, «right», by
                    simpa only [List.nil_append, equation]⟩
      | there head «first» =>
          cases second with
          | here d e f tail =>
              cases «first» with
              | here => exact (notPrev (.there head (.here _ _ _))).elim
              | there _ «first» =>
                  obtain ⟨middle, «right», equation⟩ := «first».literal
                  exact Or.inr ⟨[], head, middle, a, c, «right», by
                    simpa only [List.nil_append, equation]⟩
          | there _ second =>
              rcases ih «first» second distinct (fun h => notNext (.there head h))
                (fun h => notPrev (.there head h)) with ordered | ordered
              · obtain ⟨«left», a, middle, d, c, «right», equation⟩ := ordered
                exact Or.inl ⟨head :: «left», a, middle, d, c, «right», by
                  simpa only [List.cons_append, equation]⟩
              · obtain ⟨«left», a, middle, d, c, «right», equation⟩ := ordered
                exact Or.inr ⟨head :: «left», a, middle, d, c, «right», by
                  simpa only [List.cons_append, equation]⟩

theorem trace_colliders_ordered {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = [])
    {vertices : List V} {b e : V} (simple : vertices.Nodup)
    («first» : TraceCollider D vertices b) (second : TraceCollider D vertices e) (distinct : b ≠ e) :
    OrderedCenters vertices b e ∨ OrderedCenters vertices e b := by
  obtain ⟨a, c, firstTriple, firstLeft, firstRight⟩ := «first»
  obtain ⟨d, f, secondTriple, secondLeft, secondRight⟩ := second
  have «first» : TraceCollider D vertices b := ⟨a, c, firstTriple, firstLeft, firstRight⟩
  have second : TraceCollider D vertices e := ⟨d, f, secondTriple, secondLeft, secondRight⟩
  exact triple_centers_ordered firstTriple secondTriple distinct
    (fun h => trace_collider_isolated D acyclic simple h ⟨«first», second⟩)
    (fun h => trace_collider_isolated D acyclic simple h ⟨second, «first»⟩)

end RestrictedCausal.ProbabilitySource
