import OriginalWeakConnection


/- Pinned-context spelling variant: explicit original List.Sublist relation.
All proof scripts outside these annotation spellings, source predicates and
conclusion semantics are unchanged; frozen original retained separately. -/
/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Delete conditioned joins that would cease to be colliders after replacing
raw inducing incidences by literal MAG marks. The recursion is on the actual
finite observed-route length. It preserves both indexed endpoint arrivals,
physical simplicity and a literal observed-state sublist.
-/

namespace RestrictedCausal.WeakInducing

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget ActiveWalkReduction

universe u v w

def GoodJoin {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (a b c : Arrival X) : Prop :=
  Z b.vertex → ¬ TailFlag D b.vertex a.vertex ∧ ¬ TailFlag D b.vertex c.vertex

def AllTriples {V : Type u} (P : V → V → V → Prop) : List V → Prop
  | a :: b :: c :: xs => P a b c ∧ AllTriples P (b :: c :: xs)
  | _ => True

theorem bad_join_flag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) {a b c : Arrival X}
    (h : ¬ GoodJoin D Z a b c) :
    Z b.vertex ∧ (TailFlag D b.vertex a.vertex ∨ TailFlag D b.vertex c.vertex) := by
  classical
  by_cases hb : Z b.vertex
  · refine ⟨hb, ?_⟩
    by_cases «left» : TailFlag D b.vertex a.vertex
    · exact Or.inl «left»
    · by_cases «right» : TailFlag D b.vertex c.vertex
      · exact Or.inr «right»
      · exact (h (fun _ => ⟨«left», «right»⟩)).elim
  · exact (h (fun hz => (hb hz).elim)).elim

theorem merge_bad_steps {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) {a b c : Arrival X}
    (hne : a.vertex ≠ c.vertex)
    («first» : Transition (graph D) Z (Activated D Z) a b)
    (last : Transition (graph D) Z (Activated D Z) b c)
    (bad : ¬ GoodJoin D Z a b c) : Transition (graph D) Z (Activated D Z) a c := by
  obtain ⟨conditioned, flag⟩ := bad_join_flag D Z bad
  obtain ⟨«left», middleIn, firstEdge, middleMark, firstActive⟩ := «first»
  obtain ⟨middleOut, «right», lastEdge, lastMark, lastActive⟩ := last
  have atMiddle : ActiveAt Z (Activated D Z) b.vertex middleIn middleOut := by
    simpa only [middleMark] using lastActive
  obtain ⟨inHead, outHead⟩ := conditioned_active_heads conditioned atMiddle
  subst middleIn
  subst middleOut
  exact ⟨«left», «right», merge_collider_edges D hne firstEdge lastEdge flag, lastMark, firstActive⟩

theorem normalize_aux {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (n : Nat) :
    ∀ (p : Arrival X) (xs : List (Arrival X)) (q : Arrival X), xs.length = n →
      Route (Transition (graph D) Z (Activated D Z)) p xs q →
      ((p :: xs).map Arrival.vertex).Nodup →
      ∃ ys, Route (Transition (graph D) Z (Activated D Z)) p ys q ∧
        ((p :: ys).map Arrival.vertex).Nodup ∧ AllTriples (GoodJoin D Z) (p :: ys) ∧
        List.Sublist (p :: ys) (p :: xs) := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro p xs q length route nodup
      cases route with
      | nil p => exact ⟨[], .nil p, nodup, trivial, List.Sublist.refl _⟩
      | @cons p b q rest «first» tail =>
          have shorter : rest.length < n := by
            simp only [List.length_cons] at length
            omega
          obtain ⟨ys, normalizedTail, tailNodup, tailGood, tailSub⟩ :=
            ih rest.length shorter b rest q rfl tail (List.nodup_cons.mp nodup).2
          have newSub : List.Sublist (p :: b :: ys) (p :: b :: rest) := tailSub.cons_cons p
          have newNodup : ((p :: b :: ys).map Arrival.vertex).Nodup :=
            nodup.sublist (newSub.map Arrival.vertex)
          cases ys with
          | nil => exact ⟨[b], .cons «first» normalizedTail, newNodup, trivial, newSub⟩
          | cons c zs =>
              cases normalizedTail with
              | cons second suffix =>
                  by_cases good : GoodJoin D Z p b c
                  · exact ⟨b :: c :: zs, .cons «first» (.cons second suffix),
                      newNodup, ⟨good, tailGood⟩, newSub⟩
                  · have endpointsDistinct : p.vertex ≠ c.vertex := by
                      intro eq
                      have notMem := (List.nodup_cons.mp newNodup).1
                      apply notMem
                      simp only [List.map_cons, List.mem_cons, List.mem_map]
                      exact Or.inr (Or.inl eq)
                    have merged := merge_bad_steps D Z endpointsDistinct «first» second good
                    have removeMiddle : List.Sublist (p :: c :: zs) (p :: b :: c :: zs) :=
                      ((List.Sublist.refl (c :: zs)).cons b).cons_cons p
                    have shortNodup := newNodup.sublist (removeMiddle.map Arrival.vertex)
                    have tailLength : (c :: zs).length ≤ rest.length :=
                      (List.Sublist.of_cons_cons tailSub).length_le
                    have strictlyShorter : (c :: zs).length < n := by
                      simp only [List.length_cons] at length
                      omega
                    obtain ⟨result, resultRoute, resultNodup, resultGood, resultSub⟩ :=
                      ih (c :: zs).length strictlyShorter p (c :: zs) q rfl
                        (.cons merged suffix) shortNodup
                    exact ⟨result, resultRoute, resultNodup, resultGood,
                      resultSub.trans (removeMiddle.trans newSub)⟩

/-- The endpoint arrival marks are unchanged, unlike unconstrained physical
loop erasure. Every remaining conditioned internal vertex has two MAG heads. -/
theorem normalize_weak_route {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop)
    {p q : Arrival X} {xs : List (Arrival X)}
    (route : Route (Transition (graph D) Z (Activated D Z)) p xs q)
    (nodup : ((p :: xs).map Arrival.vertex).Nodup) :
    ∃ ys, Route (Transition (graph D) Z (Activated D Z)) p ys q ∧
      ((p :: ys).map Arrival.vertex).Nodup ∧ AllTriples (GoodJoin D Z) (p :: ys) ∧
      List.Sublist (p :: ys) (p :: xs) := normalize_aux D Z xs.length p xs q rfl route nodup

end RestrictedCausal.WeakInducing
