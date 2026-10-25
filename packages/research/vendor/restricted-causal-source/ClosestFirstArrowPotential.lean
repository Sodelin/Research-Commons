import ClosestFirstArrowSplice

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Exact potential calculation for the only equal-length splice: replace the
original collider b by its first minimum-distance child d. Every other
physical vertex is retained, and the two neighboring collider statuses are
explicitly preserved. The potential drops by exactly one, not merely by an
informal appeal to a closer path. Classical attribution:
Ali--Richardson--Spirtes (2009), Definition 3.23 and Lemma 3.25.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing

universe u

theorem potential_initial_endpoint_change {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    (b d : V) («right» : List V)
    (stable : ∀ a c rest, «right» = a :: c :: rest →
      (Collider G b a c ↔ Collider G d a c)) :
    colliderPotential G Z (b :: «right») = colliderPotential G Z (d :: «right») := by
  classical
  cases «right» with
  | nil => rfl
  | cons a «right» =>
      cases «right» with
      | nil => rfl
      | cons c rest =>
          have same := propext (stable a c rest rfl)
          change (if Collider G b a c then directedDistance G Z a else 0) +
              colliderPotential G Z (a :: c :: rest) =
            (if Collider G d a c then directedDistance G Z a else 0) +
              colliderPotential G Z (a :: c :: rest)
          rw [same]

/-- The exact one-unit decrease on the literal old/new whole vertex lists.
No ancestry or status of an omitted vertex is hidden in the cost function:
there is precisely one substituted center in this equal-length case. -/
theorem potential_replace_collider {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    (b d : V) («left» «right» : List V)
    (distance : directedDistance G Z b = directedDistance G Z d + 1)
    (leftStable : ∀ front p a, «left» = front ++ [p, a] →
      (Collider G p a b ↔ Collider G p a d))
    (rightStable : ∀ c q rest, «right» = c :: q :: rest →
      (Collider G b c q ↔ Collider G d c q))
    (central : ∀ front a c rest, «left» = front ++ [a] → «right» = c :: rest →
      Collider G a b c ∧ Collider G a d c)
    (nonemptyLeft : «left» ≠ []) (nonemptyRight : «right» ≠ []) :
    colliderPotential G Z («left» ++ (b :: «right»)) =
      colliderPotential G Z («left» ++ (d :: «right»)) + 1 := by
  classical
  revert leftStable central nonemptyLeft
  induction «left» with
  | nil => intro _ _ «impossible»; exact («impossible» rfl).elim
  | cons p «left» ih =>
      intro leftStable central nonemptyLeft
      cases «left» with
      | nil =>
          cases «right» with
          | nil => exact (nonemptyRight rfl).elim
          | cons c rest =>
              obtain ⟨oldCollider, newCollider⟩ := central [] p c rest rfl rfl
              have tailEqual := potential_initial_endpoint_change G Z b d (c :: rest) rightStable
              change (if Collider G p b c then directedDistance G Z b else 0) +
                  colliderPotential G Z (b :: c :: rest) =
                ((if Collider G p d c then directedDistance G Z d else 0) +
                  colliderPotential G Z (d :: c :: rest)) + 1
              rw [if_pos oldCollider, if_pos newCollider, tailEqual, distance]
              omega
      | cons a «left» =>
          have tailResult := ih
            (by
              intro front q r equation
              exact leftStable (p :: front) q r (by simpa only [List.cons_append, equation]))
            (by
              intro front q c rest equation rightEquation
              exact central (p :: front) q c rest
                (by simpa only [List.cons_append, equation]) rightEquation)
            (by intro «impossible»; cases «impossible»)
          cases «left» with
          | nil =>
              have same := propext (leftStable [] p a rfl)
              change (if Collider G p a b then directedDistance G Z a else 0) +
                  colliderPotential G Z (a :: b :: «right») =
                ((if Collider G p a d then directedDistance G Z a else 0) +
                  colliderPotential G Z (a :: d :: «right»)) + 1
              rw [same]
              simp only [List.cons_append, List.nil_append] at tailResult
              omega
          | cons q remaining =>
              change (if Collider G p a q then directedDistance G Z a else 0) +
                  colliderPotential G Z ((a :: q :: remaining) ++ (b :: «right»)) =
                ((if Collider G p a q then directedDistance G Z a else 0) +
                  colliderPotential G Z ((a :: q :: remaining) ++ (d :: «right»))) + 1
              omega

theorem closest_rejects_equal_length_replacement {V : Type u} (G : MarkedGraph V)
    (Z : V → Prop) (x y b d : V) («left» «right» : List V) {old new : List V}
    (closest : Closest G Z x y old) (candidate : Path G Z x y new)
    (oldTrace : x :: old = «left» ++ (b :: «right»))
    (newTrace : x :: new = «left» ++ (d :: «right»))
    (distance : directedDistance G Z b = directedDistance G Z d + 1)
    (leftStable : ∀ front p a, «left» = front ++ [p, a] →
      (Collider G p a b ↔ Collider G p a d))
    (rightStable : ∀ c q rest, «right» = c :: q :: rest →
      (Collider G b c q ↔ Collider G d c q))
    (central : ∀ front a c rest, «left» = front ++ [a] → «right» = c :: rest →
      Collider G a b c ∧ Collider G a d c)
    (nonemptyLeft : «left» ≠ []) (nonemptyRight : «right» ≠ []) : False := by
  have oldLength := congrArg List.length oldTrace
  have newLength := congrArg List.length newTrace
  simp only [List.length_cons, List.length_append] at oldLength newLength
  have equalLength : new.length = old.length := by omega
  have bound := closest.2 new candidate equalLength
  rw [oldTrace, newTrace] at bound
  have strict := potential_replace_collider G Z b d «left» «right» distance leftStable rightStable
    central nonemptyLeft nonemptyRight
  omega

end RestrictedCausal.VertexActivePaths
