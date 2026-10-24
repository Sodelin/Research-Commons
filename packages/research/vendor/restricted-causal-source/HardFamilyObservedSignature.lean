import HardFamilyActivePaths

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

L2: exact actual observed separation signatures, including target-target
queries and every conditioning subset. The exceptional separator is
literally T union S. No arbitrary binary full-law query is admitted.
-/

namespace RestrictedCausal.HardFamily

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation ProbabilitySource

def exceptionalCondition {k u : Nat} (q : Index u) : Labels k u → Prop
  | .inl _ => True
  | .inr x => q.before x = true

def exceptionalSupport {k u : Nat} (q : Index u) : Labels k u → Prop
  | .inl _ => True
  | .inr x => q.before x = true ∨ x = q.first ∨ x = q.second

theorem exceptional_support_closed {k u : Nat} (q : Index u) :
    BackwardClosed (arrowGraph (arrow (k := k) (some q))) (exceptionalSupport q) := by
  intro parent child edge member
  have raw := (arrow_directed_exact _ _ _).mp edge
  cases child with
  | inl t => exact (target_has_no_parent (some q) t parent raw).elim
  | inr child =>
      cases parent with
      | inl t => trivial
      | inr parent =>
          change q.before child = true ∨ child = q.first ∨ child = q.second at member
          change insideArrow (some q) parent child at raw
          change q.before parent = true ∨ parent = q.first ∨ parent = q.second
          rcases member with before | atFirst | atSecond
          · exact Or.inl (q.predecessor_of_before parent child before raw.1)
          · subst child; exact Or.inl ((rival_parent_first q parent).mp raw)
          · subst child; exact Or.inl ((rival_parent_second q parent).mp raw)

theorem first_no_forward_into_support {k u : Nat} (q : Index u) (z : Labels k u)
    (member : exceptionalSupport q z) : ¬ arrow (some q) (.inr q.first) z := by
  intro edge
  cases z with
  | inl t => exact edge.elim
  | inr z =>
      change q.before z = true ∨ z = q.first ∨ z = q.second at member
      change insideArrow (some q) q.first z at edge
      rcases member with before | atFirst | atSecond
      · have «impossible» := q.predecessor_of_before q.first z before edge.1
        rw [q.before_first] at «impossible»
        cases «impossible»
      · subst z; exact Nat.lt_irrefl _ edge.1
      · subst z; exact edge.2 ⟨rfl, rfl⟩

theorem exceptional_pair_separated {k u : Nat} (q : Index u) :
    ¬ ActiveConnection (arrowGraph (arrow (k := k) (some q))) (exceptionalCondition q)
      (.inr q.first) (.inr q.second) := by
  apply separated_by_conditioned_first_tails _ (raw_arrow_mixed_laws _ (arrow_acyclic (some q)))
    (exceptionalCondition q) (exceptionalSupport q) (exceptional_support_closed q)
  · intro z conditioned
    cases z with
    | inl t => trivial
    | inr z => exact Or.inl conditioned
  · intro same; exact q.distinct (Sum.inr.inj same)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · change ¬ q.before q.second = true
    rw [q.before_second]
    decide
  · intro z ma mb edge member
    rcases edge with ⟨forward, _, _⟩ | ⟨backward, _, atTail⟩
    · exact (first_no_forward_into_support q z member forward).elim
    · refine ⟨?_, atTail⟩
      cases z with
      | inl t => trivial
      | inr z => exact (rival_parent_first q z).mp backward

/-- The unique separator is derived in both directions, including every
target root, every S member, every R member, and both excluded endpoints. -/
theorem exceptional_pair_separated_iff {k u : Nat} (q : Index u) (C : Labels k u → Prop)
    (firstOutside : ¬ C (.inr q.first)) (secondOutside : ¬ C (.inr q.second)) :
    (¬ ActiveConnection (arrowGraph (arrow (some q))) C (.inr q.first) (.inr q.second)) ↔
      ∀ z, C z ↔ exceptionalCondition q z := by
  constructor
  · intro separated
    have different : (Sum.inr q.first : Labels k u) ≠ .inr q.second :=
      fun same => q.distinct (Sum.inr.inj same)
    have targetConditioned (t : Fin k) : C (.inl t) := by
      by_contra outside
      exact separated (raw_fork_active _ (arrow_acyclic (some q)) C _ _ (.inl t) different
        (targets_cause_all (some q) t q.first) (targets_cause_all (some q) t q.second) outside)
    have beforeConditioned (z : Fin u) (before : q.before z = true) : C (.inr z) := by
      by_contra outside
      exact separated (raw_fork_active _ (arrow_acyclic (some q)) C _ _ (.inr z) different
        ((rival_parent_first q z).mpr before) ((rival_parent_second q z).mpr before) outside)
    have remainderOutside (z : Fin u) (notBefore : ¬ q.before z = true)
        (notFirst : z ≠ q.first) (notSecond : z ≠ q.second) : ¬ C (.inr z) := by
      intro conditioned
      have edges := rival_endpoints_to_remainder (k := k) q z notBefore notFirst notSecond
      exact separated (raw_conditioned_collider_active _ (arrow_acyclic (some q)) C _ _ (.inr z)
        different edges.1 edges.2 conditioned)
    intro z
    cases z with
    | inl t => exact ⟨fun _ => True.intro, fun _ => targetConditioned t⟩
    | inr z =>
        change C (.inr z) ↔ q.before z = true
        by_cases before : q.before z = true
        · exact ⟨fun _ => before, fun _ => beforeConditioned z before⟩
        · by_cases atFirst : z = q.first
          · subst z
            exact ⟨fun h => (firstOutside h).elim, fun h => (before h).elim⟩
          · by_cases atSecond : z = q.second
            · subst z
              exact ⟨fun h => (secondOutside h).elim, fun h => (before h).elim⟩
            · exact ⟨fun h => (remainderOutside z before atFirst atSecond h).elim,
                fun h => (before h).elim⟩
  · intro same
    have equality : C = exceptionalCondition q := funext (fun z => propext (same z))
    rw [equality]
    exact exceptional_pair_separated q

theorem roots_separated_iff {k u : Nat} (source : Option (Index u))
    (C : Labels k u → Prop) (t s : Fin k) (different : t ≠ s) :
    (¬ ActiveConnection (arrowGraph (arrow source)) C (.inl t) (.inl s)) ↔
      ∀ z : Fin u, ¬ C (.inr z) := by
  constructor
  · intro separated z selected
    exact separated (raw_conditioned_collider_active _ (arrow_acyclic source) C _ _ (.inr z)
      (fun same => different (Sum.inl.inj same))
      (targets_cause_all source t z) (targets_cause_all source s z) selected)
  · intro noUntargeted
    have closed : BackwardClosed (arrowGraph (arrow source)) Available := by
      intro a b edge member
      cases b with
      | inl root => exact (target_has_no_parent source root a
          ((arrow_directed_exact _ _ _).mp edge)).elim
      | inr z => exact member.elim
    apply separated_by_no_first_neighbor _ (raw_arrow_mixed_laws _ (arrow_acyclic source))
      C Available closed
    · intro v conditioned
      cases v with
      | inl t => trivial
      | inr z => exact (noUntargeted z conditioned).elim
    · intro same; exact different (Sum.inl.inj same)
    · trivial
    · trivial
    · intro v ma mb edge available
      cases v with
      | inr z => exact available.elim
      | inl root =>
          rcases edge with ⟨«impossible», _, _⟩ | ⟨«impossible», _, _⟩ <;> exact «impossible».elim

theorem root_untargeted_active {k u : Nat} (source : Option (Index u))
    (C : Labels k u → Prop) (t : Fin k) (x : Fin u) :
    ActiveConnection (arrowGraph (arrow source)) C (.inl t) (.inr x) :=
  single_edge_active _ C (by intro «impossible»; cases «impossible») .tail .head
    (Or.inl ⟨targets_cause_all source t x, rfl, rfl⟩)

theorem untargeted_adjacent_active {k u : Nat} (source : Option (Index u))
    (C : Labels k u → Prop) (x y : Fin u) (different : x ≠ y)
    (notMissing : ∀ q, source = some q →
      ¬ (x = q.first ∧ y = q.second) ∧ ¬ (y = q.first ∧ x = q.second)) :
    ActiveConnection (arrowGraph (arrow source)) C (.inr x) (.inr y) := by
  have ne : (Sum.inr x : Labels k u) ≠ .inr y := fun h => different (Sum.inr.inj h)
  rcases inside_adjacent_except source x y different notMissing with forward | backward
  · exact single_edge_active _ C ne .tail .head (Or.inl ⟨forward, rfl, rfl⟩)
  · exact single_edge_active _ C ne .head .tail (Or.inr ⟨backward, rfl, rfl⟩)

theorem baseline_untargeted_active {k u : Nat} (C : Labels k u → Prop)
    (x y : Fin u) (different : x ≠ y) :
    ActiveConnection (arrowGraph (arrow none)) C (.inr x) (.inr y) :=
  untargeted_adjacent_active none C x y different (fun _ «impossible» => by cases «impossible»)

end RestrictedCausal.HardFamily
