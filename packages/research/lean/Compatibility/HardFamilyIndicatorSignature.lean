import HardFamilyObservedSignature

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

L3: every separate named indicator, every observed endpoint, and every
legal conditioning predicate. The complete truth table is independent
of the U order and missing edge. No joint-indicator or numerical full-law
query is introduced. The actual source label/physical realization join
is a subsequent obligation, not silently assumed here.
-/

namespace RestrictedCausal.HardFamily

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation ProbabilitySource VertexActivePaths DiscriminatingStatus

def augmented {k u : Nat} (source : Option (Index u)) (t : Fin k) :=
  AddIndicator (arrow source) (Sum.inl t : Labels k u)

def augmentedCondition {k u : Nat} (C : Labels k u → Prop) : Option (Labels k u) → Prop
  | none => False
  | some v => C v

theorem augmented_acyclic {k u : Nat} (source : Option (Index u)) (t : Fin k) :
    ∀ a xs, Route (augmented source t) a xs a → xs = [] :=
  add_indicator_acyclic (arrow source) (.inl t) (arrow_acyclic source)

theorem indicator_neighbor {k u : Nat} (source : Option (Index u)) (t : Fin k)
    (v : Option (Labels k u))
    (adjacent : Adjacent (arrowGraph (augmented source t)) none v) : v = some (.inl t) := by
  rcases arrow_adjacent_directions _ adjacent with forward | backward
  · exact (indicator_sole_child (arrow source) (.inl t) v).mp forward
  · exact (indicator_no_parent (arrow source) (.inl t) v backward).elim

theorem only_indicator_enters_target {k u : Nat} (source : Option (Index u)) (t : Fin k)
    (v : Option (Labels k u)) (edge : augmented source t v (some (.inl t))) : v = none := by
  cases v with
  | none => rfl
  | some v => exact (target_has_no_parent source t v edge).elim

/-- Conditioning the targeted root blocks every nontrivial indicator path.
The only apparent collider escape would return to the initial indicator,
which is excluded by the ACTUAL path's vertex simplicity. -/
theorem conditioned_target_blocks {k u : Nat} (source : Option (Index u)) (t : Fin k)
    (C : Labels k u → Prop) (x : Labels k u) (outside : ¬ C x) (conditioned : C (.inl t)) :
    ¬ ActiveConnection (arrowGraph (augmented source t)) (augmentedCondition C) none (some x) := by
  intro connection
  obtain ⟨vertices, route, simple, good⟩ := active_connection_vertex_path _
    (arrow_single_edges _ (augmented_acyclic source t)) _ none (some x) connection
  cases route with
  | @cons start «next» finish rest «first» tail =>
      have nextEq := indicator_neighbor source t «next» «first»
      subst «next»
      cases tail with
      | nil => exact outside conditioned
      | @cons «next» after finish remaining second tail =>
          have afterNotIndicator : after ≠ none := by
            intro same
            exact (List.nodup_cons.mp simple).1
              (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl same.symm)))
          have notCollider : ¬ Collider (arrowGraph (augmented source t)) none (some (.inl t)) after := by
            intro collider
            have arrows := arrow_collider_arrows _ collider
            exact afterNotIndicator (only_indicator_enters_target source t after arrows.2)
          exact (good.1.2 notCollider) conditioned

theorem indicator_target_active {k u : Nat} (source : Option (Index u)) (t : Fin k)
    (C : Labels k u → Prop) :
    ActiveConnection (arrowGraph (augmented source t)) (augmentedCondition C) none (some (.inl t)) :=
  single_edge_active _ _ (by intro «impossible»; cases «impossible») .tail .head
    (Or.inl ⟨rfl, rfl, rfl⟩)

theorem indicator_untargeted_active {k u : Nat} (source : Option (Index u)) (t : Fin k)
    (C : Labels k u → Prop) (x : Fin u) (outside : ¬ C (.inl t)) :
    ActiveConnection (arrowGraph (augmented source t)) (augmentedCondition C) none (some (.inr x)) := by
  apply two_edge_active (arrowGraph (augmented source t)) (augmentedCondition C) none (some (.inl t)) (some (.inr x))
    (by intro «impossible»; cases «impossible») (by intro «impossible»; cases «impossible»)
    (by intro «impossible»; cases «impossible») .tail .head .tail .head
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨targets_cause_all source t x, rfl, rfl⟩
  · simpa (config := {instances := true}) [ActiveAt, augmentedCondition] using outside

def otherRootsSupport {k u : Nat} (t : Fin k) : Option (Labels k u) → Prop
  | none => True
  | some (.inl s) => s ≠ t
  | some (.inr _) => False

theorem other_roots_support_closed {k u : Nat} (source : Option (Index u)) (t : Fin k) :
    BackwardClosed (arrowGraph (augmented source t)) (otherRootsSupport t) := by
  intro parent child edge member
  have raw := (arrow_directed_exact _ _ _).mp edge
  cases child with
  | none => exact (indicator_no_parent (arrow source) (.inl t) parent raw).elim
  | some child =>
      cases child with
      | inr x => exact member.elim
      | inl s =>
          cases parent with
          | none => trivial
          | some parent => exact (target_has_no_parent source s parent raw).elim

theorem other_root_no_selected_untargeted_separated {k u : Nat} (source : Option (Index u))
    (t s : Fin k) (different : s ≠ t) (C : Labels k u → Prop)
    (targetOutside : ¬ C (.inl t)) (noUntargeted : ∀ z : Fin u, ¬ C (.inr z)) :
    ¬ ActiveConnection (arrowGraph (augmented source t)) (augmentedCondition C) none (some (.inl s)) := by
  apply separated_by_no_first_neighbor _ (raw_arrow_mixed_laws _ (augmented_acyclic source t))
    (augmentedCondition C) (otherRootsSupport t) (other_roots_support_closed source t)
  · intro v conditioned
    cases v with
    | none => exact conditioned.elim
    | some v => cases v with
      | inl root => intro same; subst root; exact targetOutside conditioned
      | inr z => exact (noUntargeted z conditioned).elim
  · intro «impossible»; cases «impossible»
  · trivial
  · exact different
  · intro v ma mb edge member
    have same := indicator_neighbor source t v ⟨ma, mb, edge⟩
    rw [same] at member
    exact member rfl

/-- The literal open path I_t -> t -> z <- s. Its four vertices are
distinct, t is an unconditioned noncollider, and z is a conditioned collider. -/
theorem other_root_selected_untargeted_active {k u : Nat} (source : Option (Index u))
    (t s : Fin k) (different : s ≠ t) (C : Labels k u → Prop)
    (targetOutside : ¬ C (.inl t)) (z : Fin u) (selected : C (.inr z)) :
    ActiveConnection (arrowGraph (augmented source t)) (augmentedCondition C) none (some (.inl s)) := by
  have activated : SourceSelection.AncestorOf (arrowGraph (augmented source t))
      (augmentedCondition C) (some (.inr z)) := ⟨some (.inr z), ⟨[], .nil _⟩, selected⟩
  refine ⟨some .tail,
    [⟨some (.inl t), some .head⟩, ⟨some (.inr z), some .head⟩, ⟨some (.inl s), some .tail⟩],
    .cons ⟨.tail, .head, Or.inl ⟨rfl, rfl, rfl⟩, rfl, trivial⟩
      (.cons ⟨.tail, .head, Or.inl ⟨targets_cause_all source t z, rfl, rfl⟩, rfl, ?_⟩
        (.cons ⟨.head, .tail, Or.inr ⟨targets_cause_all source s z, rfl, rfl⟩, rfl, ?_⟩ (.nil _))), ?_⟩
  · simpa (config := {instances := true}) [ActiveAt, augmentedCondition] using targetOutside
  · simpa (config := {instances := true}) [ActiveAt] using activated
  · simp [different, different.symm]

theorem indicator_untargeted_separated_iff {k u : Nat} (source : Option (Index u))
    (t : Fin k) (C : Labels k u → Prop) (x : Fin u) (outside : ¬ C (.inr x)) :
    (¬ ActiveConnection (arrowGraph (augmented source t)) (augmentedCondition C) none (some (.inr x))) ↔
      C (.inl t) := by
  constructor
  · intro separated
    by_contra targetOutside
    exact separated (indicator_untargeted_active source t C x targetOutside)
  · exact conditioned_target_blocks source t C (.inr x) outside

theorem indicator_other_root_separated_iff {k u : Nat} (source : Option (Index u))
    (t s : Fin k) (different : s ≠ t) (C : Labels k u → Prop) (outside : ¬ C (.inl s)) :
    (¬ ActiveConnection (arrowGraph (augmented source t)) (augmentedCondition C) none (some (.inl s))) ↔
      C (.inl t) ∨ ∀ z : Fin u, ¬ C (.inr z) := by
  constructor
  · intro separated
    by_cases targetConditioned : C (.inl t)
    · exact Or.inl targetConditioned
    · right
      intro z selected
      exact separated (other_root_selected_untargeted_active source t s different C targetConditioned z selected)
  · rintro (conditioned | noUntargeted)
    · exact conditioned_target_blocks source t C (.inl s) outside conditioned
    · by_cases conditioned : C (.inl t)
      · exact conditioned_target_blocks source t C (.inl s) outside conditioned
      · exact other_root_no_selected_untargeted_separated source t s different C conditioned noUntargeted

/-- Every elementary invariance bit agrees for every baseline/rival pair.
The quantifiers include ALL available t, endpoints and legal C. -/
theorem all_indicator_separations_equal {k u : Nat} («first» second : Option (Index u))
    (t : Fin k) (C : Labels k u → Prop) (x : Labels k u) (outside : ¬ C x) :
    (¬ ActiveConnection (arrowGraph (augmented «first» t)) (augmentedCondition C) none (some x)) ↔
      (¬ ActiveConnection (arrowGraph (augmented second t)) (augmentedCondition C) none (some x)) := by
  cases x with
  | inr x => rw [indicator_untargeted_separated_iff «first» t C x outside,
      indicator_untargeted_separated_iff second t C x outside]
  | inl s =>
      by_cases same : s = t
      · subst s
        exact ⟨fun h => (h (indicator_target_active «first» t C)).elim,
          fun h => (h (indicator_target_active second t C)).elim⟩
      · rw [indicator_other_root_separated_iff «first» t s same C outside,
          indicator_other_root_separated_iff second t s same C outside]

end RestrictedCausal.HardFamily
