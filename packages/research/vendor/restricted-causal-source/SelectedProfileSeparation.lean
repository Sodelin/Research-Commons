import SelectedAncestry

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. Not elaborated or executed.
Composition of the proved extraction, contraction, lifting and ancestry terms.
No latent-projection or MAG/TCM theorem is assumed as a structure field.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u v

theorem map {α : Type u} {β : Type v} {R : α → α → Prop} {T : β → β → Prop}
    (f : α → β) (hf : ∀ a b, R a b → T (f a) (f b))
    {a b : α} {xs : List α} (h : Route R a xs b) :
    Route T (f a) (xs.map f) (f b) := by
  induction h with
  | nil a => exact .nil (f a)
  | @cons a b c xs hab hbc ih => exact .cons (hf a b hab) ih

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.SourceSelection

open SelectedWalk CanonicalSelection

universe u v w

def IsObserved {X : Type u} {S : Type v} (p : Arrival (Sum X S)) : Prop :=
  ∃ x : X, p.vertex = .inl x

theorem compressed_route_observed {X : Type u} {S : Type v}
    (H : SelectedGraph X S) {C A : Sum X S → Prop}
    {a b : Arrival (Sum X S)} {xs : List (Arrival (Sum X S))}
    (h : Route (CompressedTransition H C A) a xs b) :
    IsObserved a → ∀ p ∈ a :: xs, IsObserved p := by
  induction h with
  | nil a =>
      intro ha p hp
      have heq : p = a := by simpa only [List.mem_singleton] using hp
      exact heq.symm ▸ ha
  | @cons a b c xs hab hbc ih =>
      intro ha p hp
      obtain ⟨x, y, outgoing, incoming, _, hb, _⟩ := hab
      rcases List.mem_cons.mp hp with hpa | hp
      · exact hpa.symm ▸ ha
      · exact ih ⟨y, hb⟩ p hp

/-- The fallback is used only to make a total map. All routes to which it is
applied below are proved observed-only, so no selected vertex is reclassified. -/
def relabel {X : Type u} {S : Type v} {T : Type w} (fallback : X)
    (p : Arrival (Sum X S)) : Arrival (Sum X T) :=
  ⟨.inl (match p.vertex with | .inl x => x | .inr _ => fallback), p.incoming⟩

theorem relabel_noObservedRepeat {X : Type u} {S : Type v} {T : Type w}
    (fallback : X) {xs : List (Arrival (Sum X S))}
    (hall : ∀ p ∈ xs, IsObserved p) (h : NoObservedRepeat isSelected xs) :
    NoObservedRepeat isSelected (xs.map (relabel (T := T) fallback)) := by
  unfold NoObservedRepeat
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ h
  intro p q hp hq hpq
  obtain ⟨x, hpx⟩ := hall p hp
  obtain ⟨y, hqy⟩ := hall q hq
  rcases p with ⟨pv, pm⟩
  rcases q with ⟨qv, qm⟩
  change pv = .inl x at hpx
  change qv = .inl y at hqy
  subst pv
  subst qv
  intro heq
  have hxy : x = y := Sum.inl.inj heq
  have hbad := hpq (congrArg Sum.inl hxy)
  exact hbad.elim

/-- The finite sufficient profile equality needed for transfer. Each component
is an equality of actual extracted data, not an assumed separation theorem. -/
structure SameProfile {X : Type u} {S : Type v} {T : Type w}
    (H : SelectedGraph X S) (K : SelectedGraph X T) : Prop where
  observed : H.observed = K.observed
  parent : ∀ x, Parent H x ↔ Parent K x
  bridge : ∀ x mx y my, Bridge H x mx y my ↔ Bridge K x mx y my

theorem SameProfile.symm {X : Type u} {S : Type v} {T : Type w}
    {H : SelectedGraph X S} {K : SelectedGraph X T} (h : SameProfile H K) :
    SameProfile K H :=
  ⟨h.observed.symm, fun x => (h.parent x).symm,
    fun x mx y my => (h.bridge x mx y my).symm⟩

theorem SameProfile.ancestor {X : Type u} {S : Type v} {T : Type w}
    {H : SelectedGraph X S} {K : SelectedGraph X T} (h : SameProfile H K)
    (Z : X → Prop) (x : X) :
    AncestorOf (graph H) (Condition Z) (.inl x) ↔
      AncestorOf (graph K) (Condition Z) (.inl x) := by
  rw [observed_condition_ancestry, observed_condition_ancestry]
  constructor
  · rintro ⟨z, hz, hc | hf⟩
    · exact ⟨z, h.observed ▸ hz, Or.inl hc⟩
    · exact ⟨z, h.observed ▸ hz, Or.inr ((h.parent z).mp hf)⟩
  · rintro ⟨z, hz, hc | hf⟩
    · exact ⟨z, h.observed.symm ▸ hz, Or.inl hc⟩
    · exact ⟨z, h.observed.symm ▸ hz, Or.inr ((h.parent z).mpr hf)⟩

theorem same_profile_compressed_step {X : Type u} {S : Type v} {T : Type w}
    {H : SelectedGraph X S} {K : SelectedGraph X T} (same : SameProfile H K)
    (Z : X → Prop) (fallback : X) (p q : Arrival (Sum X S))
    (h : CompressedTransition H (Condition Z) (AncestorOf (graph H) (Condition Z)) p q) :
    CompressedTransition K (Condition Z) (AncestorOf (graph K) (Condition Z))
      (relabel fallback p) (relabel fallback q) := by
  obtain ⟨x, y, outgoing, incoming, hp, hq, hmark, hactive, hedge⟩ := h
  rcases p with ⟨pv, pm⟩
  rcases q with ⟨qv, qm⟩
  change pv = .inl x at hp
  change qv = .inl y at hq
  subst pv
  subst qv
  refine ⟨x, y, outgoing, incoming, rfl, rfl, hmark, ?_, ?_⟩
  · cases pm with
    | none => trivial
    | some previous =>
        change ActiveAt (Condition Z) (AncestorOf (graph K) (Condition Z))
          (.inl x) previous outgoing
        change ActiveAt (Condition Z) (AncestorOf (graph H) (Condition Z))
          (.inl x) previous outgoing at hactive
        by_cases hcollider : previous = .head ∧ outgoing = .head
        · simp only [ActiveAt, if_pos hcollider] at hactive ⊢
          exact (same.ancestor Z x).mp hactive
        · simp only [ActiveAt, if_neg hcollider] at hactive ⊢
          exact hactive
  · rcases hedge with hdir | hbridge
    · exact Or.inl (same.observed ▸ hdir)
    · exact Or.inr ((same.bridge x outgoing y incoming).mp hbridge)

/-- An actual vertex-simple active path. Endpoint activity is not imposed;
the intended separated endpoints are separately required outside Z. -/
def ActivePath {X : Type u} {S : Type v} (H : SelectedGraph X S)
    (Z : X → Prop) (x y : X) : Prop :=
  ∃ lastMark xs,
    Route (Transition (graph H) (Condition Z)
      (AncestorOf (graph H) (Condition Z)))
      (observedArrival x none) xs (observedArrival y lastMark) ∧
    ((observedArrival x none :: xs).map Arrival.vertex).Nodup

theorem noObservedRepeat_of_vertex_nodup {X : Type u} {S : Type v}
    {xs : List (Arrival (Sum X S))} (h : (xs.map Arrival.vertex).Nodup) :
    NoObservedRepeat isSelected xs := by
  have hp : xs.Pairwise (fun p q => p.vertex ≠ q.vertex) := by
    simpa only [List.Nodup, List.pairwise_map] using h
  exact hp.imp (fun hne heq => (hne heq).elim)

theorem SameProfile.activePath {X : Type u} {S : Type v} {T : Type w}
    {H : SelectedGraph X S} {K : SelectedGraph X T} (same : SameProfile H K)
    (Z : X → Prop) (x y : X) (h : ActivePath H Z x y) : ActivePath K Z x y := by
  obtain ⟨lastMark, xs, hp, hnd⟩ := h
  have hobs := noObservedRepeat_of_vertex_nodup hnd
  obtain ⟨ys, hmacro, hsub⟩ := contract_active_route H hp hobs
  have hmacroObs : NoObservedRepeat isSelected (observedArrival x none :: ys) :=
    hobs.sublist (hsub.cons_cons _)
  have hall := compressed_route_observed H hmacro ⟨x, rfl⟩
  have hroute := hmacro.map (relabel (T := T) x)
    (same_profile_compressed_step same Z x)
  have hnodup := relabel_noObservedRepeat (T := T) x hall hmacroObs
  obtain ⟨zs, hz, hsimple⟩ := compressed_route_realizes_simple K
    (selected_is_ancestor K Z) hroute hnodup
  exact ⟨lastMark, zs, hz, hsimple⟩

/-- Full selected active-path equivalence, proved through concrete contraction
and lifting. Neither graph is required to have a bounded original selection set. -/
theorem same_profile_activePath_iff {X : Type u} {S : Type v} {T : Type w}
    {H : SelectedGraph X S} {K : SelectedGraph X T} (same : SameProfile H K)
    (Z : X → Prop) (x y : X) : ActivePath H Z x y ↔ ActivePath K Z x y :=
  ⟨same.activePath Z x y, same.symm.activePath Z x y⟩

theorem canonical_same_profile {X : Type u} {S : Type v} [LinearOrder X]
    (H : SelectedGraph X S) : SameProfile H (canonical (profile H)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro x
    exact (canonical_parent (profile H) x).symm
  · intro x mx y my
    exact (canonical_bridge (profile H) x mx y my).symm

/-- The canonical selected graph preserves all observed active paths, with
the true ancestor-of-Z-union-S activity predicate rather than a free predicate. -/
theorem canonical_activePath_iff {X : Type u} {S : Type v} [LinearOrder X]
    (H : SelectedGraph X S) (Z : X → Prop) (x y : X) :
    ActivePath H Z x y ↔ ActivePath (canonical (profile H)) Z x y :=
  same_profile_activePath_iff (canonical_same_profile H) Z x y

theorem SameProfile.augment {X : Type u} {S : Type v} {T : Type w}
    {H : SelectedGraph X S} {K : SelectedGraph X T} (same : SameProfile H K)
    (target : X) : SameProfile (augment H target) (augment K target) := by
  refine ⟨congrArg (fun G => augmentObserved G target) same.observed, ?_, ?_⟩
  · intro x
    cases x with
    | none =>
        exact ⟨fun h => (augment_parent_root H target h).elim,
          fun h => (augment_parent_root K target h).elim⟩
    | some x => exact same.parent x
  · intro x mx y my
    cases x with
    | none =>
        exact ⟨fun h => (augment_bridge_root_left H target y mx my h).elim,
          fun h => (augment_bridge_root_left K target y mx my h).elim⟩
    | some x =>
        cases y with
        | none =>
            exact ⟨fun h => (augment_bridge_root_right H target (some x) mx my h).elim,
              fun h => (augment_bridge_root_right K target (some x) mx my h).elim⟩
        | some y =>
            exact (augment_bridge_old H target x y mx my).trans
              ((same.bridge x mx y my).trans
                (augment_bridge_old K target x y mx my).symm)

theorem SameProfile.observedReach {X : Type u} {S : Type v} {T : Type w}
    {H : SelectedGraph X S} {K : SelectedGraph X T} (same : SameProfile H K)
    (x y : X) : Reach (graph H) (.inl x) (.inl y) ↔
      Reach (graph K) (.inl x) (.inl y) := by
  rw [observed_ancestry_exact, observed_ancestry_exact, same.observed]

theorem SameProfile.selectionReach {X : Type u} {S : Type v} {T : Type w}
    {H : SelectedGraph X S} {K : SelectedGraph X T} (same : SameProfile H K)
    (x : X) : (∃ s, Reach (graph H) (.inl x) (.inr s)) ↔
      ∃ t, Reach (graph K) (.inl x) (.inr t) := by
  rw [selection_ancestry_exact, selection_ancestry_exact]
  constructor
  · rintro ⟨z, hz, hf⟩
    exact ⟨z, same.observed ▸ hz, (same.parent z).mp hf⟩
  · rintro ⟨z, hz, hf⟩
    exact ⟨z, same.observed.symm ▸ hz, (same.parent z).mpr hf⟩

/-- One fixed canonical graph works for every named single-root augmentation.
The statement does not select separate realizations for separate indicators.
All variables, including the newly named root, remain in the path quantifiers. -/
theorem canonical_augmented_preservation {X : Type u} {S : Type v} [LinearOrder X]
    (H : SelectedGraph X S) (target : X) :
    (∀ (Z : Option X → Prop) (x y : Option X),
      ActivePath (augment H target) Z x y ↔
        ActivePath (augment (canonical (profile H)) target) Z x y) ∧
    (∀ x y : Option X,
      Reach (graph (augment H target)) (.inl x) (.inl y) ↔
        Reach (graph (augment (canonical (profile H)) target)) (.inl x) (.inl y)) ∧
    (∀ x : Option X,
      (∃ s, Reach (graph (augment H target)) (.inl x) (.inr s)) ↔
        ∃ t, Reach (graph (augment (canonical (profile H)) target)) (.inl x) (.inr t)) := by
  have same := (canonical_same_profile H).augment target
  exact ⟨same_profile_activePath_iff same, same.observedReach, same.selectionReach⟩

end RestrictedCausal.SourceSelection
