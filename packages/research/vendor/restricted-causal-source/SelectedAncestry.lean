import SelectedSourceProfile

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Original-source B3 and concrete canonical selected-graph construction.
Original latent projection, MAG/TCM semantics and finite counts remain separate.
-/

namespace RestrictedCausal.SourceSelection

open SelectedWalk CanonicalSelection

universe u v

theorem no_selected_departure {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (s : S) (v : Sum X S) :
    ¬ Directed (graph H) (.inr s) v := by
  intro h
  cases v with
  | inl x => exact Mark.noConfusion h.2
  | inr t => exact Mark.noConfusion h.2.1

def observedOption {X : Type u} {S : Type v} : Sum X S → Option X
  | .inl x => some x
  | .inr _ => none

theorem route_to_observed {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {a b : Sum X S} {xs : List (Sum X S)}
    (h : Route (Directed (graph H)) a xs b) :
    ∀ y : X, b = .inl y → ∃ x : X, a = .inl x ∧
      Route (Directed H.observed) x (xs.filterMap observedOption) y := by
  induction h with
  | nil a =>
      intro y ha
      subst a
      exact ⟨y, rfl, .nil y⟩
  | @cons a b c xs hab hbc ih =>
      intro y hc
      obtain ⟨z, hb, hz⟩ := ih y hc
      subst b
      cases a with
      | inl x => exact ⟨x, rfl, .cons hab hz⟩
      | inr s => exact (no_selected_departure H s (.inl z) hab).elim

theorem lift_observed_route {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {x y : X} {xs : List X} (h : Route (Directed H.observed) x xs y) :
    Route (Directed (graph H)) (.inl x)
      (xs.map (fun z => Sum.inl z : X → Sum X S)) (.inl y) := by
  induction h with
  | nil x => exact .nil (.inl x)
  | cons hstep htail ih => exact .cons hstep ih

theorem observed_ancestry_exact {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (x y : X) :
    Reach (graph H) (.inl x) (.inl y) ↔ Reach H.observed x y := by
  constructor
  · rintro ⟨xs, h⟩
    obtain ⟨z, hz, hp⟩ := route_to_observed H h y rfl
    have heq : x = z := Sum.inl.inj hz
    subst z
    exact ⟨_, hp⟩
  · rintro ⟨xs, h⟩
    exact ⟨_, lift_observed_route H h⟩

theorem route_to_selector {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {a b : Sum X S} {xs : List (Sum X S)}
    (h : Route (Directed (graph H)) a xs b) :
    ∀ s : S, b = .inr s →
      (a = .inr s ∧ xs = []) ∨
      ∃ x z : X, a = .inl x ∧ Reach H.observed x z ∧ H.boundary z .tail s := by
  induction h with
  | nil a =>
      intro s ha
      exact Or.inl ⟨ha, rfl⟩
  | @cons a b c xs hab hbc ih =>
      intro s hc
      rcases ih s hc with ⟨hb, _⟩ | ⟨x, z, hb, hpath, hinc⟩
      · subst b
        cases a with
        | inl y => exact Or.inr ⟨y, y, rfl, ⟨[], .nil y⟩, hab.1⟩
        | inr t => exact (no_selected_departure H t (.inr s) hab).elim
      · subst b
        cases a with
        | inl y =>
            obtain ⟨zs, hzs⟩ := hpath
            exact Or.inr ⟨y, z, rfl, ⟨x :: zs, .cons hab hzs⟩, hinc⟩
        | inr t => exact (no_selected_departure H t (.inl x) hab).elim

theorem selection_ancestry_exact {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (x : X) :
    (∃ s : S, Reach (graph H) (.inl x) (.inr s)) ↔
      ∃ z : X, Reach H.observed x z ∧ Parent H z := by
  constructor
  · rintro ⟨s, xs, h⟩
    rcases route_to_selector H h s rfl with ⟨hbad, _⟩ | ⟨y, z, hxy, hp, hi⟩
    · exact Sum.noConfusion hbad
    · have heq : x = y := Sum.inl.inj hxy
      subst y
      exact ⟨z, hp, s, hi⟩
  · rintro ⟨z, ⟨xs, h⟩, s, hs⟩
    have hlast : Directed (graph H) (.inl z) (.inr s) := ⟨hs, rfl⟩
    exact ⟨s, _, (lift_observed_route H h).append (.cons hlast (.nil (.inr s)))⟩

/-- The entire original selection set is conditioned, not discarded. -/
def Condition {X : Type u} {S : Type v} (Z : X → Prop) : Sum X S → Prop
  | .inl x => Z x
  | .inr _ => True

def AncestorOf {V : Type u} (G : MarkedGraph V) (C : V → Prop) (x : V) : Prop :=
  ∃ y, Reach G x y ∧ C y

theorem selected_is_ancestor {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (Z : X → Prop) (s : S) :
    AncestorOf (graph H) (Condition Z) (.inr s) :=
  ⟨.inr s, ⟨[], .nil (.inr s)⟩, trivial⟩

/-- The exact original ancestry formula needed for internal collider activity.
It includes F even when its members have no marked-pair participation. -/
theorem observed_condition_ancestry {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (Z : X → Prop) (x : X) :
    AncestorOf (graph H) (Condition Z) (.inl x) ↔
      ∃ z, Reach H.observed x z ∧ (Z z ∨ Parent H z) := by
  constructor
  · rintro ⟨v, hp, hc⟩
    cases v with
    | inl z => exact ⟨z, (observed_ancestry_exact H x z).mp hp, Or.inl hc⟩
    | inr s =>
        obtain ⟨z, hz, hf⟩ := (selection_ancestry_exact H x).mp ⟨s, hp⟩
        exact ⟨z, hz, Or.inr hf⟩
  · rintro ⟨z, hp, hz | hf⟩
    · exact ⟨.inl z, (observed_ancestry_exact H x z).mpr hp, hz⟩
    · obtain ⟨s, hs⟩ := (selection_ancestry_exact H x).mpr ⟨z, hp, hf⟩
      exact ⟨.inr s, hs, trivial⟩

/-- The actual canonical selected graph, in the same source data type. -/
def canonical {X : Type u} [LinearOrder X] (Q : Profile X) :
    SelectedGraph X (Selector Q) where
  observed := Q.observed
  boundary := Incident Q
  selectionEdge := fun _ _ => False
  selection_symm := False.elim

theorem canonical_parent {X : Type u} [LinearOrder X] (Q : Profile X) (x : X) :
    Parent (canonical Q) x ↔ Q.parent x := by
  constructor
  · rintro ⟨s, hs⟩
    exact incident_tail_parent Q hs
  · intro hx
    exact ⟨.inl ⟨x, hx⟩, rfl, rfl⟩

theorem canonical_bridge {X : Type u} [LinearOrder X] (Q : Profile X)
    (x : X) (mx : Mark) (y : X) (my : Mark) :
    Bridge (canonical Q) x mx y my ↔ Q.bridge x mx y my := by
  exact marked_pairs_exact Q x mx y my

end RestrictedCausal.SourceSelection
