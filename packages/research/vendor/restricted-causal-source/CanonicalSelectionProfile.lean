import SelectedWalkReduction
import Mathlib.Order.Defs.LinearOrder

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. Not elaborated, executed, or kernel checked.
Lean v4.33.1 / mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

Actual canonical construction and profile proofs for B7. `Profile` contains
data and elementary symmetry/validity conditions, NOT a separation-preservation
or source-compression theorem. The proof constructs every selector explicitly.
Singleton parent flags and all four marked-pair possibilities are retained.
This component alone is not the full selected source registry theorem.
-/

namespace RestrictedCausal.CanonicalSelection

open SelectedWalk

universe u

structure Profile (X : Type u) where
  observed : MarkedGraph X
  parent : X → Prop
  bridge : X → Mark → X → Mark → Prop
  bridge_ne : ∀ {x mx y my}, bridge x mx y my → x ≠ y
  bridge_symm : ∀ {x mx y my}, bridge x mx y my → bridge y my x mx
  bridge_tails : ∀ {x mx y my}, bridge x mx y my →
    (mx = .tail → parent x) ∧ (my = .tail → parent y)

structure BridgeToken {X : Type u} [LinearOrder X] (Q : Profile X) where
  «left» : X
  «right» : X
  leftMark : Mark
  rightMark : Mark
  ordered : «left» < «right»
  allowed : Q.bridge «left» leftMark «right» rightMark

abbrev Selector {X : Type u} [LinearOrder X] (Q : Profile X) :=
  Sum {x : X // Q.parent x} (BridgeToken Q)

abbrev Vertex {X : Type u} [LinearOrder X] (Q : Profile X) := Sum X (Selector Q)

/-- A selector has one flagged parent, or one specified marked endpoint pair.
The two endpoint marks are independent, including two tails or two heads. -/
def Incident {X : Type u} [LinearOrder X] (Q : Profile X) (x : X) (m : Mark) : Selector Q → Prop
  | .inl p => x = p.val ∧ m = .tail
  | .inr b => (x = b.left ∧ m = b.leftMark) ∨
      (x = b.right ∧ m = b.rightMark)

def graph {X : Type u} [LinearOrder X] (Q : Profile X) : MarkedGraph (Vertex Q) where
  edge a b ma mb := match a, b with
    | .inl x, .inl y => Q.observed.edge x y ma mb
    | .inl x, .inr s => Incident Q x ma s ∧ mb = .head
    | .inr s, .inl x => Incident Q x mb s ∧ ma = .head
    | .inr _, .inr _ => False

def selected {X : Type u} [LinearOrder X] {Q : Profile X} : Vertex Q → Prop
  | .inl _ => False
  | .inr _ => True

theorem observed_edges_exact {X : Type u} [LinearOrder X] (Q : Profile X)
    (x y : X) (mx my : Mark) :
    (graph Q).edge (.inl x) (.inl y) mx my ↔ Q.observed.edge x y mx my :=
  Iff.rfl

theorem selection_heads {X : Type u} [LinearOrder X] (Q : Profile X) :
    SelectionHeads (graph Q) selected := by
  intro a b ma mb hedge
  cases a with
  | inl x =>
      cases b with
      | inl y => exact ⟨False.elim, False.elim⟩
      | inr s => exact ⟨False.elim, fun _ => hedge.2⟩
  | inr s =>
      cases b with
      | inl y => exact ⟨fun _ => hedge.2, False.elim⟩
      | inr t => exact hedge.elim

theorem incident_tail_parent {X : Type u} [LinearOrder X] (Q : Profile X)
    {x : X} {s : Selector Q} (h : Incident Q x .tail s) : Q.parent x := by
  cases s with
  | inl p =>
      obtain ⟨rfl, _⟩ := h
      exact p.property
  | inr b =>
      rcases h with ⟨rfl, hmark⟩ | ⟨rfl, hmark⟩
      · exact (Q.bridge_tails b.allowed).1 hmark.symm
      · exact (Q.bridge_tails b.allowed).2 hmark.symm

/-- Singleton selectors are essential to the reverse direction even when no
marked pair uses that parent. -/
theorem parent_flags_exact {X : Type u} [LinearOrder X] (Q : Profile X) (x : X) :
    (∃ s : Selector Q, (graph Q).edge (.inl x) (.inr s) .tail .head) ↔
      Q.parent x := by
  constructor
  · rintro ⟨s, hs⟩
    exact incident_tail_parent Q hs.1
  · intro hx
    exact ⟨.inl ⟨x, hx⟩, ⟨⟨rfl, rfl⟩, rfl⟩⟩

def SelectionConnected {X : Type u} [LinearOrder X] (Q : Profile X)
    (s t : Selector Q) : Prop :=
  ∃ xs, Route (fun a b : Selector Q =>
    (graph Q).edge (.inr a) (.inr b) .head .head) s xs t

theorem selection_components_singleton {X : Type u} [LinearOrder X] (Q : Profile X)
    (s t : Selector Q) : SelectionConnected Q s t ↔ s = t := by
  constructor
  · rintro ⟨xs, h⟩
    cases h with
    | nil => rfl
    | cons step tail => exact step.elim
  · intro h
    subst t
    exact ⟨[], .nil s⟩

def VirtualBoundary {X : Type u} [LinearOrder X] (Q : Profile X)
    (x : X) (mx : Mark) (y : X) (my : Mark) : Prop :=
  x ≠ y ∧ ∃ s t : Selector Q,
    Incident Q x mx s ∧ SelectionConnected Q s t ∧ Incident Q y my t

theorem same_selector_pair {X : Type u} [LinearOrder X] (Q : Profile X)
    {x y : X} {mx my : Mark} {s : Selector Q}
    (hne : x ≠ y) (hx : Incident Q x mx s) (hy : Incident Q y my s) :
    Q.bridge x mx y my := by
  cases s with
  | inl p =>
      obtain ⟨hxp, _⟩ := hx
      obtain ⟨hyp, _⟩ := hy
      exact (hne (hxp.trans hyp.symm)).elim
  | inr b =>
      rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (hne rfl).elim
        · exact b.allowed
      · rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Q.bridge_symm b.allowed
        · exact (hne rfl).elim

/-- No independent-slice realization and no hidden bound is assumed: the one
explicit graph has exactly the original marked boundary profile. -/
theorem marked_pairs_exact {X : Type u} [LinearOrder X] (Q : Profile X)
    (x : X) (mx : Mark) (y : X) (my : Mark) :
    VirtualBoundary Q x mx y my ↔ Q.bridge x mx y my := by
  constructor
  · rintro ⟨hne, s, t, hx, hst, hy⟩
    have hst' : s = t := (selection_components_singleton Q s t).mp hst
    subst t
    exact same_selector_pair Q hne hx hy
  · intro h
    rcases lt_or_gt_of_ne (Q.bridge_ne h) with hxy | hyx
    · let b : BridgeToken Q := ⟨x, y, mx, my, hxy, h⟩
      refine ⟨Q.bridge_ne h, .inr b, .inr b, ?_, ?_, ?_⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact (selection_components_singleton Q _ _).mpr rfl
      · exact Or.inr ⟨rfl, rfl⟩
    · let b : BridgeToken Q := ⟨y, x, my, mx, hyx, Q.bridge_symm h⟩
      refine ⟨Q.bridge_ne h, .inr b, .inr b, ?_, ?_, ?_⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (selection_components_singleton Q _ _).mpr rfl
      · exact Or.inl ⟨rfl, rfl⟩

def Directed {V : Type u} (G : MarkedGraph V) (x y : V) : Prop :=
  G.edge x y .tail .head

def Reach {V : Type u} (G : MarkedGraph V) (x y : V) : Prop :=
  ∃ xs, Route (Directed G) x xs y

theorem no_selected_departure {X : Type u} [LinearOrder X] (Q : Profile X)
    (s : Selector Q) (v : Vertex Q) : ¬ Directed (graph Q) (.inr s) v := by
  intro h
  cases v with
  | inl x => exact Mark.noConfusion h.2
  | inr t => exact h.elim

def observedOption {X : Type u} [LinearOrder X] {Q : Profile X} : Vertex Q → Option X
  | .inl x => some x
  | .inr _ => none

/-- A canonical directed path ending at an observed vertex never visits a
selector. Its observed projection is a genuine directed path in H_X. -/
theorem route_to_observed {X : Type u} [LinearOrder X] (Q : Profile X)
    {a b : Vertex Q} {xs : List (Vertex Q)}
    (h : Route (Directed (graph Q)) a xs b) :
    ∀ y : X, b = .inl y → ∃ x : X, a = .inl x ∧
      Route (Directed Q.observed) x (xs.filterMap observedOption) y := by
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
      | inr s => exact (no_selected_departure Q s (.inl z) hab).elim

theorem lift_observed_route {X : Type u} [LinearOrder X] (Q : Profile X)
    {x y : X} {xs : List X} (h : Route (Directed Q.observed) x xs y) :
    Route (Directed (graph Q)) (.inl x)
      (xs.map (fun z => Sum.inl z : X → Vertex Q)) (.inl y) := by
  induction h with
  | nil x => exact .nil (.inl x)
  | cons hstep htail ih => exact .cons hstep ih

theorem observed_ancestry_exact {X : Type u} [LinearOrder X] (Q : Profile X) (x y : X) :
    Reach (graph Q) (.inl x) (.inl y) ↔ Reach Q.observed x y := by
  constructor
  · rintro ⟨xs, h⟩
    obtain ⟨z, hz, hp⟩ := route_to_observed Q h y rfl
    have hzx : x = z := Sum.inl.inj hz
    subst z
    exact ⟨_, hp⟩
  · rintro ⟨xs, h⟩
    exact ⟨_, lift_observed_route Q h⟩

/-- A route ending at a selector is either its zero-length route, or an
observed route followed by one tail incidence into that very selector. -/
theorem route_to_selector {X : Type u} [LinearOrder X] (Q : Profile X)
    {a b : Vertex Q} {xs : List (Vertex Q)}
    (h : Route (Directed (graph Q)) a xs b) :
    ∀ s : Selector Q, b = .inr s →
      (a = .inr s ∧ xs = []) ∨
      ∃ x z : X, a = .inl x ∧ Reach Q.observed x z ∧ Incident Q z .tail s := by
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
        | inr t => exact (no_selected_departure Q t (.inr s) hab).elim
      · subst b
        cases a with
        | inl y =>
            obtain ⟨zs, hzs⟩ := hpath
            exact Or.inr ⟨y, z, rfl, ⟨x :: zs, .cons hab hzs⟩, hinc⟩
        | inr t => exact (no_selected_departure Q t (.inl x) hab).elim

/-- Exact selection ancestry, including singleton flags. This is not merely
an independence statement: it supplies the ancestry part needed for MAG marks. -/
theorem selection_ancestry_exact {X : Type u} [LinearOrder X]
    (Q : Profile X) (x : X) :
    (∃ s : Selector Q, Reach (graph Q) (.inl x) (.inr s)) ↔
      ∃ z : X, Reach Q.observed x z ∧ Q.parent z := by
  constructor
  · rintro ⟨s, xs, h⟩
    rcases route_to_selector Q h s rfl with ⟨hbad, _⟩ | ⟨y, z, hxy, hp, hi⟩
    · exact Sum.noConfusion hbad
    · have heq : x = y := Sum.inl.inj hxy
      subst y
      exact ⟨z, hp, incident_tail_parent Q hi⟩
  · rintro ⟨z, ⟨xs, h⟩, hz⟩
    let s : Selector Q := .inl ⟨z, hz⟩
    have hlast : Directed (graph Q) (.inl z) (.inr s) :=
      ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨s, _, (lift_observed_route Q h).append (.cons hlast (.nil (.inr s)))⟩

end RestrictedCausal.CanonicalSelection
