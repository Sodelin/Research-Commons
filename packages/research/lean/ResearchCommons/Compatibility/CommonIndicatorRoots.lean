import MarkedGraphEquivalence
import Mathlib.Order.WithBot

/- Pinned-context proof variant: actual WithBot case names, explicit marked
Directed name, and computed equivalence/identity reductions. Original graph,
root maps, activity/ancestry statements and source hypotheses are unchanged. -/


/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Named-root augmentation of the SAME actual canonical latent-root DAG.
The root-label equivalence is explicit; separate slice realizations are not used.
-/

namespace RestrictedCausal.LatentRoots

open SelectedWalk CanonicalSelection GraphEquivalence

universe u

def augmentGraph {V : Type u} (G : MarkedGraph V) (target : V) :
    MarkedGraph (WithBot V) := SourceSelection.augmentObserved G target

theorem augment_mixed_laws {V : Type u} (G : MarkedGraph V)
    (laws : MixedLaws G) (target : V) : MixedLaws (augmentGraph G target) := by
  constructor
  · intro a b ma mb h
    cases a with
    | bot =>
        cases b with
        | bot => exact h.elim
        | coe y => exact ⟨h.1, h.2.2, h.2.1⟩
    | coe x =>
        cases b with
        | bot => exact ⟨h.1, h.2.2, h.2.1⟩
        | coe y => exact laws.symmetric x y ma mb h
  · intro a ma mb h
    cases a with
    | bot => exact h.elim
    | coe x => exact laws.irreflexive x ma mb h
  · intro a b h
    cases a with
    | bot =>
        cases b with
        | bot => exact h.elim
        | coe y => exact Mark.noConfusion h.2.2
    | coe x =>
        cases b with
        | bot => exact Mark.noConfusion h.2.1
        | coe y => exact laws.no_tail_tail x y h

def rootUp {V : Type u} [LinearOrder V] (G : MarkedGraph V) (target : V)
    (r : Root G) : Root (augmentGraph G target) :=
  ⟨some r.left, some r.right, WithBot.coe_lt_coe.mpr r.ordered, r.edge⟩

def rootDown {V : Type u} [LinearOrder V] (G : MarkedGraph V) (target : V)
    (r : Root (augmentGraph G target)) : Root G := by
  rcases r with ⟨a, b, hord, hedge⟩
  cases a with
  | bot =>
      cases b with
      | bot => exact hedge.elim
      | coe y => exact Mark.noConfusion hedge.2.1
  | coe x =>
      cases b with
      | bot => exact Mark.noConfusion hedge.2.2
      | coe y => exact ⟨x, y, WithBot.coe_lt_coe.mp hord, hedge⟩

theorem rootDown_up {V : Type u} [LinearOrder V] (G : MarkedGraph V) (target : V)
    (r : Root G) : rootDown G target (rootUp G target r) = r := by
  cases r
  rfl

theorem rootUp_down {V : Type u} [LinearOrder V] (G : MarkedGraph V) (target : V)
    (r : Root (augmentGraph G target)) : rootUp G target (rootDown G target r) = r := by
  rcases r with ⟨a, b, hord, hedge⟩
  cases a with
  | bot =>
      cases b with
      | bot => exact hedge.elim
      | coe y => exact Mark.noConfusion hedge.2.1
  | coe x =>
      cases b with
      | bot => exact Mark.noConfusion hedge.2.2
      | coe y => rfl

def rootEquiv {V : Type u} [LinearOrder V] (G : MarkedGraph V) (target : V) :
    Root G ≃ Root (augmentGraph G target) where
  toFun := rootUp G target
  invFun := rootDown G target
  left_inv := rootDown_up G target
  right_inv := rootUp_down G target

/-- The source on the left is the original canonical DAG with just one new
root; hidden-root labels and all old arrows are unchanged. -/
def indicatorVertexEquiv {V : Type u} [LinearOrder V] (G : MarkedGraph V) (target : V) :
    Option (Vertex G) ≃ Vertex (augmentGraph G target) where
  toFun a := match a with
    | none => .inl none
    | some (.inl x) => .inl (some x)
    | some (.inr r) => .inr (rootUp G target r)
  invFun b := match b with
    | .inl none => none
    | .inl (some x) => some (.inl x)
    | .inr r => some (.inr (rootDown G target r))
  left_inv a := by
    rcases a with _ | (x | r)
    · rfl
    · rfl
    · simp only [rootDown_up]
  right_inv b := by
    rcases b with (a | r)
    · cases a <;> rfl
    · simp only [rootUp_down]

private theorem indicatorVertexEquiv_apply {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (target : V) (a : Option (Vertex G)) :
    indicatorVertexEquiv G target a =
      match a with
      | none => .inl none
      | some (.inl x) => .inl (some x)
      | some (.inr r) => .inr (rootUp G target r) := by
  rfl

theorem indicator_arrow_equiv {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (target : V) (a b : Option (Vertex G)) :
    AddIndicator (Arrow G) (.inl target) a b ↔
      Arrow (augmentGraph G target) (indicatorVertexEquiv G target a)
        (indicatorVertexEquiv G target b) := by
  simp only [indicatorVertexEquiv_apply]
  rcases a with _ | (x | r) <;> rcases b with _ | (y | s) <;>
    simp [AddIndicator, Arrow, CanonicalSelection.Directed, augmentGraph, SourceSelection.augmentObserved,
      indicatorVertexEquiv, rootUp, Incident]

def indicatorGraph {V : Type u} [LinearOrder V] (G : MarkedGraph V) (target : V) :
    MarkedGraph (Option (Vertex G)) where
  edge a b ma mb :=
    (AddIndicator (Arrow G) (.inl target) a b ∧ ma = .tail ∧ mb = .head) ∨
    (AddIndicator (Arrow G) (.inl target) b a ∧ ma = .head ∧ mb = .tail)

def indicatorGraphEquiv {V : Type u} [LinearOrder V] (G : MarkedGraph V) (target : V) :
    MarkedEquiv (indicatorGraph G target) (dagGraph (augmentGraph G target)) where
  toEquiv := indicatorVertexEquiv G target
  edge a b ma mb :=
    or_congr (and_congr (indicator_arrow_equiv G target a b) Iff.rfl)
      (and_congr (indicator_arrow_equiv G target b a) Iff.rfl)

def indicatorCondition {V : Type u} [LinearOrder V] {G : MarkedGraph V}
    (C : WithBot V → Prop) : Option (Vertex G) → Prop
  | none => C none
  | some (.inl x) => C (some x)
  | some (.inr _) => False

def indicatorRetained {V : Type u} [LinearOrder V] {G : MarkedGraph V} :
    WithBot V → Option (Vertex G)
  | none => none
  | some x => some (.inl x)

theorem indicator_equiv_retained {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (target : V) (x : WithBot V) :
    indicatorVertexEquiv G target (indicatorRetained x) = .inl x := by
  cases x <;> rfl

theorem indicator_condition_equiv {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (target : V) (C : WithBot V → Prop)
    (a : Option (Vertex G)) :
    indicatorCondition C a ↔ liftCondition C (indicatorVertexEquiv G target a) := by
  rcases a with _ | (x | r) <;> exact Iff.rfl

/-- Exact active-path equivalence for one named indicator added to the SAME
baseline hidden-root DAG. No new latent roots or per-slice source choice occur. -/
theorem common_indicator_active_iff {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (laws : MixedLaws G) (target : V)
    (C : WithBot V → Prop) (x y : WithBot V) :
    ActiveConnection (indicatorGraph G target) (indicatorCondition C)
      (indicatorRetained x) (indicatorRetained y) ↔
      ActiveConnection (augmentGraph G target) C x y := by
  have h := (indicatorGraphEquiv G target).active_iff
    (indicator_condition_equiv G target C) (indicatorRetained x) (indicatorRetained y)
  have h' : ActiveConnection (indicatorGraph G target) (indicatorCondition C)
      (indicatorRetained x) (indicatorRetained y) ↔
      ActiveConnection (dagGraph (augmentGraph G target)) (liftCondition C) (.inl x) (.inl y) := by
    simpa only [indicatorGraphEquiv, indicator_equiv_retained] using h
  exact h'.trans (root_active_connection_iff (augmentGraph G target)
    (augment_mixed_laws G laws target) C x y)

theorem common_indicator_reach_iff {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (target : V) (x y : WithBot V) :
    Reach (indicatorGraph G target) (indicatorRetained x) (indicatorRetained y) ↔
      Reach (augmentGraph G target) x y := by
  have h := (indicatorGraphEquiv G target).reach_iff (indicatorRetained x) (indicatorRetained y)
  have h' : Reach (indicatorGraph G target) (indicatorRetained x) (indicatorRetained y) ↔
      Reach (dagGraph (augmentGraph G target)) (.inl x) (.inl y) := by
    simpa only [indicatorGraphEquiv, indicator_equiv_retained] using h
  exact h'.trans (retained_ancestry_exact (augmentGraph G target) x y)

theorem indicator_route_to_new {V : Type u} (D : V → V → Prop) (target : V)
    {a b : Option V} {xs : List (Option V)} (h : Route (AddIndicator D target) a xs b) :
    b = none → a = none ∧ xs = [] := by
  induction h with
  | nil a => exact fun ha => ⟨ha, rfl⟩
  | @cons a b c xs hab hbc ih =>
      intro hc
      obtain ⟨hb, _⟩ := ih hc
      subst b
      exact (indicator_no_parent D target a hab).elim

theorem indicator_old_route {V : Type u} (D : V → V → Prop) (target : V)
    {a b : Option V} {xs : List (Option V)} (h : Route (AddIndicator D target) a xs b) :
    ∀ x, a = some x → ∃ y ys, b = some y ∧ xs = ys.map some ∧ Route D x ys y := by
  induction h with
  | nil a =>
      intro x ha
      exact ⟨x, [], ha, rfl, .nil x⟩
  | @cons a b c xs hab hbc ih =>
      intro x ha
      subst a
      cases b with
      | none => exact hab.elim
      | some z =>
          obtain ⟨y, ys, hc, hxs, hp⟩ := ih z rfl
          exact ⟨y, z :: ys, hc, congrArg (List.cons (some z)) hxs, .cons hab hp⟩

theorem add_indicator_acyclic {V : Type u} (D : V → V → Prop) (target : V)
    (hD : ∀ x xs, Route D x xs x → xs = []) (a : Option V) (xs : List (Option V))
    (h : Route (AddIndicator D target) a xs a) : xs = [] := by
  cases a with
  | none => exact (indicator_route_to_new D target h rfl).2
  | some x =>
      obtain ⟨y, ys, hxy, hxs, hp⟩ := indicator_old_route D target h x rfl
      have heq : x = y := Option.some.inj hxy
      subst y
      have hnil := hD x ys hp
      simpa only [hnil, List.map_nil] using hxs

theorem indicator_directed_exact {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (target : V) (a b : Option (Vertex G)) :
    Directed (indicatorGraph G target) a b ↔ AddIndicator (Arrow G) (.inl target) a b := by
  change ((AddIndicator (Arrow G) (.inl target) a b ∧ _ ∧ _) ∨
    (AddIndicator (Arrow G) (.inl target) b a ∧ _ ∧ _)) ↔ _
  simp

theorem indicator_dag_acyclic {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (hG : DirectedAcyclic G) (target : V) :
    DirectedAcyclic (indicatorGraph G target) := by
  intro a xs h
  have hp := h.map (fun z : Option (Vertex G) => z) (fun a b hab => (indicator_directed_exact G target a b).mp hab)
  have hp' : Route (AddIndicator (Arrow G) (.inl target)) a xs a := by
    simpa using hp
  exact add_indicator_acyclic (Arrow G) (.inl target) (root_expansion_acyclic G hG) a xs hp'

end RestrictedCausal.LatentRoots
