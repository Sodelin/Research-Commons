import FiniteOriginalTargetImage
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.OfMap

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Finite graph decision components for E3. Bounds are proved from finite route
erasure, not supplied hidden-size bounds. Computational definitions receive
an actual finite vertex enumeration and decidable input edge/conditioning
predicates. This does not yet replace the noncomputable full-profile registry
encoding or establish the optimized query certificate.
-/

namespace RestrictedCausal.FiniteGraphDecision

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open SourceSelection (AncestorOf)

universe u

def BoundedRoute {V : Type u} (R : V → V → Prop) : Nat → V → V → Prop
  | 0, a, b => a = b
  | n + 1, a, b => a = b ∨ ∃ c, R a c ∧ BoundedRoute R n c b

def boundedDecision {V : Type u} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] :
    ∀ n a b, Decidable (BoundedRoute R n a b)
  | 0, a, b => inferInstanceAs (Decidable (a = b))
  | n + 1, a, b => by
      letI : DecidablePred (fun c => BoundedRoute R n c b) := fun c => boundedDecision R n c b
      change Decidable (a = b ∨ ∃ c, R a c ∧ BoundedRoute R n c b)
      infer_instance

theorem bounded_to_route {V : Type u} {R : V → V → Prop} {n : Nat} {a b : V}
    (h : BoundedRoute R n a b) : ∃ xs, SelectedWalk.Route R a xs b ∧ xs.length ≤ n := by
  induction n generalizing a with
  | zero =>
      change a = b at h
      subst b
      exact ⟨[], .nil _, Nat.le_refl 0⟩
  | succ n ih =>
      rcases h with heq | ⟨c, hac, hcb⟩
      · subst b
        exact ⟨[], .nil _, Nat.zero_le _⟩
      · obtain ⟨xs, hp, hlen⟩ := ih hcb
        exact ⟨c :: xs, .cons hac hp, Nat.succ_le_succ hlen⟩

theorem route_to_bounded {V : Type u} {R : V → V → Prop} {a b : V} {xs : List V}
    (h : SelectedWalk.Route R a xs b) (n : Nat) (hlen : xs.length ≤ n) : BoundedRoute R n a b := by
  revert hlen
  revert n
  induction h with
  | nil a =>
      intro n _
      cases n with
      | zero => rfl
      | succ n => exact Or.inl rfl
  | cons hedge htail ih =>
      intro n hlen
      cases n with
      | zero => simp only [List.length_cons] at hlen; omega
      | succ n =>
          exact Or.inr ⟨_, hedge, ih n (Nat.le_of_succ_le_succ hlen)⟩

/-- The finite bound is on an actual simple subroute, and is derived for
every finite vertex type, including an arbitrarily large original source. -/
theorem bounded_iff_route {V : Type u} [Fintype V] (R : V → V → Prop) (a b : V) :
    BoundedRoute R (Fintype.card V) a b ↔ ∃ xs, SelectedWalk.Route R a xs b := by
  constructor
  · intro h
    obtain ⟨xs, hp, _⟩ := bounded_to_route h
    exact ⟨xs, hp⟩
  · rintro ⟨xs, hp⟩
    obtain ⟨ys, hy, hnd, _⟩ := hp.exists_simple_subroute
    have hcard := hnd.length_le_card
    have hlen : ys.length ≤ Fintype.card V := by
      simp only [List.length_cons] at hcard
      omega
    exact route_to_bounded hy _ hlen

def routeDecision {V : Type u} [Fintype V] [DecidableEq V]
    (R : V → V → Prop) [DecidableRel R] (a b : V) :
    Decidable (∃ xs, SelectedWalk.Route R a xs b) :=
  match boundedDecision R (Fintype.card V) a b with
  | .isTrue h => .isTrue ((bounded_iff_route R a b).mp h)
  | .isFalse h => .isFalse (fun hp => h ((bounded_iff_route R a b).mpr hp))

def arrivalEquiv {V : Type u} : Arrival V ≃ V × Option Mark where
  toFun p := (p.vertex, p.incoming)
  invFun p := ⟨p.1, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

instance arrivalFintype {V : Type u} [Fintype V] : Fintype (Arrival V) :=
  Fintype.ofEquiv (V × Option Mark) arrivalEquiv.symm

instance arrivalDecidableEq {V : Type u} [DecidableEq V] : DecidableEq (Arrival V) :=
  fun p q =>
    if hv : p.vertex = q.vertex then
      if hm : p.incoming = q.incoming then
        .isTrue (Arrival.eq_of_fields hv hm)
      else .isFalse (fun heq => hm (congrArg Arrival.incoming heq))
    else .isFalse (fun heq => hv (congrArg Arrival.vertex heq))

def reachDecision {V : Type u} [Fintype V] [DecidableEq V]
    (G : MarkedGraph V) (edgeDecision : ∀ a b ma mb, Decidable (G.edge a b ma mb))
    (a b : V) : Decidable (Reach G a b) := by
  letI : DecidableRel (Directed G) := fun a b => edgeDecision a b .tail .head
  exact routeDecision (Directed G) a b

def ancestorDecision {V : Type u} [Fintype V] [DecidableEq V]
    (G : MarkedGraph V) (edgeDecision : ∀ a b ma mb, Decidable (G.edge a b ma mb))
    (C : V → Prop) (conditionDecision : DecidablePred C) (a : V) : Decidable (AncestorOf G C a) := by
  letI : DecidableRel (Reach G) := reachDecision G edgeDecision
  letI : DecidablePred C := conditionDecision
  change Decidable (∃ b, Reach G a b ∧ C b)
  infer_instance

def transitionDecision {V : Type u} [Fintype V] [DecidableEq V]
    (G : MarkedGraph V) (edgeDecision : ∀ a b ma mb, Decidable (G.edge a b ma mb))
    (C : V → Prop) (conditionDecision : DecidablePred C) (p q : Arrival V) :
    Decidable (RealStep G C p q) := by
  letI : ∀ a b ma mb, Decidable (G.edge a b ma mb) := edgeDecision
  letI : DecidablePred C := conditionDecision
  letI : DecidablePred (AncestorOf G C) := ancestorDecision G edgeDecision C conditionDecision
  unfold RealStep Transition
  cases p.incoming <;> dsimp [ActiveAt] <;> infer_instance

def FiniteActiveTest {V : Type u} [Fintype V] (G : MarkedGraph V) (C : V → Prop)
    (x y : V) : Prop :=
  ∃ last : Option Mark, BoundedRoute (RealStep G C) (Fintype.card (Arrival V))
    ⟨x, none⟩ ⟨y, last⟩

theorem finite_active_iff {V : Type u} [Fintype V] (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) (x y : V) : FiniteActiveTest G C x y ↔ ActiveConnection G C x y := by
  constructor
  · rintro ⟨last, hb⟩
    obtain ⟨xs, hp⟩ := (bounded_iff_route (RealStep G C) ⟨x, none⟩ ⟨y, last⟩).mp hb
    obtain ⟨r, zs, hz, hv, hnd⟩ := ActiveWalkReduction.active_walk_to_simple G laws C hp
    have heq : r = ⟨y, r.incoming⟩ := Arrival.eq_of_fields hv rfl
    rw [heq] at hz
    exact ⟨r.incoming, zs, hz, hnd⟩
  · rintro ⟨last, xs, hp, _⟩
    exact ⟨last, (bounded_iff_route (RealStep G C) ⟨x, none⟩ ⟨y, last⟩).mpr ⟨xs, hp⟩⟩

/-- A terminating source-level decision procedure for the actual selected
active-path predicate in a finite DAG (or a no-tail-tail mixed graph with the
stated laws), not an oracle placeholder. It has not been executed. -/
def activeDecision {V : Type u} [Fintype V] [DecidableEq V]
    (G : MarkedGraph V) (laws : MixedLaws G)
    (edgeDecision : ∀ a b ma mb, Decidable (G.edge a b ma mb))
    (C : V → Prop) (conditionDecision : DecidablePred C) (x y : V) :
    Decidable (ActiveConnection G C x y) := by
  letI : DecidableRel (RealStep G C) := transitionDecision G edgeDecision C conditionDecision
  letI : DecidablePred (fun last : Option Mark =>
      BoundedRoute (RealStep G C) (Fintype.card (Arrival V)) ⟨x, none⟩ ⟨y, last⟩) :=
    fun last => boundedDecision (RealStep G C) _ _ _
  have test : Decidable (FiniteActiveTest G C x y) := inferInstanceAs (Decidable (∃ last : Option Mark,
    BoundedRoute (RealStep G C) (Fintype.card (Arrival V)) ⟨x, none⟩ ⟨y, last⟩))
  exact match test with
    | .isTrue h => .isTrue ((finite_active_iff G laws C x y).mp h)
    | .isFalse h => .isFalse (fun hp => h ((finite_active_iff G laws C x y).mpr hp))

end RestrictedCausal.FiniteGraphDecision
