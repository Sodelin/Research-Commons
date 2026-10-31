import CanonicalLatentRoots
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sym.Card
import Mathlib.Order.Basic

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. Not elaborated or executed.
Exact finite canonical selector and hidden-root count bounds. The original
source remains arbitrary; only the constructed representative is bounded.
-/

namespace RestrictedCausal.SelectedWalk

instance : Fintype Mark where
  elems := {.tail, .head}
  complete := by intro m; cases m <;> simp

theorem card_mark : Fintype.card Mark = 2 := rfl

end RestrictedCausal.SelectedWalk

namespace RestrictedCausal.CanonicalSelection

open SelectedWalk

universe u

abbrev OrderedPair (X : Type u) [LinearOrder X] := {p : X × X // p.1 < p.2}

theorem card_orderedPair (X : Type u) [LinearOrder X] [Fintype X] :
    Fintype.card (OrderedPair X) = (Fintype.card X).choose 2 := by
  rw [Fintype.card_subtype]
  exact Fintype.card_product_filter_lt

def bridgeEncoding {X : Type u} [LinearOrder X] (Q : Profile X)
    (b : BridgeToken Q) : OrderedPair X × Mark × Mark :=
  (⟨(b.left, b.right), b.ordered⟩, b.leftMark, b.rightMark)

theorem bridgeEncoding_injective {X : Type u} [LinearOrder X] (Q : Profile X) :
    Function.Injective (bridgeEncoding Q) := by
  intro a b h
  have hl := congrArg (fun p : OrderedPair X × Mark × Mark => p.1.val.1) h
  have hr := congrArg (fun p : OrderedPair X × Mark × Mark => p.1.val.2) h
  have hml := congrArg (fun p : OrderedPair X × Mark × Mark => p.2.1) h
  have hmr := congrArg (fun p : OrderedPair X × Mark × Mark => p.2.2) h
  cases a
  cases b
  cases hl
  cases hr
  cases hml
  cases hmr
  rfl

noncomputable instance bridgeTokenFintype {X : Type u} [LinearOrder X] [Fintype X]
    (Q : Profile X) : Fintype (BridgeToken Q) :=
  Fintype.ofInjective (bridgeEncoding Q) (bridgeEncoding_injective Q)

noncomputable instance selectorFintype {X : Type u} [LinearOrder X] [Fintype X]
    (Q : Profile X) : Fintype (Selector Q) := by
  classical
  infer_instance

theorem bridge_card_bound {X : Type u} [LinearOrder X] [Fintype X]
    (Q : Profile X) : Fintype.card (BridgeToken Q) ≤ 4 * (Fintype.card X).choose 2 := by
  have h := Fintype.card_le_of_injective (bridgeEncoding Q) (bridgeEncoding_injective Q)
  simp only [Fintype.card_prod, card_orderedPair, card_mark] at h
  omega

theorem selector_card_bound {X : Type u} [LinearOrder X] [Fintype X]
    (Q : Profile X) :
    Fintype.card (Selector Q) ≤ Fintype.card X + 4 * (Fintype.card X).choose 2 := by
  classical
  change Fintype.card (Sum {x : X // Q.parent x} (BridgeToken Q)) ≤ _
  rw [Fintype.card_sum]
  exact Nat.add_le_add (Fintype.card_subtype_le Q.parent) (bridge_card_bound Q)

/-- A fixed order exists on the finite canonical retained vertex set. It only
chooses one root label per unordered edge and does not change graph semantics. -/
noncomputable def canonicalVertexOrder {X : Type u} [LinearOrder X] [Fintype X]
    (Q : Profile X) : LinearOrder (Vertex Q) :=
  LinearOrder.lift' (Fintype.equivFin (Vertex Q)) (Fintype.equivFin (Vertex Q)).injective

end RestrictedCausal.CanonicalSelection

namespace RestrictedCausal.LatentRoots

open SelectedWalk CanonicalSelection

universe u

def rootEncoding {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (r : Root G) : OrderedPair V := ⟨(r.left, r.right), r.ordered⟩

theorem rootEncoding_injective {V : Type u} [LinearOrder V] (G : MarkedGraph V) :
    Function.Injective (rootEncoding G) := by
  intro a b h
  have hl := congrArg (fun p : OrderedPair V => p.val.1) h
  have hr := congrArg (fun p : OrderedPair V => p.val.2) h
  cases a
  cases b
  cases hl
  cases hr
  rfl

noncomputable instance rootFintype {V : Type u} [LinearOrder V] [Fintype V]
    (G : MarkedGraph V) : Fintype (Root G) :=
  Fintype.ofInjective (rootEncoding G) (rootEncoding_injective G)

theorem root_pair_injective {V : Type u} [LinearOrder V] (G : MarkedGraph V) :
    Function.Injective (fun r : Root G => s(r.left, r.right)) := by
  intro a b h
  rcases Sym2.eq_iff.mp h with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · apply rootEncoding_injective G
    apply Subtype.ext
    exact Prod.ext hl hr
  · have hb := b.ordered
    rw [← hr, ← hl] at hb
    exact (lt_asymm a.ordered hb).elim

/-- Every canonical bidirected edge is either observed-observed, or belongs
to one of the two incidences of a marked-pair selector. Singleton selectors
have only a tail incidence and contribute no hidden root. -/
abbrev CanonicalRootTag {X : Type u} [LinearOrder X] (Q : Profile X) :=
  Sum {p : Sym2 X // ¬ p.IsDiag} (BridgeToken Q × Mark)

def rootTagVertices {X : Type u} [LinearOrder X] (Q : Profile X) :
    CanonicalRootTag Q → Sym2 (CanonicalSelection.Vertex Q)
  | .inl p => Sym2.map Sum.inl p.val
  | .inr (b, .tail) => s(Sum.inl b.left, Sum.inr (Sum.inr b))
  | .inr (b, .head) => s(Sum.inl b.right, Sum.inr (Sum.inr b))

theorem canonical_root_has_tag {X : Type u} [LinearOrder X] (Q : Profile X)
    [LinearOrder (CanonicalSelection.Vertex Q)]
    (r : Root (SourceSelection.graph (SourceSelection.canonical Q))) :
    ∃ tag : CanonicalRootTag Q, rootTagVertices Q tag = s(r.left, r.right) := by
  rcases r with ⟨a, b, hord, hedge⟩
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          have hne : x ≠ y := by
            intro heq
            subst y
            exact (lt_irrefl _ hord)
          exact ⟨.inl ⟨s(x, y), hne⟩, rfl⟩
      | inr sel =>
          cases sel with
          | inl p => exact (Mark.noConfusion hedge.1.2)
          | inr bridge =>
              rcases hedge.1 with ⟨hx, _⟩ | ⟨hx, _⟩
              · subst x
                exact ⟨.inr (bridge, .tail), rfl⟩
              · subst x
                exact ⟨.inr (bridge, .head), rfl⟩
  | inr sel =>
      cases b with
      | inl y =>
          cases sel with
          | inl p => exact (Mark.noConfusion hedge.1.2)
          | inr bridge =>
              rcases hedge.1 with ⟨hy, _⟩ | ⟨hy, _⟩
              · subst y
                exact ⟨.inr (bridge, .tail), Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩
              · subst y
                exact ⟨.inr (bridge, .head), Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩
      | inr other => exact hedge.1.elim

noncomputable def canonicalRootEncoding {X : Type u} [LinearOrder X] (Q : Profile X)
    [LinearOrder (CanonicalSelection.Vertex Q)]
    (r : Root (SourceSelection.graph (SourceSelection.canonical Q))) : CanonicalRootTag Q :=
  Classical.choose (canonical_root_has_tag Q r)

theorem canonicalRootEncoding_injective {X : Type u} [LinearOrder X] (Q : Profile X)
    [LinearOrder (CanonicalSelection.Vertex Q)] :
    Function.Injective (canonicalRootEncoding Q) := by
  intro a b h
  apply root_pair_injective (SourceSelection.graph (SourceSelection.canonical Q))
  have ha := Classical.choose_spec (canonical_root_has_tag Q a)
  have hb := Classical.choose_spec (canonical_root_has_tag Q b)
  exact ha.symm.trans ((congrArg (rootTagVertices Q) h).trans hb)

/-- Exact advertised O(n²) representative bound, not the weaker choose(n+s,2).
It counts hidden roots of the one constructed source, not original confounders. -/
theorem canonical_hidden_root_bound {X : Type u} [LinearOrder X] [Fintype X]
    (Q : Profile X) [LinearOrder (CanonicalSelection.Vertex Q)] :
    Fintype.card (Root (SourceSelection.graph (SourceSelection.canonical Q))) ≤
      9 * (Fintype.card X).choose 2 := by
  classical
  have h := Fintype.card_le_of_injective (canonicalRootEncoding Q)
    (canonicalRootEncoding_injective Q)
  change Fintype.card (Root (SourceSelection.graph (SourceSelection.canonical Q))) ≤
    Fintype.card (Sum {p : Sym2 X // ¬ p.IsDiag} (BridgeToken Q × Mark)) at h
  rw [Fintype.card_sum, Fintype.card_prod, Sym2.card_subtype_not_diag, card_mark] at h
  have hb := bridge_card_bound Q
  omega

end RestrictedCausal.LatentRoots
