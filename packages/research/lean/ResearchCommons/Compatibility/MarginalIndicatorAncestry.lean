import SelectedMAGValidity

/- Pinned proof compatibility: type the SAME mapped route and expose actual
arrival fields/mark cases. Original source, selection, ancestry and mask
statements are unchanged. -/

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. Not elaborated or executed.

Original-DAG proof bodies for the marginal-indicator ancestry sandwich used
by Hou--Park--Li Proposition 3, Appendix F.8. This is a formalization of their
prior graphical argument, not a novelty claim or a faithfulness theorem.
Selection sinks and a genuinely exogenous sole-child indicator are retained.
The mask is NOT identified with ordinary ancestry in the selected case.
-/

namespace RestrictedCausal.IndicatorAncestry

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation GraphEquivalence
open SourceSelection (AncestorOf)

universe u v w

theorem selected_old {X : Type u} {S : Type v} {L : Type w}
    (a : SourceVertex X S L) : Selected (oldSource a) ↔ Selected a := by
  rcases a with ((x | s) | l) <;> exact Iff.rfl

theorem selected_empty_condition {X : Type u} {S : Type v} {L : Type w} :
    (Selected : SourceVertex X S L → Prop) = SelectedCondition (fun _ : X => False) := by
  funext a
  rcases a with ((x | s) | l) <;> rfl

theorem old_source_reach {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (a b : SourceVertex X S L) :
    Reach (arrowGraph (augmentSource D t).arrow) (oldSource a) (oldSource b) ↔
      Reach (arrowGraph D.arrow) a b := by
  constructor
  · rintro ⟨xs, hp⟩
    have raw : Route (AddIndicator D.arrow (Observed t))
        (sourceIndicatorEquiv (oldSource a)) (xs.map sourceIndicatorEquiv)
        (sourceIndicatorEquiv (oldSource b)) :=
      hp.map sourceIndicatorEquiv (fun x y hxy =>
        (arrow_directed_exact (augmentSource D t).arrow x y).mp hxy)
    have raw' : Route (AddIndicator D.arrow (Observed t)) (some a)
        (xs.map sourceIndicatorEquiv) (some b) := by
      simpa only [indicator_equiv_oldSource] using raw
    obtain ⟨z, zs, hz, _, hzs⟩ := indicator_old_route D.arrow (Observed t) raw' a rfl
    have hzb : b = z := Option.some.inj hz
    subst z
    exact ⟨_, hzs.map id (fun x y hxy => (arrow_directed_exact D.arrow x y).mpr hxy)⟩
  · rintro ⟨xs, hp⟩
    exact ⟨_, hp.map oldSource (fun x y hxy =>
      (old_source_marked_exact D t x y .tail .head).mp hxy)⟩

theorem selected_ancestor_old {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (a : SourceVertex X S L) :
    AncestorOf (arrowGraph (augmentSource D t).arrow) Selected (oldSource a) ↔
      AncestorOf (arrowGraph D.arrow) Selected a := by
  constructor
  · rintro ⟨z, hp, hs⟩
    rcases z with ((x | s) | l)
    · exact hs.elim
    · exact ⟨.inl (.inr s), (old_source_reach D t a _).mp hp, trivial⟩
    · exact hs.elim
  · rintro ⟨z, hp, hs⟩
    exact ⟨oldSource z, (old_source_reach D t a z).mpr hp, (selected_old z).mpr hs⟩

theorem old_selected_step {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (p q : Arrival (SourceVertex X S L))
    (h : RealStep (arrowGraph D.arrow) Selected p q) :
    RealStep (arrowGraph (augmentSource D t).arrow) Selected
      (mapArrival oldSource p) (mapArrival oldSource q) := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  refine ⟨outgoing, incoming, (old_source_marked_exact D t _ _ _ _).mp hedge, hmark, ?_⟩
  cases hm : p.incoming with
  | none => simpa only [mapArrival, hm] using hactive
  | some previous =>
      by_cases hc : previous = .head ∧ outgoing = .head
      · have ha : AncestorOf (arrowGraph D.arrow) Selected p.vertex := by
          simpa only [hm, ActiveAt, if_pos hc] using hactive
        simpa only [mapArrival, hm, ActiveAt, if_pos hc] using
          (selected_ancestor_old D t p.vertex).mpr ha
      · have hn : ¬ Selected p.vertex := by
          simpa only [hm, ActiveAt, if_neg hc] using hactive
        simpa only [mapArrival, hm, ActiveAt, if_neg hc] using
          (fun hs => hn ((selected_old p.vertex).mp hs))

/-- A route ready to receive the actual edge I_t -> t. It is not assumed
simple: subsequent physical loop reduction handles overlap and returns. -/
def HeadConnection {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x : X) : Prop :=
  ∃ last xs, Route (RealStep (arrowGraph D.arrow) Selected)
    ⟨Observed t, some .head⟩ xs ⟨Observed x, last⟩

/-- The exact marginal invariance-dependence mask, excluding the target's
own coordinate. This has a real sole-child indicator on the original source. -/
def MarginalMask {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x : X) : Prop :=
  t ≠ x ∧ ActiveConnection (arrowGraph (augmentSource D t).arrow) Selected
    (Observed none) (Observed (some x))

theorem head_connection_mask {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {t x : X} (hne : t ≠ x) (h : HeadConnection D t x) :
    MarginalMask D t x := by
  obtain ⟨last, xs, hp⟩ := h
  have lifted := hp.map (mapArrival oldSource) (old_selected_step D t)
  have «first» : RealStep (arrowGraph (augmentSource D t).arrow) Selected
      ⟨Observed none, none⟩ ⟨Observed (some t), some .head⟩ := by
    exact ⟨.tail, .head, (indicator_raw_edge D t _ _ _).mpr ⟨rfl, rfl, rfl⟩, rfl, trivial⟩
  have whole := Route.cons «first» lifted
  obtain ⟨r, ys, hy, hvertex, hnd⟩ := ActiveWalkReduction.active_walk_to_simple
    (arrowGraph (augmentSource D t).arrow) (original_arrow_mixed_laws (augmentSource D t))
    Selected whole
  have heq : r = ⟨Observed (some x), r.incoming⟩ := Arrival.eq_of_fields hvertex rfl
  rw [heq] at hy
  exact ⟨hne, r.incoming, ys, hy, hnd⟩

theorem directed_selected_route {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {a b : SourceVertex X S L} {xs : List (SourceVertex X S L)}
    (h : Route D.arrow a xs b) (incoming : Option Mark) :
    ∃ last ys, Route (RealStep (arrowGraph D.arrow) Selected)
      ⟨a, incoming⟩ ys ⟨b, last⟩ := by
  revert incoming
  induction h with
  | nil a => intro incoming; exact ⟨incoming, [], .nil _⟩
  | @cons a «next» b rest hedge hrest ih =>
      intro incoming
      have hn : ¬ Selected a := by
        intro hs
        rcases a with ((x | s) | l)
        · exact hs.elim
        · exact D.selection_sink s «next» hedge
        · exact hs.elim
      obtain ⟨last, ys, hy⟩ := ih (some .head)
      refine ⟨last, ⟨«next», some .head⟩ :: ys, .cons ?_ hy⟩
      refine ⟨.tail, .head, Or.inl ⟨hedge, rfl, rfl⟩, rfl, ?_⟩
      cases incoming with
      | none => trivial
      | some previous => simpa [ActiveAt] using hn

theorem ordinary_ancestor_mask {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {t x : X} (hne : t ≠ x)
    (h : Reach (arrowGraph D.arrow) (Observed t) (Observed x)) : MarginalMask D t x := by
  obtain ⟨xs, hp⟩ := h
  have raw := hp.map id (fun a b hab => (arrow_directed_exact D.arrow a b).mp hab)
  exact head_connection_mask D hne (directed_selected_route D raw (some .head))

def OneEndpointSelection {X : Type u} {S : Type v} {L : Type w} (x : X)
    (a : SourceVertex X S L) : Prop := a = Observed x ∨ Selected a

/-- The upper inclusion is derived from the actual first edge and head
propagation, not from identifying this mask with ordinary ancestors. -/
theorem mask_ancestor_endpoint_or_selection {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {t x : X} (h : MarginalMask D t x) :
    AncestorOf (arrowGraph D.arrow) (OneEndpointSelection x) (Observed t) := by
  classical
  obtain ⟨_, last, xs, hp, _⟩ := h
  let E := augmentSource D t
  let A := AncestorOf (arrowGraph E.arrow) (OneEndpointSelection (some x))
  have hBA : ∀ v, AncestorOf (arrowGraph E.arrow) Selected v → A v := by
    exact fun _ hv => ancestor_mono (fun _ hs => Or.inr hs) hv
  have hend : A (Observed (some x)) :=
    ⟨Observed (some x), ⟨[], .nil _⟩, Or.inl rfl⟩
  have htarget : A (Observed (some t)) := by
    cases xs with
    | nil => cases hp
    | cons «next» rest =>
      cases hp with
      | cons hstep hrest =>
        obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hstep
        obtain ⟨hvertex, _, hincoming⟩ := (indicator_raw_edge D t _ _ _).mp hedge
        by_contra hn
        have hnext : ¬ A «next».vertex := by simpa only [hvertex] using hn
        have hhead : «next».incoming = some .head := hmark.trans (congrArg some hincoming)
        exact (head_nonancestor_general (arrowGraph E.arrow) (original_arrow_mixed_laws E)
          Selected (AncestorOf (arrowGraph E.arrow) Selected) A hBA
          (ancestor_backward_closed (arrowGraph E.arrow) (OneEndpointSelection (some x)))
          hrest hhead hnext).2 hend
  obtain ⟨z, hpz, hz⟩ := htarget
  rcases hz with hzx | hzs
  · subst z
    exact ⟨Observed x, (old_source_reach D t _ _).mp hpz, Or.inl rfl⟩
  · rcases z with ((y | s) | l)
    · exact hzs.elim
    · exact ⟨.inl (.inr s), (old_source_reach D t _ _).mp hpz, Or.inr trivial⟩
    · exact hzs.elim

end RestrictedCausal.IndicatorAncestry
