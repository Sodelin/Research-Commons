import PartialObservedQueryFamily
import FiniteOriginalTargetImage

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Prior HPL Proposition 3(3), with its source-level omitted details exposed.
The root-free suffix is pulled back into the SAME original DAG. The proof
does not replace a separate indicator by an independently realizable graph,
or assume that adding an indicator preserves arbitrary root-containing paths.
-/

namespace RestrictedCausal.RefinedIndicator

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation IndicatorAncestry RefinedSeparator GraphEquivalence
open FiniteTargetImage
open SourceSelection (AncestorOf)

universe u v w

def forgetIndicator {X : Type u} {S : Type v} {L : Type w} (t : X)
    (a : SourceVertex (Option X) S L) : SourceVertex X S L :=
  match sourceIndicatorEquiv a with
  | none => Observed t
  | some v => v

theorem forget_old {X : Type u} {S : Type v} {L : Type w}
    (t : X) (a : SourceVertex X S L) : forgetIndicator t (oldSource a) = a := by
  simp only [forgetIndicator, indicator_equiv_oldSource]

theorem old_forget_nonroot {X : Type u} {S : Type v} {L : Type w}
    (t : X) (a : SourceVertex (Option X) S L) (ha : a ≠ Observed none) :
    oldSource (forgetIndicator t a) = a := by
  rcases a with ((x | s) | l)
  · cases x with
    | none => exact (ha rfl).elim
    | some x => rfl
  · rfl
  · rfl

theorem old_condition {X : Type u} {S : Type v} {L : Type w}
    (Z : X → Prop) (a : SourceVertex X S L) :
    SelectedCondition (InvarianceCondition Z) (oldSource a) ↔ SelectedCondition Z a := by
  rcases a with ((x | s) | l) <;> exact Iff.rfl

theorem old_condition_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (Z : X → Prop) (a : SourceVertex X S L) :
    AncestorOf (arrowGraph (augmentSource D t).arrow)
      (SelectedCondition (InvarianceCondition Z)) (oldSource a) ↔
    AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) a := by
  constructor
  · rintro ⟨z, hp, hc⟩
    rcases z with ((x | s) | l)
    · cases x with
      | none => exact hc.elim
      | some x => exact ⟨Observed x, (old_source_reach D t a _).mp hp, hc⟩
    · exact ⟨.inl (.inr s), (old_source_reach D t a _).mp hp, trivial⟩
    · exact hc.elim
  · rintro ⟨z, hp, hc⟩
    exact ⟨oldSource z, (old_source_reach D t a z).mpr hp, (old_condition Z z).mpr hc⟩

theorem old_not_ancestor_root {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (a : SourceVertex X S L) :
    ¬ Reach (arrowGraph (augmentSource D t).arrow) (oldSource a) (Observed none) := by
  rintro ⟨xs, hp⟩
  have raw := hp.map sourceIndicatorEquiv (fun x y hxy =>
    (arrow_directed_exact (augmentSource D t).arrow x y).mp hxy)
  have raw' : Route (AddIndicator D.arrow (Observed t)) (some a)
      (xs.map sourceIndicatorEquiv) none := by
    simpa only [indicator_equiv_oldSource, sourceIndicatorEquiv] using raw
  have hbad := (indicator_route_to_new D.arrow (Observed t) raw' rfl).1
  exact Option.noConfusion hbad

theorem old_endpoint_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x : X) (a : SourceVertex X S L) :
    EndpointAncestor (augmentSource D t) none (some x) (oldSource a) ↔
      AncestorOf (arrowGraph D.arrow) (OneEndpointSelection x) a := by
  constructor
  · rintro ⟨z, hp, hz⟩
    rcases hz with hroot | hx | hs
    · subst z
      exact (old_not_ancestor_root D t a hp).elim
    · subst z
      exact ⟨Observed x, (old_source_reach D t a _).mp hp, Or.inl rfl⟩
    · rcases z with ((y | s) | l)
      · exact hs.elim
      · exact ⟨.inl (.inr s), (old_source_reach D t a _).mp hp, Or.inr trivial⟩
      · exact hs.elim
  · rintro ⟨z, hp, hz⟩
    refine ⟨oldSource z, (old_source_reach D t a z).mpr hp, ?_⟩
    rcases hz with hx | hs
    · subst z
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ((selected_old z).mpr hs))

theorem root_free_step_pulls_back {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (Z : X → Prop)
    (p q : Arrival (SourceVertex (Option X) S L))
    (hp : p.vertex ≠ Observed none) (hq : q.vertex ≠ Observed none)
    (h : RealStep (arrowGraph (augmentSource D t).arrow)
      (SelectedCondition (InvarianceCondition Z)) p q) :
    RealStep (arrowGraph D.arrow) (SelectedCondition Z)
      (mapArrival (forgetIndicator t) p) (mapArrival (forgetIndicator t) q) := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  have he : (arrowGraph D.arrow).edge (forgetIndicator t p.vertex)
      (forgetIndicator t q.vertex) outgoing incoming := by
    apply (old_source_marked_exact D t _ _ _ _).mpr
    simpa only [old_forget_nonroot t p.vertex hp, old_forget_nonroot t q.vertex hq] using hedge
  refine ⟨outgoing, incoming, he, hmark, ?_⟩
  cases hm : p.incoming with
  | none => trivial
  | some previous =>
      by_cases hc : previous = .head ∧ outgoing = .head
      · have ha : AncestorOf (arrowGraph (augmentSource D t).arrow)
            (SelectedCondition (InvarianceCondition Z)) p.vertex := by
          simpa only [hm, ActiveAt, if_pos hc] using hactive
        have ha' := (old_condition_ancestor D t Z (forgetIndicator t p.vertex)).mp
          (by simpa only [old_forget_nonroot t p.vertex hp] using ha)
        simpa only [mapArrival, ActiveAt, if_pos hc] using ha'
      · have hn : ¬ SelectedCondition (InvarianceCondition Z) p.vertex := by
          simpa only [hm, ActiveAt, if_neg hc] using hactive
        have hn' : ¬ SelectedCondition Z (forgetIndicator t p.vertex) := by
          intro h
          have old := (old_condition Z (forgetIndicator t p.vertex)).mpr h
          exact hn (by simpa only [old_forget_nonroot t p.vertex hp] using old)
        simpa only [mapArrival, ActiveAt, if_neg hc] using hn'

/-- Root absence is checked on the complete suffix, including its endpoint.
This premise follows from the global simple path's first-vertex exclusion. -/
theorem root_free_route_pulls_back {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (Z : X → Prop)
    {p q : Arrival (SourceVertex (Option X) S L)} {xs : List (Arrival (SourceVertex (Option X) S L))}
    (h : Route (RealStep (arrowGraph (augmentSource D t).arrow)
      (SelectedCondition (InvarianceCondition Z))) p xs q)
    (hfree : ∀ r ∈ p :: xs, r.vertex ≠ Observed none) :
    Route (RealStep (arrowGraph D.arrow) (SelectedCondition Z))
      (mapArrival (forgetIndicator t) p) (xs.map (mapArrival (forgetIndicator t)))
      (mapArrival (forgetIndicator t) q) := by
  revert hfree
  induction h with
  | nil p => intro _; exact .nil _
  | @cons p next q rest hstep hrest ih =>
      intro hfree
      refine .cons (root_free_step_pulls_back D t Z p next
        (hfree p List.mem_cons_self) (hfree next (List.mem_cons_of_mem _ List.mem_cons_self)) hstep)
        (ih ?_)
      intro r hr
      exact hfree r (List.mem_cons_of_mem _ hr)

theorem one_endpoint_to_pair {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x : X) (a : SourceVertex X S L)
    (ha : AncestorOf (arrowGraph D.arrow) (OneEndpointSelection x) a) :
    EndpointAncestor D x x a := by
  apply ancestor_mono (C := OneEndpointSelection x) (fun v hv => ?_) ha
  rcases hv with hx | hs
  · exact Or.inl hx
  · exact Or.inr (Or.inr hs)

theorem indicator_suffix_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x : X) (Z : X → Prop)
    (upper : ∀ z, Z z → AncestorOf (arrowGraph D.arrow) (OneEndpointSelection x) (Observed z))
    (lower : ∀ z, z ≠ x → MarginalMask D z x → Z z)
    {p q : Arrival (SourceVertex (Option X) S L)} {xs : List (Arrival (SourceVertex (Option X) S L))}
    (h : Route (RealStep (arrowGraph (augmentSource D t).arrow)
      (SelectedCondition (InvarianceCondition Z))) p xs q)
    (hq : q.vertex = Observed (some x)) (hnd : ((p :: xs).map Arrival.vertex).Nodup)
    (hfirst : Observed none ∉ (p :: xs).map Arrival.vertex)
    (hsupport : ∀ r ∈ p :: xs, EndpointAncestor (augmentSource D t) none (some x) r.vertex) :
    Route (Transition (arrowGraph (augmentSource D t).arrow) Nonlatent
      (EndpointAncestor (augmentSource D t) none (some x))) p xs q := by
  have upperAug : ∀ z, InvarianceCondition Z z →
      EndpointAncestor (augmentSource D t) none (some x) (Observed z) := by
    intro z hz
    cases z with
    | none => exact hz.elim
    | some z => exact (old_endpoint_ancestor D t x (Observed z)).mpr (upper z hz)
  revert hnd hfirst hsupport
  revert hq
  induction h with
  | nil p => intro _ _ _ _; exact .nil p
  | @cons p next q rest hstep hrest ih =>
      intro hq hnd hfirst hsupport
      have hnotTail := (List.nodup_cons.mp hnd).1
      have htailNd := (List.nodup_cons.mp hnd).2
      have hfree : ∀ r ∈ p :: next :: rest, r.vertex ≠ Observed none := by
        intro r hr heq
        exact hfirst (List.mem_map.mpr ⟨r, hr, heq⟩)
      have hpx : p.vertex ≠ Observed (some x) := by
        intro heq
        exact hnotTail (List.mem_map.mpr ⟨q, Route.end_mem hrest, hq.trans heq.symm⟩)
      have newstep : Transition (arrowGraph (augmentSource D t).arrow) Nonlatent
          (EndpointAncestor (augmentSource D t) none (some x)) p next := by
        obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
        refine ⟨outgoing, incoming, hedge, hmark, ?_⟩
        cases hm : p.incoming with
        | none => trivial
        | some previous =>
            by_cases hc : previous = .head ∧ outgoing = .head
            · have ha : AncestorOf (arrowGraph (augmentSource D t).arrow)
                  (SelectedCondition (InvarianceCondition Z)) p.vertex := by
                simpa only [hm, ActiveAt, if_pos hc] using hactive
              simpa only [ActiveAt, if_pos hc] using colliders_in_endpoint_ancestry
                (augmentSource D t) none (some x) (InvarianceCondition Z) upperAug _ ha
            · have hn : ¬ SelectedCondition (InvarianceCondition Z) p.vertex := by
                simpa only [hm, ActiveAt, if_neg hc] using hactive
              have hnonlatent : ¬ Nonlatent p.vertex := by
                intro hret
                rcases hv : p.vertex with ((z | s) | l)
                · cases z with
                  | none => exact hfree p List.mem_cons_self hv
                  | some z =>
                      have hzx : z ≠ x := fun hz =>
                        hpx (hv.trans (congrArg (fun v => Observed (some v)) hz))
                      have oldroute := root_free_route_pulls_back D t Z
                        (.cons ⟨outgoing, incoming, hedge, hmark, hactive⟩ hrest) hfree
                      have hpOld : (mapArrival (forgetIndicator t) p).vertex = Observed z := by
                        simp only [mapArrival, hv, forgetIndicator, sourceIndicatorEquiv]
                      have hqOld : (mapArrival (forgetIndicator t) q).vertex = Observed x := by
                        simp only [mapArrival, hq, forgetIndicator, sourceIndicatorEquiv]
                      have haOld : AncestorOf (arrowGraph D.arrow) (OneEndpointSelection x)
                          (Observed z) := (old_endpoint_ancestor D t x (Observed z)).mp
                        (by simpa only [hv] using hsupport p List.mem_cons_self)
                      have hmask := ancestral_suffix_forces_mask D x x z Z
                        (fun z hz => one_endpoint_to_pair D x _ (upper z hz)) hzx hzx
                        oldroute hpOld hqOld (by
                          simpa only [hpOld] using one_endpoint_to_pair D x _ haOld)
                      apply hn
                      rw [hv]
                      exact lower z hzx (hmask.elim id id)
                · apply hn
                  rw [hv]
                  trivial
                · simpa only [hv, Nonlatent] using hret
              simpa only [ActiveAt, if_neg hc] using hnonlatent
      refine .cons newstep (ih hq htailNd ?_ ?_)
      · intro hm
        exact hfirst (List.mem_cons_of_mem _ hm)
      · intro r hr
        exact hsupport r (List.mem_cons_of_mem _ hr)

/-- The exact refined indicator separator. Root and observed endpoints are
not conditioned. Every old observed coordinate, including untargeted ones,
remains in the source and in the permitted conditioning family. -/
theorem refined_indicator_separator {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x : X) (Z : X → Prop) (hx : ¬ Z x)
    (upper : ∀ z, Z z → AncestorOf (arrowGraph D.arrow) (OneEndpointSelection x) (Observed z))
    (lower : ∀ z, z ≠ x → MarginalMask D z x → Z z) :
    InducingPath (augmentSource D t) none (some x) ↔
      ActiveConnection (arrowGraph (augmentSource D t).arrow)
        (SelectedCondition (InvarianceCondition Z)) (Observed none) (Observed (some x)) := by
  constructor
  · intro h
    exact (inducing_implies_inseparable (augmentSource D t) none (some x) h).2
      (InvarianceCondition Z) (fun h => h.elim) hx
  · rintro ⟨last, xs, hp, hnd⟩
    have upperAug : ∀ z, InvarianceCondition Z z →
        EndpointAncestor (augmentSource D t) none (some x) (Observed z) := by
      intro z hz
      cases z with
      | none => exact hz.elim
      | some z => exact (old_endpoint_ancestor D t x (Observed z)).mpr (upper z hz)
    have hsupport := route_ancestral_support
      (arrowGraph (augmentSource D t).arrow) (original_arrow_mixed_laws (augmentSource D t))
      (SelectedCondition (InvarianceCondition Z))
      (AncestorOf (arrowGraph (augmentSource D t).arrow) (SelectedCondition (InvarianceCondition Z)))
      (EndpointAncestor (augmentSource D t) none (some x))
      (colliders_in_endpoint_ancestry (augmentSource D t) none (some x)
        (InvarianceCondition Z) upperAug)
      (ancestor_backward_closed (arrowGraph (augmentSource D t).arrow)
        (EndpointSelection none (some x))) hp
      ⟨Observed none, ⟨[], .nil _⟩, Or.inl rfl⟩
      ⟨Observed (some x), ⟨[], .nil _⟩, Or.inr (Or.inl rfl)⟩
    refine ⟨(fun h => Option.noConfusion h), last, xs, ?_, hnd⟩
    cases xs with
    | nil => cases hp
    | cons next rest =>
      cases hp with
      | cons hstep hrest =>
        obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hstep
        refine .cons ⟨outgoing, incoming, hedge, hmark, trivial⟩
          (indicator_suffix_inducing D t x Z upper lower hrest rfl
            (List.nodup_cons.mp hnd).2 (List.nodup_cons.mp hnd).1 ?_)
        intro r hr
        exact hsupport r (List.mem_cons_of_mem _ hr)

end RestrictedCausal.RefinedIndicator
