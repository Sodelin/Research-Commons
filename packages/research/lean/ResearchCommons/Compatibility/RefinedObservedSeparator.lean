import MarginalIndicatorAncestry


/- Pinned-context proof variant: expose the SAME identity maps/simplification,
or eliminate the existing impossible Sum equality. All original theorem and
source/graph/conditioning hypotheses and conclusion semantics remain. -/
/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Hou--Park--Li Proposition 3(2), Appendix F.8, at the original-DAG route level.
This prior-attributed dependency is part of the optimized partial-intervention
certificate. It is not the complete MAG-MEC certificate, query policy, or
physical-faithfulness theorem. Unknown latent and selected carriers remain
unrestricted; selection vertices remain sinks.
-/

namespace RestrictedCausal.RefinedSeparator

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation IndicatorAncestry
open SourceSelection (AncestorOf)

universe u v w

theorem transition_mono {V : Type u} (G : MarkedGraph V)
    (C₁ C₂ A₁ A₂ : V → Prop) (hC : ∀ x, C₂ x → C₁ x) (hA : ∀ x, A₁ x → A₂ x)
    (p q : Arrival V) (h : Transition G C₁ A₁ p q) : Transition G C₂ A₂ p q := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  refine ⟨outgoing, incoming, hedge, hmark, ?_⟩
  cases hm : p.incoming with
  | none => trivial
  | some previous =>
      by_cases hc : previous = .head ∧ outgoing = .head
      · have ha : A₁ p.vertex := by simpa only [hm, ActiveAt, if_pos hc] using hactive
        simpa only [ActiveAt, if_pos hc] using hA _ ha
      · have hn : ¬ C₁ p.vertex := by simpa only [hm, ActiveAt, if_neg hc] using hactive
        simpa only [ActiveAt, if_neg hc] using (fun h => hn (hC _ h))

/-- Every closed collider is ancestral to an allowed terminal. Finish at
that terminal along its directed route. Otherwise copy the next departure.
The induction processes the original finite suffix, not a lengthened walk. -/
theorem relaxed_route_hits {V : Type u} (G : MarkedGraph V) (C E : V → Prop)
    {start p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C (AncestorOf G (fun x => E x ∨ C x))) p xs q)
    (hq : E q.vertex) (actual : Option Mark) («prefix» : List (Arrival V))
    (hp : Route (RealStep G C) start «prefix» ⟨p.vertex, actual⟩)
    (hc : CompatibleArrival C p actual) :
    ∃ endpoint, E endpoint ∧ ∃ last ys,
      Route (RealStep G C) start ys ⟨endpoint, last⟩ := by
  revert hp hc
  revert actual «prefix»
  revert hq
  induction h with
  | nil p =>
      intro hq actual «prefix» hp hc
      exact ⟨p.vertex, hq, actual, «prefix», hp⟩
  | @cons p «next» q rest hstep hrest ih =>
      intro hq actual «prefix» hp hc
      obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
      rcases departure_dichotomy G C _ p actual outgoing hc hactive with good | bad
      · have copied : RealStep G C ⟨p.vertex, actual⟩ «next» :=
          ⟨outgoing, incoming, hedge, hmark, good⟩
        exact ih hq «next».incoming («prefix» ++ [«next»])
          (hp.append (.cons copied (.nil _))) (Or.inl rfl)
      · obtain ⟨_, _, _, hancestor, hnot⟩ := bad
        obtain ⟨endpoint, ⟨directed, hdirected⟩, hendpoint⟩ := hancestor
        rcases hendpoint with hterminal | hcondition
        · obtain ⟨last, tail, htail⟩ := directed_forward_active G C hdirected hnot actual
          exact ⟨endpoint, hterminal, last, «prefix» ++ tail, hp.append htail⟩
        · exact (hnot ⟨endpoint, ⟨directed, hdirected⟩, hcondition⟩).elim

/-- An unconditioned ancestor of selection can receive a new incoming head
regardless of the next edge's mark. This is the selected case that ordinary
ancestry alone would miss. -/
theorem relaxed_from_activated_vertex {V : Type u} (G : MarkedGraph V) (C E : V → Prop)
    {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C (AncestorOf G (fun x => E x ∨ C x))) p xs q)
    (hq : E q.vertex) (ha : AncestorOf G C p.vertex) (hn : ¬ C p.vertex) :
    ∃ endpoint, E endpoint ∧ ∃ last ys,
      Route (RealStep G C) ⟨p.vertex, some .head⟩ ys ⟨endpoint, last⟩ := by
  cases h with
  | nil => exact ⟨p.vertex, hq, some .head, [], .nil _⟩
  | @cons _ «next» _ _ hstep hrest =>
      obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hstep
      have «first» : RealStep G C ⟨p.vertex, some .head⟩ «next» := by
        refine ⟨outgoing, incoming, hedge, hmark, ?_⟩
        cases outgoing with
        | tail => simpa [ActiveAt] using hn
        | head => simpa [ActiveAt] using ha
      exact relaxed_route_hits G C E hrest hq «next».incoming [«next»]
        (.cons «first» (.nil «next»)) (Or.inl rfl)

theorem selected_condition_contains_selection {X : Type u} {S : Type v} {L : Type w}
    (Z : X → Prop) (a : SourceVertex X S L) (ha : Selected a) : SelectedCondition Z a := by
  rcases a with ((x | s) | l)
  · exact ha.elim
  · trivial
  · exact ha.elim

theorem condition_in_endpoint_ancestry {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (Z : X → Prop)
    (upper : ∀ z, Z z → EndpointAncestor D x y (Observed z))
    (a : SourceVertex X S L) (ha : SelectedCondition Z a) : EndpointAncestor D x y a := by
  rcases a with ((z | s) | l)
  · exact upper z ha
  · exact ⟨.inl (.inr s), ⟨[], .nil _⟩, Or.inr (Or.inr trivial)⟩
  · exact ha.elim

theorem colliders_in_endpoint_ancestry {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (Z : X → Prop)
    (upper : ∀ z, Z z → EndpointAncestor D x y (Observed z))
    (a : SourceVertex X S L)
    (ha : AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) a) : EndpointAncestor D x y a :=
  ancestor_idempotent (ancestor_mono (condition_in_endpoint_ancestry D x y Z upper) ha)

/-- An observed internal vertex of this ancestral active suffix belongs to
one of the two complete marginal masks. If its ancestry ends only in S,
use the actual suffix and terminal-directed shortcuts, then prepend I_z -> z.
No MAG separation theorem or anterior-set equality is assumed. -/
theorem ancestral_suffix_forces_mask {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y z : X) (Z : X → Prop)
    (upper : ∀ v, Z v → EndpointAncestor D x y (Observed v))
    (hzx : z ≠ x) (hzy : z ≠ y)
    {p q : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (h : Route (RealStep (arrowGraph D.arrow) (SelectedCondition Z)) p xs q)
    (hp : p.vertex = Observed z) (hq : q.vertex = Observed y)
    (hsupport : EndpointAncestor D x y p.vertex) : MarginalMask D z x ∨ MarginalMask D z y := by
  obtain ⟨a, hpa, ha⟩ := hsupport
  rcases ha with hax | hay | has
  · left
    apply ordinary_ancestor_mask D hzx
    simpa only [hp, hax] using hpa
  · right
    apply ordinary_ancestor_mask D hzy
    simpa only [hp, hay] using hpa
  · have hsel : AncestorOf (arrowGraph D.arrow) Selected p.vertex := ⟨a, hpa, has⟩
    let E : SourceVertex X S L → Prop := fun v => v = Observed x ∨ v = Observed y
    have hanc : ∀ v, AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) v →
        AncestorOf (arrowGraph D.arrow) (fun v => E v ∨ Selected v) v := by
      intro v hv
      apply ancestor_mono (C := EndpointSelection x y) (fun a ha => ?_)
        (colliders_in_endpoint_ancestry D x y Z upper v hv)
      rcases ha with hx | hy | hs
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hy)
      · exact Or.inr hs
    have relaxed := h.map (fun identityValue => identityValue) (transition_mono (arrowGraph D.arrow)
      (SelectedCondition Z) Selected _ _ (selected_condition_contains_selection Z) hanc)
    have relaxed' : Route (Transition (arrowGraph D.arrow) Selected
        (AncestorOf (arrowGraph D.arrow) (fun v => E v ∨ Selected v))) p xs q := by
      simpa using relaxed
    have hn : ¬ Selected p.vertex := by
      simpa only [hp, Selected] using (not_false : ¬ False)
    obtain ⟨endpoint, he, last, ys, hy⟩ := relaxed_from_activated_vertex
      (arrowGraph D.arrow) Selected E relaxed' (Or.inr hq) hsel hn
    rcases he with he | he
    · left
      apply head_connection_mask D hzx
      exact ⟨last, ys, by simpa only [hp, he] using hy⟩
    · right
      apply head_connection_mask D hzy
      exact ⟨last, ys, by simpa only [hp, he] using hy⟩

/-- Turn every actual suffix into an inducing suffix. The path is physically
simple, so an internal departure equals neither endpoint. Its noncollider
cannot be selected, and the preceding lemma puts any observed noncollider in
the conditioning set, a contradiction. -/
theorem mask_separator_suffix_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (Z : X → Prop)
    (upper : ∀ z, Z z → EndpointAncestor D x y (Observed z))
    (lower : ∀ z, z ≠ x → z ≠ y → (MarginalMask D z x ∨ MarginalMask D z y) → Z z)
    {p q : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (h : Route (RealStep (arrowGraph D.arrow) (SelectedCondition Z)) p xs q)
    (hq : q.vertex = Observed y) (hnd : ((p :: xs).map Arrival.vertex).Nodup)
    (hfirst : Observed x ∉ (p :: xs).map Arrival.vertex)
    (hsupport : ∀ r ∈ p :: xs, EndpointAncestor D x y r.vertex) :
    Route (Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y)) p xs q := by
  revert hnd hfirst hsupport
  revert hq
  induction h with
  | nil p => intro _ _ _ _; exact .nil p
  | @cons p «next» q rest hstep hrest ih =>
      intro hq hnd hfirst hsupport
      have hnotTail := (List.nodup_cons.mp hnd).1
      have htailNd := (List.nodup_cons.mp hnd).2
      have hpx : p.vertex ≠ Observed x := by
        intro heq
        exact hfirst (List.mem_map.mpr ⟨p, List.mem_cons_self, heq⟩)
      have hpy : p.vertex ≠ Observed y := by
        intro heq
        exact hnotTail (List.mem_map.mpr ⟨q, Route.end_mem hrest, hq.trans heq.symm⟩)
      have newstep : Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y) p «next» := by
        obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
        refine ⟨outgoing, incoming, hedge, hmark, ?_⟩
        cases hm : p.incoming with
        | none => trivial
        | some previous =>
            by_cases hc : previous = .head ∧ outgoing = .head
            · have ha : AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) p.vertex := by
                simpa only [hm, ActiveAt, if_pos hc] using hactive
              simpa only [ActiveAt, if_pos hc] using colliders_in_endpoint_ancestry D x y Z upper _ ha
            · have hn : ¬ SelectedCondition Z p.vertex := by
                simpa only [hm, ActiveAt, if_neg hc] using hactive
              have hnonlatent : ¬ Nonlatent p.vertex := by
                intro hret
                rcases hv : p.vertex with ((z | s) | l)
                · have hzx : z ≠ x := fun hz => hpx (hv.trans (congrArg Observed hz))
                  have hzy : z ≠ y := fun hz => hpy (hv.trans (congrArg Observed hz))
                  have hmask := ancestral_suffix_forces_mask D x y z Z upper hzx hzy
                    (.cons ⟨outgoing, incoming, hedge, hmark, hactive⟩ hrest)
                    hv hq (hsupport p List.mem_cons_self)
                  apply hn
                  rw [hv]
                  exact lower z hzx hzy hmask
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

/-- Prior HPL refined observed-pair separator, with exact original source
quantifiers and both conditioning-set inclusions explicit. For partial
interventions the later policy must supply the unknown-mask part by searching
untargeted variables; that policy is not assumed by this theorem. -/
theorem refined_observed_separator {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (hne : x ≠ y) (Z : X → Prop)
    (hx : ¬ Z x) (hy : ¬ Z y)
    (upper : ∀ z, Z z → EndpointAncestor D x y (Observed z))
    (lower : ∀ z, z ≠ x → z ≠ y → (MarginalMask D z x ∨ MarginalMask D z y) → Z z) :
    InducingPath D x y ↔
      ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y) := by
  constructor
  · intro h
    exact (inducing_implies_inseparable D x y h).2 Z hx hy
  · rintro ⟨last, xs, hp, hnd⟩
    have hsupport := route_ancestral_support (arrowGraph D.arrow) (original_arrow_mixed_laws D)
      (SelectedCondition Z) (AncestorOf (arrowGraph D.arrow) (SelectedCondition Z))
      (EndpointAncestor D x y) (colliders_in_endpoint_ancestry D x y Z upper)
      (ancestor_backward_closed (arrowGraph D.arrow) (EndpointSelection x y)) hp
      ⟨Observed x, ⟨[], .nil _⟩, Or.inl rfl⟩
      ⟨Observed y, ⟨[], .nil _⟩, Or.inr (Or.inl rfl)⟩
    refine ⟨hne, last, xs, ?_, hnd⟩
    cases hp with
    | nil => exact .nil _
    | @cons «first» «next» finish rest hstep hrest =>
        obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hstep
        refine .cons ⟨outgoing, incoming, hedge, hmark, trivial⟩
          (mask_separator_suffix_inducing D x y Z upper lower hrest rfl
            (List.nodup_cons.mp hnd).2 (List.nodup_cons.mp hnd).1 ?_)
        intro r hr
        exact hsupport r (List.mem_cons_of_mem _ hr)

end RestrictedCausal.RefinedSeparator
