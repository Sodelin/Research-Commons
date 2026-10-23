import EndpointColliderActivation

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Classical inducing paths, in the actual original DAG: every internal
noncollider is latent; every collider is ancestral to an endpoint or selection.
Both directions of adjacency = absence of an observed separator are proved
below, rather than made a graph-adapter premise.
-/

namespace RestrictedCausal.InducingSeparation

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open SourceSelection (AncestorOf)

universe u v w

theorem Route.end_mem {V : Type u} {R : V → V → Prop} {a b : V} {xs : List V}
    (h : SelectedWalk.Route R a xs b) : b ∈ a :: xs := by
  induction h with
  | nil a => exact List.mem_cons_self
  | cons hstep htail ih => exact List.mem_cons_of_mem _ ih

def BackwardClosed {V : Type u} (G : MarkedGraph V) (A : V → Prop) : Prop :=
  ∀ a b, Directed G a b → A b → A a

theorem ancestor_backward_closed {V : Type u} (G : MarkedGraph V) (C : V → Prop) :
    BackwardClosed G (AncestorOf G C) := by
  rintro a b hab ⟨z, ⟨zs, hz⟩, hc⟩
  exact ⟨z, ⟨b :: zs, .cons hab hz⟩, hc⟩

theorem head_nonancestor_general {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C B A : V → Prop) (hBA : ∀ v, B v → A v) (hclosed : BackwardClosed G A)
    {p q : Arrival V} {xs : List (Arrival V)}
    (h : SelectedWalk.Route (Transition G C B) p xs q) :
    p.incoming = some .head → ¬ A p.vertex → q.incoming = some .head ∧ ¬ A q.vertex := by
  induction h with
  | nil p => exact fun hp hn => ⟨hp, hn⟩
  | @cons p «next» q rest hstep hrest ih =>
      intro hp hn
      obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
      have hout : outgoing = .tail := by
        cases outgoing with
        | tail => rfl
        | head =>
            have hb : B p.vertex := by simpa [hp, ActiveAt] using hactive
            exact (hn (hBA _ hb)).elim
      subst outgoing
      have hin : incoming = .head := by
        cases incoming with
        | head => rfl
        | tail => exact (laws.no_tail_tail _ _ hedge).elim
      subst incoming
      exact ih hmark (fun ha => hn (hclosed _ _ hedge ha))

/-- Every vertex of a route whose colliders and endpoints lie in a backward
closed set lies in that set. A hypothetical nonancestor entered at a head is
forced forward until the endpoint; entered at a tail, it is ancestral to the
preceding vertex. This is the explicit ancestral-support argument. -/
theorem route_ancestral_support {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C B A : V → Prop) (hBA : ∀ v, B v → A v) (hclosed : BackwardClosed G A)
    {p q : Arrival V} {xs : List (Arrival V)}
    (h : SelectedWalk.Route (Transition G C B) p xs q)
    (hp : A p.vertex) (hq : A q.vertex) : ∀ r ∈ p :: xs, A r.vertex := by
  revert hp hq
  induction h with
  | nil p =>
      intro hp hq r hr
      have heq : r = p := by simpa only [List.mem_singleton] using hr
      simpa only [heq] using hp
  | @cons p «next» q rest hstep hrest ih =>
      intro hp hq
      have hnext : A «next».vertex := by
        by_contra hn
        obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hstep
        cases incoming with
        | head =>
            have hend := (head_nonancestor_general G laws C B A hBA hclosed hrest hmark hn).2
            exact hend hq
        | tail =>
            cases outgoing with
            | tail => exact laws.no_tail_tail _ _ hedge
            | head => exact hn (hclosed _ _ (laws.symmetric _ _ _ _ hedge) hp)
      intro r hr
      rcases List.mem_cons.mp hr with heq | hmem
      · simpa only [heq] using hp
      · exact ih hnext hq r hmem

def Nonlatent {X : Type u} {S : Type v} {L : Type w} : SourceVertex X S L → Prop
  | .inl _ => True
  | .inr _ => False

def Selected {X : Type u} {S : Type v} {L : Type w} : SourceVertex X S L → Prop
  | .inl (.inr _) => True
  | _ => False

abbrev Observed {X : Type u} {S : Type v} {L : Type w} (x : X) : SourceVertex X S L :=
  .inl (.inl x)

def EndpointSelection {X : Type u} {S : Type v} {L : Type w} (x y : X)
    (a : SourceVertex X S L) : Prop := a = Observed x ∨ a = Observed y ∨ Selected a

abbrev EndpointAncestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) := AncestorOf (arrowGraph D.arrow) (EndpointSelection x y)

abbrev SelectedCondition {X : Type u} {S : Type v} {L : Type w} (Z : X → Prop) :
    SourceVertex X S L → Prop := retainedCondition (SourceSelection.Condition Z)

/-- Exactly HPL Definition 1's path condition, represented by actual incidences
and a physically simple vertex list. Endpoints are excluded by simplicity,
not incorrectly required to be latent or to be colliders. -/
def InducingPath {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : Prop :=
  x ≠ y ∧ ∃ last xs,
    SelectedWalk.Route (Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y))
      ⟨Observed x, none⟩ xs ⟨Observed y, last⟩ ∧
    ((⟨Observed x, none⟩ :: xs).map Arrival.vertex).Nodup

def Inseparable {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : Prop :=
  x ≠ y ∧ ∀ Z : X → Prop, ¬ Z x → ¬ Z y →
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y)

theorem inducing_implies_inseparable {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (h : InducingPath D x y) : Inseparable D x y := by
  obtain ⟨hne, last, xs, hp, _⟩ := h
  refine ⟨hne, ?_⟩
  intro Z hx hy
  have hcondition : ∀ a, SelectedCondition Z a → Nonlatent a := by
    intro a ha
    cases a with
    | inl r => trivial
    | inr l => exact ha.elim
  have hancestor : ∀ a, EndpointAncestor D x y a →
      AncestorOf (arrowGraph D.arrow)
        (EndpointCondition (SelectedCondition Z) (Observed x) (Observed y)) a := by
    apply ancestor_mono
    intro a ha
    rcases ha with heq | heq | hs
    · exact Or.inl heq
    · exact Or.inr (Or.inl heq)
    · right; right
      rcases a with ((z | s) | l)
      · exact hs.elim
      · trivial
      · exact hs.elim
  have step : ∀ p q,
      Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y) p q →
      Transition (arrowGraph D.arrow) (SelectedCondition Z)
        (AncestorOf (arrowGraph D.arrow)
          (EndpointCondition (SelectedCondition Z) (Observed x) (Observed y))) p q := by
    intro p q hs
    obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hs
    refine ⟨outgoing, incoming, hedge, hmark, ?_⟩
    cases hm : p.incoming with
    | none => trivial
    | some previous =>
        by_cases hcol : previous = .head ∧ outgoing = .head
        · have ha : EndpointAncestor D x y p.vertex := by
            simpa only [hm, ActiveAt, if_pos hcol] using hactive
          simpa only [ActiveAt, if_pos hcol] using hancestor _ ha
        · have hn : ¬ Nonlatent p.vertex := by
            simpa only [hm, ActiveAt, if_neg hcol] using hactive
          simpa only [ActiveAt, if_neg hcol] using (fun hc => hn (hcondition _ hc))
  have relaxed := hp.map id step
  have relaxed' : SelectedWalk.Route (Transition (arrowGraph D.arrow) (SelectedCondition Z)
      (AncestorOf (arrowGraph D.arrow)
        (EndpointCondition (SelectedCondition Z) (Observed x) (Observed y))))
      ⟨Observed x, none⟩ xs ⟨Observed y, last⟩ := by
    simpa only [List.map_id] using relaxed
  exact endpoint_relaxed_connection (arrowGraph D.arrow) (original_arrow_mixed_laws D)
    (SelectedCondition Z) (Observed x) (Observed y) relaxed'

def AncestralSeparator {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y z : X) : Prop :=
  z ≠ x ∧ z ≠ y ∧ EndpointAncestor D x y (Observed z)

theorem separator_condition_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (a : SourceVertex X S L)
    (ha : SelectedCondition (AncestralSeparator D x y) a) : EndpointAncestor D x y a := by
  rcases a with ((z | s) | l)
  · exact ha.2.2
  · exact ⟨.inl (.inr s), ⟨[], .nil _⟩, Or.inr (Or.inr trivial)⟩
  · exact ha.elim

theorem separator_colliders_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (a : SourceVertex X S L)
    (ha : AncestorOf (arrowGraph D.arrow) (SelectedCondition (AncestralSeparator D x y)) a) :
    EndpointAncestor D x y a :=
  ancestor_idempotent (ancestor_mono (separator_condition_ancestor D x y) ha)

/-- Convert an actual suffix of the simple path at the ancestral separator.
The global first endpoint is absent from this suffix; the current departure
cannot equal the final endpoint because the remaining vertex list is nodup. -/
theorem ancestral_suffix_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X)
    {p q : Arrival (SourceVertex X S L)} {xs : List (Arrival (SourceVertex X S L))}
    (h : SelectedWalk.Route (RealStep (arrowGraph D.arrow)
      (SelectedCondition (AncestralSeparator D x y))) p xs q)
    (hq : q.vertex = Observed y)
    (hnd : ((p :: xs).map Arrival.vertex).Nodup)
    (hfirst : Observed x ∉ (p :: xs).map Arrival.vertex)
    (hsupport : ∀ r ∈ p :: xs, EndpointAncestor D x y r.vertex) :
    SelectedWalk.Route (Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y))
      p xs q := by
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
        apply hfirst
        exact List.mem_map.mpr ⟨p, List.mem_cons_self, heq⟩
      have hpy : p.vertex ≠ Observed y := by
        intro heq
        apply hnotTail
        exact List.mem_map.mpr ⟨q, Route.end_mem hrest, hq.trans heq.symm⟩
      have newstep : Transition (arrowGraph D.arrow) Nonlatent (EndpointAncestor D x y) p «next» := by
        obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
        refine ⟨outgoing, incoming, hedge, hmark, ?_⟩
        cases hm : p.incoming with
        | none => trivial
        | some previous =>
            by_cases hcol : previous = .head ∧ outgoing = .head
            · have ha : AncestorOf (arrowGraph D.arrow)
                  (SelectedCondition (AncestralSeparator D x y)) p.vertex := by
                simpa only [hm, ActiveAt, if_pos hcol] using hactive
              simpa only [ActiveAt, if_pos hcol] using separator_colliders_ancestor D x y _ ha
            · have hn : ¬ SelectedCondition (AncestralSeparator D x y) p.vertex := by
                simpa only [hm, ActiveAt, if_neg hcol] using hactive
              have hnonlatent : ¬ Nonlatent p.vertex := by
                intro hret
                have ha := hsupport p List.mem_cons_self
                rcases hv : p.vertex with ((z | s) | l)
                · apply hn
                  rw [hv]
                  exact ⟨fun hz => hpx (hv.trans (congrArg Observed hz)),
                    fun hz => hpy (hv.trans (congrArg Observed hz)), by simpa only [hv] using ha⟩
                · apply hn
                  rw [hv]
                  trivial
                · simpa only [hv, Nonlatent] using hret
              simpa only [ActiveAt, if_neg hcol] using hnonlatent
      refine .cons newstep (ih hq htailNd ?_ ?_)
      · intro hm
        exact hfirst (List.mem_cons_of_mem _ hm)
      · intro r hr
        exact hsupport r (List.mem_cons_of_mem _ hr)

theorem inseparable_implies_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (h : Inseparable D x y) : InducingPath D x y := by
  obtain ⟨hne, hsep⟩ := h
  have hx : ¬ AncestralSeparator D x y x := fun h => h.1 rfl
  have hy : ¬ AncestralSeparator D x y y := fun h => h.2.1 rfl
  obtain ⟨last, xs, hp, hnd⟩ := hsep (AncestralSeparator D x y) hx hy
  have hsupport := route_ancestral_support (arrowGraph D.arrow) (original_arrow_mixed_laws D)
    (SelectedCondition (AncestralSeparator D x y))
    (AncestorOf (arrowGraph D.arrow) (SelectedCondition (AncestralSeparator D x y)))
    (EndpointAncestor D x y) (separator_colliders_ancestor D x y)
    (ancestor_backward_closed (arrowGraph D.arrow) (EndpointSelection x y)) hp
    ⟨Observed x, ⟨[], .nil _⟩, Or.inl rfl⟩
    ⟨Observed y, ⟨[], .nil _⟩, Or.inr (Or.inl rfl)⟩
  refine ⟨hne, last, xs, ?_, hnd⟩
  cases hp with
  | nil => exact .nil _
  | @cons «first» «next» finish rest hstep hrest =>
      obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hstep
      refine .cons ⟨outgoing, incoming, hedge, hmark, trivial⟩
        (ancestral_suffix_inducing D x y hrest rfl (List.nodup_cons.mp hnd).2
          (List.nodup_cons.mp hnd).1 ?_)
      intro r hr
      exact hsupport r (List.mem_cons_of_mem _ hr)

theorem inducing_iff_inseparable {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : InducingPath D x y ↔ Inseparable D x y :=
  ⟨inducing_implies_inseparable D x y, inseparable_implies_inducing D x y⟩

end RestrictedCausal.InducingSeparation
