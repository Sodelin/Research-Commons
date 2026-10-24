import PartialIndicatorQueryFamily

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The old observed selected CI model and literal marked MAG are unchanged by
adding one genuine exogenous sole-child indicator. This supplies the exact
baseline/augmented alignment needed by the shared-separator certificate.
Attribution: classical marginalization/conditioning facts and HPL Lemma 2.
The complete MAG m-separation/MEC theorem is not assumed or proved here.
-/

namespace RestrictedCausal.CommonObserved

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation IndicatorAncestry RefinedIndicator GraphEquivalence
open FiniteTargetImage HPLTarget
open SourceSelection (AncestorOf)

universe u v w

theorem old_source_injective {X : Type u} {S : Type v} {L : Type w} :
    Function.Injective (oldSource (X := X) (S := S) (L := L)) := by
  intro a b hab
  have h := congrArg sourceIndicatorEquiv hab
  rw [indicator_equiv_oldSource, indicator_equiv_oldSource] at h
  exact Option.some.inj h

theorem old_source_not_root {X : Type u} {S : Type v} {L : Type w}
    (a : SourceVertex X S L) : oldSource a ≠ Observed none := by
  intro ha
  have h := congrArg sourceIndicatorEquiv ha
  rw [indicator_equiv_oldSource] at h
  change (some a : Option (SourceVertex X S L)) = none at h
  cases h

theorem old_condition_any {X : Type u} {S : Type v} {L : Type w}
    (K : Option X → Prop) (a : SourceVertex X S L) :
    SelectedCondition K (oldSource a) ↔ SelectedCondition (fun x => K (some x)) a := by
  rcases a with ((x | s) | l) <;> exact Iff.rfl

/-- The root may itself be conditioned. It still cannot be a conditioned
descendant of an old vertex, since its actual indegree is zero. -/
theorem old_ancestor_any {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (K : Option X → Prop) (a : SourceVertex X S L) :
    AncestorOf (arrowGraph (augmentSource D t).arrow) (SelectedCondition K) (oldSource a) ↔
      AncestorOf (arrowGraph D.arrow) (SelectedCondition (fun x => K (some x))) a := by
  constructor
  · rintro ⟨z, hp, hc⟩
    rcases z with ((x | s) | l)
    · cases x with
      | none => exact (old_not_ancestor_root D t a hp).elim
      | some x => exact ⟨Observed x, (old_source_reach D t a _).mp hp, hc⟩
    · exact ⟨.inl (.inr s), (old_source_reach D t a _).mp hp, trivial⟩
    · exact hc.elim
  · rintro ⟨z, hp, hc⟩
    exact ⟨oldSource z, (old_source_reach D t a z).mpr hp, (old_condition_any K z).mpr hc⟩

/-- A physically simple route between old endpoints cannot visit the root:
its predecessor and successor would both be the same named child. This uses
actual incidences and full vertex simplicity, not an asserted CI equivalence. -/
theorem simple_route_root_free {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X)
    (C A : SourceVertex (Option X) S L → Prop)
    {p q : Arrival (SourceVertex (Option X) S L)} {xs : List (Arrival (SourceVertex (Option X) S L))}
    (h : Route (Transition (arrowGraph (augmentSource D t).arrow) C A) p xs q)
    (hp : p.vertex ≠ Observed none) (hq : q.vertex ≠ Observed none)
    (hnd : ((p :: xs).map Arrival.vertex).Nodup) :
    ∀ r ∈ p :: xs, r.vertex ≠ Observed none := by
  revert hp hnd
  induction h with
  | nil p =>
      intro hp hnd r hr
      have heq : r = p := List.mem_singleton.mp hr
      simpa only [heq] using hp
  | @cons p «next» q rest hstep hrest ih =>
      intro hp hnd
      have hnext : «next».vertex ≠ Observed none := by
        intro hn
        obtain ⟨outgoing, incoming, hedge, _, _⟩ := hstep
        have reversed := arrow_graph_symm (augmentSource D t).arrow _ _ _ _ hedge
        have firstRoot := (indicator_raw_edge D t p.vertex incoming outgoing).mp
          (by simpa only [hn] using reversed)
        cases hrest with
        | nil => exact hq hn
        | @cons «next» later q tail second remaining =>
            obtain ⟨outgoing₂, incoming₂, hedge₂, _, _⟩ := second
            have secondRoot := (indicator_raw_edge D t later.vertex outgoing₂ incoming₂).mp
              (by simpa only [hn] using hedge₂)
            have hsame : later.vertex = p.vertex := secondRoot.1.trans firstRoot.1.symm
            apply (List.nodup_cons.mp hnd).1
            exact List.mem_map.mpr ⟨later,
              List.mem_cons_of_mem _ List.mem_cons_self, hsame⟩
      intro r hr
      rcases List.mem_cons.mp hr with heq | hr
      · simpa only [heq] using hp
      · exact ih hq hnext (List.nodup_cons.mp hnd).2 r hr

theorem forget_nodup {X : Type u} {S : Type v} {L : Type w}
    (t : X) (xs : List (Arrival (SourceVertex (Option X) S L)))
    (hnd : (xs.map Arrival.vertex).Nodup)
    (hfree : ∀ r ∈ xs, r.vertex ≠ Observed none) :
    ((xs.map (mapArrival (forgetIndicator t))).map Arrival.vertex).Nodup := by
  have hinj : ∀ a ∈ xs.map Arrival.vertex, ∀ b ∈ xs.map Arrival.vertex,
      forgetIndicator t a = forgetIndicator t b → a = b := by
    intro a ha b hb hab
    obtain ⟨p, hp, hpa⟩ := List.mem_map.mp ha
    obtain ⟨q, hq, hqb⟩ := List.mem_map.mp hb
    have han : a ≠ Observed none := by simpa only [hpa] using hfree p hp
    have hbn : b ≠ Observed none := by simpa only [hqb] using hfree q hq
    have h := congrArg oldSource hab
    simpa only [old_forget_nonroot t a han, old_forget_nonroot t b hbn] using h
  have mapped := hnd.map_on hinj
  simpa only [List.map_map, Function.comp_def, mapArrival] using mapped

theorem pullback_step_any {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (K : Option X → Prop)
    (p q : Arrival (SourceVertex (Option X) S L))
    (hp : p.vertex ≠ Observed none) (hq : q.vertex ≠ Observed none)
    (h : RealStep (arrowGraph (augmentSource D t).arrow) (SelectedCondition K) p q) :
    RealStep (arrowGraph D.arrow) (SelectedCondition (fun x => K (some x)))
      (mapArrival (forgetIndicator t) p) (mapArrival (forgetIndicator t) q) := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  have he : (arrowGraph D.arrow).edge (forgetIndicator t p.vertex)
      (forgetIndicator t q.vertex) outgoing incoming := by
    apply (old_source_marked_exact D t _ _ _ _).mpr
    simpa only [old_forget_nonroot t p.vertex hp, old_forget_nonroot t q.vertex hq] using hedge
  refine ⟨outgoing, incoming, he, hmark, ?_⟩
  cases hm : p.incoming with
  | none => simp only [mapArrival, hm]
  | some previous =>
      by_cases hc : previous = .head ∧ outgoing = .head
      · have ha : AncestorOf (arrowGraph (augmentSource D t).arrow)
            (SelectedCondition K) p.vertex := by
          simpa only [hm, ActiveAt, if_pos hc] using hactive
        have ha' := (old_ancestor_any D t K (forgetIndicator t p.vertex)).mp
          (by simpa only [old_forget_nonroot t p.vertex hp] using ha)
        simpa only [mapArrival, hm, ActiveAt, if_pos hc] using ha'
      · have hn : ¬ SelectedCondition K p.vertex := by
          simpa only [hm, ActiveAt, if_neg hc] using hactive
        have hn' : ¬ SelectedCondition (fun x => K (some x)) (forgetIndicator t p.vertex) := by
          intro h
          have old := (old_condition_any K (forgetIndicator t p.vertex)).mpr h
          exact hn (by simpa only [old_forget_nonroot t p.vertex hp] using old)
        simpa only [mapArrival, hm, ActiveAt, if_neg hc] using hn'

theorem pullback_route_any {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (K : Option X → Prop)
    {p q : Arrival (SourceVertex (Option X) S L)} {xs : List (Arrival (SourceVertex (Option X) S L))}
    (h : Route (RealStep (arrowGraph (augmentSource D t).arrow) (SelectedCondition K)) p xs q)
    (hfree : ∀ r ∈ p :: xs, r.vertex ≠ Observed none) :
    Route (RealStep (arrowGraph D.arrow) (SelectedCondition (fun x => K (some x))))
      (mapArrival (forgetIndicator t) p) (xs.map (mapArrival (forgetIndicator t)))
      (mapArrival (forgetIndicator t) q) := by
  revert hfree
  induction h with
  | nil p => intro _; exact .nil _
  | @cons p «next» q rest hstep hrest ih =>
      intro hfree
      refine .cons (pullback_step_any D t K p «next» (hfree p List.mem_cons_self)
        (hfree «next» (List.mem_cons_of_mem _ List.mem_cons_self)) hstep) (ih ?_)
      intro r hr
      exact hfree r (List.mem_cons_of_mem _ hr)

theorem lift_step_any {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (K : Option X → Prop)
    (p q : Arrival (SourceVertex X S L))
    (h : RealStep (arrowGraph D.arrow) (SelectedCondition (fun x => K (some x))) p q) :
    RealStep (arrowGraph (augmentSource D t).arrow) (SelectedCondition K)
      (mapArrival oldSource p) (mapArrival oldSource q) := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  refine ⟨outgoing, incoming, (old_source_marked_exact D t _ _ _ _).mp hedge, hmark, ?_⟩
  cases hm : p.incoming with
  | none => simp only [mapArrival, hm]
  | some previous =>
      by_cases hc : previous = .head ∧ outgoing = .head
      · have ha : AncestorOf (arrowGraph D.arrow)
            (SelectedCondition (fun x => K (some x))) p.vertex := by
          simpa only [hm, ActiveAt, if_pos hc] using hactive
        simpa only [mapArrival, hm, ActiveAt, if_pos hc] using (old_ancestor_any D t K p.vertex).mpr ha
      · have hn : ¬ SelectedCondition (fun x => K (some x)) p.vertex := by
          simpa only [hm, ActiveAt, if_neg hc] using hactive
        simpa only [mapArrival, hm, ActiveAt, if_neg hc] using
          (fun hk => hn ((old_condition_any K p.vertex).mp hk))

/-- Full old-endpoint connection equivalence, including conditioning the
root itself. This is stronger than merely preserving a projected skeleton. -/
theorem old_observed_active_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) (K : Option X → Prop) (x y : X) :
    ActiveConnection (arrowGraph (augmentSource D t).arrow) (SelectedCondition K)
      (Observed (some x)) (Observed (some y)) ↔
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition (fun x => K (some x)))
      (Observed x) (Observed y) := by
  constructor
  · rintro ⟨last, xs, hp, hnd⟩
    have hfree := simple_route_root_free D t (SelectedCondition K)
      (AncestorOf (arrowGraph (augmentSource D t).arrow) (SelectedCondition K)) hp
      (old_source_not_root (Observed x)) (old_source_not_root (Observed y)) hnd
    have pulled := pullback_route_any D t K hp hfree
    have nd := forget_nodup t (⟨Observed (some x), none⟩ :: xs) hnd hfree
    refine ⟨last, xs.map (mapArrival (forgetIndicator t)), ?_, ?_⟩
    · exact pulled
    · simpa only [List.map_cons, mapArrival, forgetIndicator, sourceIndicatorEquiv, Observed] using nd
  · rintro ⟨last, xs, hp, hnd⟩
    have lifted := hp.map (mapArrival oldSource) (lift_step_any D t K)
    have nd := hnd.map (old_source_injective (X := X) (S := S) (L := L))
    refine ⟨last, xs.map (mapArrival oldSource), lifted, ?_⟩
    simpa only [List.map_cons, List.map_map, Function.comp_def, mapArrival, oldSource, Observed] using nd

theorem old_inducing_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x y : X) :
    InducingPath (augmentSource D t) (some x) (some y) ↔ InducingPath D x y := by
  rw [inducing_iff_inseparable, inducing_iff_inseparable]
  constructor
  · rintro ⟨hne, hconn⟩
    refine ⟨fun h => hne (congrArg some h), ?_⟩
    intro Z hx hy
    exact (old_observed_active_iff D t (InvarianceCondition Z) x y).mp
      (hconn (InvarianceCondition Z) hx hy)
  · rintro ⟨hne, hconn⟩
    refine ⟨fun h => hne (Option.some.inj h), ?_⟩
    intro K hx hy
    exact (old_observed_active_iff D t K x y).mpr (hconn (fun x => K (some x)) hx hy)

theorem old_selection_ancestor_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x : X) :
    SelectionAncestor (augmentSource D t) (some x) ↔ SelectionAncestor D x := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, (old_source_reach D t (Observed x) (.inl (.inr s))).mp hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, (old_source_reach D t (Observed x) (.inl (.inr s))).mpr hs⟩

theorem old_tail_flag_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x y : X) :
    TailFlag (augmentSource D t) (some x) (some y) ↔ TailFlag D x y :=
  or_congr (old_source_reach D t (Observed x) (Observed y)) (old_selection_ancestor_iff D t x)

theorem old_endpoint_mark_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x y : X) (m : Mark) :
    EndpointMark (augmentSource D t) (some x) (some y) m ↔ EndpointMark D x y m := by
  cases m with
  | tail => simpa only [endpoint_tail_iff] using old_tail_flag_iff D t x y
  | head => simpa only [endpoint_head_iff] using not_congr (old_tail_flag_iff D t x y)

/-- Literal old observed MAG equality, including every endpoint mark, for
each root added to the same original source. Not independent slice matching. -/
theorem old_mag_edge_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t x y : X) (mx my : Mark) :
    (mag (augmentSource D t)).edge (some x) (some y) mx my ↔ (mag D).edge x y mx my :=
  and_congr (old_inducing_iff D t x y)
    (and_congr (old_endpoint_mark_iff D t x y mx) (old_endpoint_mark_iff D t y x my))

end RestrictedCausal.CommonObserved
