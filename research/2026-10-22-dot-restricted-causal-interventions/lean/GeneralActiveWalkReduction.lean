import OriginalProjectionAncestry

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Classical active-walk reduction with the TRUE ancestor conditioning predicate.
Unlike uniform-head/tail special cases, repeated vertices may have different
arrival marks. The splice proof explicitly handles the new-collider obstruction.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem prefix_of_mem {V : Type u} {R : V → V → Prop}
    {a b x : V} {xs : List V} (h : Route R a xs b) (hx : x ∈ a :: xs) :
    ∃ ys, Route R a ys x := by
  revert hx
  induction h with
  | nil a =>
      intro hx
      have heq : x = a := by simpa only [List.mem_singleton] using hx
      subst x
      exact ⟨[], .nil a⟩
  | @cons a b c xs hab hbc ih =>
      intro hx
      rcases List.mem_cons.mp hx with heq | hx
      · subst x
        exact ⟨[], .nil a⟩
      · obtain ⟨ys, hy⟩ := ih hx
        exact ⟨b :: ys, .cons hab hy⟩

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.ActiveWalkReduction

open SelectedWalk CanonicalSelection LatentRoots
open SourceSelection (AncestorOf)

universe u

theorem conditioned_active_heads {V : Type u} {C A : V → Prop}
    {v : V} {incoming outgoing : Mark} (hc : C v)
    (h : ActiveAt C A v incoming outgoing) : incoming = .head ∧ outgoing = .head := by
  by_cases hh : incoming = .head ∧ outgoing = .head
  · exact hh
  · have hn : ¬ C v := by simpa only [ActiveAt, if_neg hh] using h
    exact (hn hc).elim

theorem head_nonancestor_step {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) {p q : Arrival V} (hp : p.incoming = some .head)
    (hn : ¬ AncestorOf G C p.vertex) (h : Transition G C (AncestorOf G C) p q) :
    q.incoming = some .head ∧ ¬ AncestorOf G C q.vertex := by
  obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := h
  have ha : ActiveAt C (AncestorOf G C) p.vertex .head outgoing := by
    simpa only [hp] using hactive
  have hout : outgoing = .tail := by
    cases outgoing with
    | tail => rfl
    | head =>
        have hac : AncestorOf G C p.vertex := by simpa [ActiveAt] using ha
        exact (hn hac).elim
  subst outgoing
  have hin : incoming = .head := by
    cases incoming with
    | head => rfl
    | tail => exact (laws.no_tail_tail p.vertex q.vertex hedge).elim
  subst incoming
  refine ⟨hmark, ?_⟩
  rintro ⟨z, ⟨zs, hz⟩, hc⟩
  exact hn ⟨z, ⟨q.vertex :: zs, .cons hedge hz⟩, hc⟩

/-- A head-arrival at a nonancestor forces all later active steps forward.
Hence it cannot return to the same vertex with a tail-arrival. This is exactly
the obstruction that could otherwise make loop splicing create a closed collider. -/
theorem head_nonancestor_route {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C (AncestorOf G C)) p xs q) :
    p.incoming = some .head → ¬ AncestorOf G C p.vertex →
      q.incoming = some .head ∧ ¬ AncestorOf G C q.vertex := by
  induction h with
  | nil p => exact fun hp hn => ⟨hp, hn⟩
  | cons hstep htail ih =>
      intro hp hn
      obtain ⟨hq, hqn⟩ := head_nonancestor_step G laws C hp hn hstep
      exact ih hq hqn

theorem some_arrival_preserved {V : Type u} {G : MarkedGraph V} {C A : V → Prop}
    {p q : Arrival V} {xs : List (Arrival V)} (h : Route (Transition G C A) p xs q) :
    (∃ m, p.incoming = some m) → ∃ m, q.incoming = some m := by
  induction h with
  | nil p => exact id
  | cons hstep htail ih =>
      intro _
      obtain ⟨outgoing, incoming, _, hmark, _⟩ := hstep
      exact ih ⟨incoming, hmark⟩

/-- Delete a return segment at the same physical vertex, even if the two
arrival marks differ. Uses true ancestry, not a freely chosen activity set. -/
theorem splice_departure {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) {p q r : Arrival V} {loop : List (Arrival V)}
    (hloop : Route (Transition G C (AncestorOf G C)) p loop q)
    (hv : p.vertex = q.vertex) (hnext : Transition G C (AncestorOf G C) q r) :
    Transition G C (AncestorOf G C) p r := by
  cases hloop with
  | nil => exact hnext
  | @cons p first q rest hfirst hrest =>
      have hwhole : Route (Transition G C (AncestorOf G C)) p (first :: rest) q := .cons hfirst hrest
      obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hnext
      refine ⟨outgoing, incoming, ?_, hmark, ?_⟩
      · rw [hv]
        exact hedge
      · cases hpm : p.incoming with
        | none => trivial
        | some previous =>
            by_cases hcollider : previous = .head ∧ outgoing = .head
            · simp only [ActiveAt, if_pos hcollider]
              by_cases ha : AncestorOf G C p.vertex
              · exact ha
              · have hphead : p.incoming = some .head := hpm.trans (congrArg some hcollider.1)
                obtain ⟨hqhead, hqnot⟩ := head_nonancestor_route G laws C hwhole hphead ha
                have hqa : AncestorOf G C q.vertex := by
                  simpa [hqhead, hcollider.2, ActiveAt] using hactive
                exact (hqnot hqa).elim
            · simp only [ActiveAt, if_neg hcollider]
              intro hc
              obtain ⟨firstOut, firstIn, _, firstMark, firstActive⟩ := hfirst
              have hpa : ActiveAt C (AncestorOf G C) p.vertex previous firstOut := by
                simpa only [hpm] using firstActive
              have hphead := (conditioned_active_heads hc hpa).1
              obtain ⟨lastIn, hlast⟩ := some_arrival_preserved hrest ⟨firstIn, firstMark⟩
              have hqa : ActiveAt C (AncestorOf G C) q.vertex lastIn outgoing := by
                simpa only [hlast] using hactive
              have hqc : C q.vertex := hv ▸ hc
              have houthead := (conditioned_active_heads hqc hqa).2
              exact hcollider ⟨hphead, houthead⟩

/-- Full finite physical-vertex loop reduction. The terminal incoming mark may
change if the entire tail is erased, but both physical endpoints are preserved.
No shortest-path oracle, graph adapter or finite-source-size premise is assumed. -/
theorem active_walk_to_simple {V : Type u} (G : MarkedGraph V) (laws : MixedLaws G)
    (C : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C (AncestorOf G C)) p xs q) :
    ∃ r ys, Route (Transition G C (AncestorOf G C)) p ys r ∧
      r.vertex = q.vertex ∧ ((p :: ys).map Arrival.vertex).Nodup := by
  classical
  induction h with
  | nil p => exact ⟨p, [], .nil p, rfl, List.nodup_singleton p.vertex⟩
  | @cons p q r xs hpq hqr ih =>
      obtain ⟨last, ys, hy, hlast, hnd⟩ := ih
      by_cases hmem : p.vertex ∈ (q :: ys).map Arrival.vertex
      · obtain ⟨at, hat, hvertex⟩ := List.mem_map.mp hmem
        obtain ⟨prefix, hprefix⟩ := hy.prefix_of_mem hat
        obtain ⟨suffix, hsuffix, hsub⟩ := hy.suffix_of_mem hat
        have hloop := Route.cons hpq hprefix
        have hshort := hnd.sublist (List.Sublist.map Arrival.vertex hsub)
        cases hsuffix with
        | nil =>
            exact ⟨p, [], .nil p, hvertex.symm.trans hlast,
              List.nodup_singleton p.vertex⟩
        | @cons at next last tail hstep htail =>
            refine ⟨last, next :: tail, .cons ?_ htail, hlast, ?_⟩
            · exact splice_departure G laws C hloop hvertex.symm hstep
            · simpa only [List.map_cons, hvertex] using hshort
      · exact ⟨last, q :: ys, .cons hpq hy, hlast, List.Nodup.cons hmem hnd⟩

end RestrictedCausal.ActiveWalkReduction
