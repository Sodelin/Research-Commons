import FiniteProfileRegistry

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Actual activity/ancestry semantics for the canonical hidden-root expansion.
This file is part of the original full selected-source dependency graph.
-/

namespace RestrictedCausal.SelectedWalk

universe u

/-- Uniform hidden incidences generalize the selected-head case. Hidden roots
have uniform tails and are unconditioned; selection vertices have uniform heads. -/
def UniformIncidences {V : Type u} (G : MarkedGraph V) (H : V → Prop) (mark : Mark) : Prop :=
  ∀ a b ma mb, G.edge a b ma mb → (H a → ma = mark) ∧ (H b → mb = mark)

theorem uniform_arrival_marks {V : Type u} {G : MarkedGraph V}
    {C A H : V → Prop} {mark : Mark} (uniform : UniformIncidences G H mark)
    {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C A) p xs q)
    (initial : H p.vertex → p.incoming = some mark) :
    ∀ r ∈ p :: xs, H r.vertex → r.incoming = some mark := by
  revert initial
  induction h with
  | nil p =>
      intro initial r hr
      have hrp : r = p := by simpa only [List.mem_singleton] using hr
      subst r
      exact initial
  | @cons p q r xs hpq hqr ih =>
      intro initial z hz
      rcases List.mem_cons.mp hz with hzp | hz
      · subst z
        exact initial
      · apply ih _ z hz
        intro hq
        obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hpq
        exact hmark.trans (congrArg some ((uniform _ _ _ _ hedge).2 hq))

theorem uniform_vertex_nodup {V : Type u} {H : V → Prop} {mark : Mark}
    {xs : List (Arrival V)} (hnd : xs.Nodup) (hobs : NoObservedRepeat H xs)
    (marks : ∀ p ∈ xs, H p.vertex → p.incoming = some mark) :
    (xs.map Arrival.vertex).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.Pairwise.and hnd hobs).imp_of_mem
  intro p q hp hq hpair heq
  have hhp : H p.vertex := hpair.2 heq
  have hhq : H q.vertex := heq ▸ hhp
  exact hpair.1 (Arrival.eq_of_fields heq
    ((marks p hp hhp).trans (marks q hq hhq).symm))

theorem uniform_walk_to_simple_path {V : Type u} {G : MarkedGraph V}
    {C A H : V → Prop} {mark : Mark} (uniform : UniformIncidences G H mark)
    {x : V} {q : Arrival V} {xs : List (Arrival V)} (hx : ¬ H x)
    (h : Route (Transition G C A) ⟨x, none⟩ xs q)
    (hobs : NoObservedRepeat H (⟨x, none⟩ :: xs)) :
    ∃ ys, Route (Transition G C A) ⟨x, none⟩ ys q ∧
      ((⟨x, none⟩ :: ys).map Arrival.vertex).Nodup ∧
      (⟨x, none⟩ :: ys) <+ (⟨x, none⟩ :: xs) := by
  obtain ⟨ys, hy, hnd, hsub⟩ := h.exists_simple_subroute
  have marks := uniform_arrival_marks uniform h (fun hh => (hx hh).elim)
  refine ⟨ys, hy, uniform_vertex_nodup hnd (hobs.sublist hsub) ?_, hsub⟩
  intro p hp hh
  exact marks p (hsub.subset hp) hh

end RestrictedCausal.SelectedWalk

namespace RestrictedCausal.LatentRoots

open SelectedWalk CanonicalSelection
open SourceSelection (AncestorOf)

universe u

def hidden {V : Type u} [LinearOrder V] {G : MarkedGraph V} : Vertex G → Prop
  | .inl _ => False
  | .inr _ => True

theorem root_incidence_tails {V : Type u} [LinearOrder V] (G : MarkedGraph V) :
    UniformIncidences (dagGraph G) hidden .tail := by
  intro a b ma mb hedge
  cases a with
  | inl x =>
      cases b with
      | inl y => exact ⟨False.elim, False.elim⟩
      | inr r =>
          exact ⟨False.elim, fun _ => ((obs_root_marks G x r ma mb).mp hedge).2.2⟩
  | inr r =>
      cases b with
      | inl y =>
          exact ⟨fun _ => ((root_obs_marks G r y ma mb).mp hedge).2.1, False.elim⟩
      | inr s => exact (no_root_adjacency G r s ma mb hedge).elim

def liftCondition {V : Type u} [LinearOrder V] {G : MarkedGraph V}
    (C : V → Prop) : Vertex G → Prop
  | .inl x => C x
  | .inr _ => False

theorem retained_ancestry_exact {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (x y : V) :
    Reach (dagGraph G) (.inl x) (.inl y) ↔ Reach G x y := by
  constructor
  · rintro ⟨xs, h⟩
    have hp := h.map id (fun a b hab => (dag_directed_exact G a b).mp hab)
    have hp' : Route (Arrow G) (.inl x) xs (.inl y) := by
      simpa only [List.map_id] using hp
    obtain ⟨z, zs, hyz, _, hz⟩ := observed_route G hp' x rfl
    have heq : y = z := Sum.inl.inj hyz
    subst z
    exact ⟨zs, hz⟩
  · rintro ⟨xs, h⟩
    exact ⟨_, h.map (fun z => Sum.inl z : V → Vertex G)
      (fun a b hab => (dag_directed_exact G (.inl a) (.inl b)).mpr hab)⟩

theorem retained_condition_ancestry {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (C : V → Prop) (x : V) :
    AncestorOf (dagGraph G) (liftCondition C) (.inl x) ↔ AncestorOf G C x := by
  constructor
  · rintro ⟨v, hp, hc⟩
    cases v with
    | inl y => exact ⟨y, (retained_ancestry_exact G x y).mp hp, hc⟩
    | inr r => exact hc.elim
  · rintro ⟨y, hp, hc⟩
    exact ⟨.inl y, (retained_ancestry_exact G x y).mpr hp, hc⟩

theorem retained_activity_iff {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (C : V → Prop) (x : V) (incoming outgoing : Mark) :
    ActiveAt (liftCondition C) (AncestorOf (dagGraph G) (liftCondition C))
      (.inl x) incoming outgoing ↔
    ActiveAt C (AncestorOf G C) x incoming outgoing := by
  by_cases hcollider : incoming = .head ∧ outgoing = .head
  · simp only [ActiveAt, if_pos hcollider]
    exact retained_condition_ancestry G C x
  · simp only [ActiveAt, if_neg hcollider]
    exact Iff.rfl

def retainedState {V : Type u} [LinearOrder V] {G : MarkedGraph V}
    (p : Arrival V) : Arrival (Vertex G) := ⟨.inl p.vertex, p.incoming⟩

def rootState {V : Type u} [LinearOrder V] {G : MarkedGraph V}
    (r : Root G) : Arrival (Vertex G) := ⟨.inr r, some .tail⟩

/-- A full marked observed edge lifts to one direct arrow or one real latent
fork. Hidden-root activity is proved from its two tails and nonconditioning. -/
theorem lift_marked_edge {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) (C : V → Prop) {x y : V} {mx my : Mark}
    {previous : Option Mark} (hedge : G.edge x y mx my)
    (hactive : match previous with
      | none => True
      | some m => ActiveAt C (AncestorOf G C) x m mx) :
    ∃ middle : List (Arrival (Vertex G)),
      (∀ p ∈ middle, hidden p.vertex) ∧
      Route (Transition (dagGraph G) (liftCondition C)
        (AncestorOf (dagGraph G) (liftCondition C)))
        (retainedState ⟨x, previous⟩)
        (middle ++ [retainedState ⟨y, some my⟩]) (retainedState ⟨y, some my⟩) := by
  have hleft : match previous with
      | none => True
      | some m => ActiveAt (liftCondition C)
          (AncestorOf (dagGraph G) (liftCondition C)) (.inl x) m mx := by
    cases previous with
    | none => trivial
    | some m => exact (retained_activity_iff G C x m mx).mpr hactive
  rcases (root_projection_exact G laws x y mx my).mpr hedge with ⟨_, hdir | ⟨r, hx, hy⟩⟩
  · exact ⟨[], (by intro p hp; cases hp),
      .cons ⟨mx, my, hdir, rfl, hleft⟩ (.nil _)⟩
  · refine ⟨[rootState r], ?_, .cons ?_ (.cons ?_ (.nil _))⟩
    · intro p hp
      have heq : p = rootState r := by simpa only [List.mem_singleton] using hp
      subst p
      trivial
    · exact ⟨mx, .tail, hx, rfl, hleft⟩
    · refine ⟨.tail, my, hy, rfl, ?_⟩
      simp [rootState, ActiveAt, liftCondition]

theorem lift_active_route {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) (C : V → Prop) {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C (AncestorOf G C)) p xs q) :
    ∃ ys, Route (Transition (dagGraph G) (liftCondition C)
        (AncestorOf (dagGraph G) (liftCondition C))) (retainedState p) ys (retainedState q) ∧
      ys.filterMap SourceSelection.observedValue = xs.map Arrival.vertex := by
  induction h with
  | nil p => exact ⟨[], .nil _, rfl⟩
  | @cons p q r xs hpq hqr ih =>
      obtain ⟨ys, hy, htrace⟩ := ih
      obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hpq
      obtain ⟨middle, hhidden, hblock⟩ := lift_marked_edge G laws C hedge hactive
      have hq : retainedState (G := G) ⟨q.vertex, some incoming⟩ = retainedState q := by
        apply Arrival.eq_of_fields
        · rfl
        · exact hmark.symm
      rw [hq] at hblock
      refine ⟨(middle ++ [retainedState q]) ++ ys, hblock.append hy, ?_⟩
      have hmiddle : middle.filterMap SourceSelection.observedValue = [] :=
        SourceSelection.selected_trace_nil hhidden
      simp only [List.filterMap_append, hmiddle, List.nil_append]
      rw [htrace]
      rfl

def ActiveConnection {V : Type u} (G : MarkedGraph V) (C : V → Prop) (x y : V) : Prop :=
  ∃ lastMark xs, Route (Transition G C (AncestorOf G C)) ⟨x, none⟩ xs ⟨y, lastMark⟩ ∧
    ((⟨x, none⟩ :: xs).map Arrival.vertex).Nodup

theorem lift_active_connection {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) (C : V → Prop) (x y : V)
    (h : ActiveConnection G C x y) :
    ActiveConnection (dagGraph G) (liftCondition C) (.inl x) (.inl y) := by
  obtain ⟨lastMark, xs, hp, hsimple⟩ := h
  obtain ⟨ys, hy, htrace⟩ := lift_active_route G laws C hp
  have hobs : NoObservedRepeat hidden (retainedState ⟨x, none⟩ :: ys) := by
    apply (SourceSelection.noObservedRepeat_iff_trace_nodup _).mpr
    change (x :: ys.filterMap SourceSelection.observedValue).Nodup
    rw [htrace]
    exact hsimple
  obtain ⟨zs, hz, hnd, _⟩ := uniform_walk_to_simple_path (root_incidence_tails G)
    (fun hfalse => hfalse) hy hobs
  exact ⟨lastMark, zs, hz, hnd⟩

theorem retained_optional_activity_iff {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (C : V → Prop) (x : V) (previous : Option Mark) (outgoing : Mark) :
    (match previous with
      | none => True
      | some m => ActiveAt (liftCondition C)
          (AncestorOf (dagGraph G) (liftCondition C)) (.inl x) m outgoing) ↔
    (match previous with
      | none => True
      | some m => ActiveAt C (AncestorOf G C) x m outgoing) := by
  cases previous with
  | none => exact Iff.rfl
  | some m => exact retained_activity_iff G C x m outgoing

theorem contract_root_route_aux {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) (C : V → Prop) (n : Nat) :
    ∀ (x : V) (previous : Option Mark) (xs : List (Arrival (Vertex G)))
      (y : V) (lastMark : Option Mark), xs.length = n →
      Route (Transition (dagGraph G) (liftCondition C)
        (AncestorOf (dagGraph G) (liftCondition C)))
        (retainedState ⟨x, previous⟩) xs (retainedState ⟨y, lastMark⟩) →
      NoObservedRepeat hidden (retainedState ⟨x, previous⟩ :: xs) →
      ∃ ys, Route (Transition G C (AncestorOf G C)) ⟨x, previous⟩ ys ⟨y, lastMark⟩ ∧
        ys.map Arrival.vertex = xs.filterMap SourceSelection.observedValue := by
  refine Nat.strongRecOn n ?_
  intro n ih x previous xs y lastMark hlen h hobs
  cases xs with
  | nil =>
      cases h
      exact ⟨[], .nil _, rfl⟩
  | cons next rest =>
      cases h with
      | cons hfirst htail =>
          rcases next with ⟨nv, nm⟩
          obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hfirst
          change nm = some incoming at hmark
          subst nm
          cases nv with
          | inl z =>
              have hne : x ≠ z := by
                intro hxz
                have hbad := List.rel_of_pairwise_cons hobs List.mem_cons_self
                  (congrArg Sum.inl hxz)
                exact hbad
              have hgz : G.edge x z outgoing incoming :=
                (root_projection_exact G laws x z outgoing incoming).mp ⟨hne, Or.inl hedge⟩
              have hlt : rest.length < n := by simp only [List.length_cons] at hlen; omega
              obtain ⟨ys, hy, htrace⟩ := ih rest.length hlt z (some incoming) rest y lastMark
                rfl htail (List.Pairwise.of_cons hobs)
              refine ⟨⟨z, some incoming⟩ :: ys, .cons ?_ hy, ?_⟩
              · exact ⟨outgoing, incoming, hgz, rfl,
                  (retained_optional_activity_iff G C x previous outgoing).mp hactive⟩
              · exact congrArg (List.cons z) htrace
          | inr r =>
              have hin : incoming = .tail := ((obs_root_marks G x r outgoing incoming).mp hedge).2.2
              subst incoming
              cases rest with
              | nil => cases htail
              | cons after remaining =>
                  cases htail with
                  | cons hsecond hrest =>
                      rcases after with ⟨av, am⟩
                      obtain ⟨secondOut, secondIn, secondEdge, secondMark, _⟩ := hsecond
                      change am = some secondIn at secondMark
                      subst am
                      cases av with
                      | inr s => exact (no_root_adjacency G r s secondOut secondIn secondEdge).elim
                      | inl z =>
                          have hout : secondOut = .tail :=
                            ((root_obs_marks G r z secondOut secondIn).mp secondEdge).2.1
                          subst secondOut
                          have hne : x ≠ z := by
                            intro hxz
                            have hbad := List.rel_of_pairwise_cons hobs
                              (List.mem_cons_of_mem _ List.mem_cons_self) (congrArg Sum.inl hxz)
                            exact hbad
                          have hgz : G.edge x z outgoing secondIn :=
                            (root_projection_exact G laws x z outgoing secondIn).mp
                              ⟨hne, Or.inr ⟨r, hedge, secondEdge⟩⟩
                          have hlt : remaining.length < n := by
                            simp only [List.length_cons] at hlen
                            omega
                          obtain ⟨ys, hy, htrace⟩ := ih remaining.length hlt z (some secondIn)
                            remaining y lastMark rfl hrest
                            (List.Pairwise.of_cons (List.Pairwise.of_cons hobs))
                          refine ⟨⟨z, some secondIn⟩ :: ys, .cons ?_ hy, ?_⟩
                          · exact ⟨outgoing, secondIn, hgz, rfl,
                              (retained_optional_activity_iff G C x previous outgoing).mp hactive⟩
                          · exact congrArg (List.cons z) htrace

theorem contract_root_route {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) (C : V → Prop) {x y : V} {previous lastMark : Option Mark}
    {xs : List (Arrival (Vertex G))}
    (h : Route (Transition (dagGraph G) (liftCondition C)
      (AncestorOf (dagGraph G) (liftCondition C)))
      (retainedState ⟨x, previous⟩) xs (retainedState ⟨y, lastMark⟩))
    (hobs : NoObservedRepeat hidden (retainedState ⟨x, previous⟩ :: xs)) :
    ∃ ys, Route (Transition G C (AncestorOf G C)) ⟨x, previous⟩ ys ⟨y, lastMark⟩ ∧
      ys.map Arrival.vertex = xs.filterMap SourceSelection.observedValue :=
  contract_root_route_aux G laws C xs.length x previous xs y lastMark rfl h hobs

theorem contract_active_connection {V : Type u} [LinearOrder V] (G : MarkedGraph V)
    (laws : MixedLaws G) (C : V → Prop) (x y : V)
    (h : ActiveConnection (dagGraph G) (liftCondition C) (.inl x) (.inl y)) :
    ActiveConnection G C x y := by
  obtain ⟨lastMark, xs, hp, hsimple⟩ := h
  have hobs := SourceSelection.noObservedRepeat_of_vertex_nodup hsimple
  obtain ⟨ys, hy, htrace⟩ := contract_root_route G laws C hp hobs
  have hnd := (SourceSelection.noObservedRepeat_iff_trace_nodup _).mp hobs
  refine ⟨lastMark, ys, hy, ?_⟩
  change (x :: ys.map Arrival.vertex).Nodup
  rw [htrace]
  exact hnd

/-- Actual two-way separation semantics for the canonical hidden-root DAG,
including arbitrary conditioning on retained selection vertices. No generic
latent-projection separation axiom is invoked in this particular construction. -/
theorem root_active_connection_iff {V : Type u} [LinearOrder V]
    (G : MarkedGraph V) (laws : MixedLaws G) (C : V → Prop) (x y : V) :
    ActiveConnection (dagGraph G) (liftCondition C) (.inl x) (.inl y) ↔
      ActiveConnection G C x y :=
  ⟨contract_active_connection G laws C x y, lift_active_connection G laws C x y⟩

end RestrictedCausal.LatentRoots

namespace RestrictedCausal.SourceSelection

open SelectedWalk CanonicalSelection

universe u v

/-- Baseline composition to the actual bounded canonical DAG. The selectors
are retained and conditioned; the added common-cause roots are unconditioned.
The original source's selection carrier remains arbitrary in this statement. -/
theorem canonical_dag_selected_preservation {X : Type u} {S : Type v}
    [LinearOrder X] (H : SelectedGraph X S)
    (laws : LatentRoots.MixedLaws H.observed)
    [LinearOrder (CanonicalSelection.Vertex (profile H))]
    (Z : X → Prop) (x y : X) :
    ActivePath H Z x y ↔
      LatentRoots.ActiveConnection
        (LatentRoots.dagGraph (graph (canonical (profile H))))
        (LatentRoots.liftCondition (Condition Z))
        (.inl (.inl x)) (.inl (.inl y)) := by
  have hcanonical := canonical_activePath_iff H Z x y
  have hroots := LatentRoots.root_active_connection_iff
    (graph (canonical (profile H))) (canonical_mixed_laws (profile H) laws)
    (Condition Z) (.inl x) (.inl y)
  exact hcanonical.trans hroots.symm

theorem canonical_dag_selection_sinks {X : Type u} [LinearOrder X]
    (Q : Profile X) [LinearOrder (CanonicalSelection.Vertex Q)]
    (s : Selector Q) (b : LatentRoots.Vertex (graph (canonical Q))) :
    ¬ LatentRoots.Arrow (graph (canonical Q)) (.inl (.inr s)) b :=
  LatentRoots.retained_sink_stays_sink (graph (canonical Q)) (.inr s)
    (no_selected_departure (canonical Q) s) b

end RestrictedCausal.SourceSelection
