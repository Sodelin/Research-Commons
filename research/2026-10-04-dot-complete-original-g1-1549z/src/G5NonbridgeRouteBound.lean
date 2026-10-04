import G5CalendarRoutes
import Mathlib.Data.Fintype.Card

/-!
# Original cut-child nonbridge routes have at most two choices

New proof contribution: dot's active Lean source-bridge lane, 2026-10-02.
We use original edge occurrences, including parallel arcs. The generic proof
needs only acyclicity and unique incoming edges at sources of kept edges.
The actual binary cut-child source supplies this uniqueness for nonbridges:
a hybrid cannot be the source of a nonbridge, since its child is a bridge.
A rootward nonbridge route is consequently fixed by its first parent edge.
This is the graph core of the two-route current-blob claim, not a stochastic
route probability, calendar compiler, or full G5 identification theorem.
-/

namespace GProgram.G5.NonbridgeRoutes

open Nanuq.Source

variable {V E : Type*}

/-- Rootward paths explicitly retain all original edge occurrence IDs. -/
inductive UpPath (G : EdgeGraph V E) (keep : E → Prop) : V → V → List E → Prop
  | nil (a : V) : UpPath G keep a a []
  | cons {a b : V} {e : E} {es : List E}
      (ht : G.target e = a) (he : keep e)
      (rest : UpPath G keep (G.source e) b es) : UpPath G keep a b (e :: es)

theorem UpPath.directed {G : EdgeGraph V E} {keep : E → Prop}
    {a b : V} {es : List E} (p : UpPath G keep a b es) : G.DReach b a := by
  induction p with
  | nil => exact .refl
  | cons ht _ rest ih =>
    exact ih.tail ⟨_, rfl, ht⟩

theorem UpPath.nonempty_start_ne_end {G : EdgeGraph V E} {keep : E → Prop}
    (ha : G.Acyclic) {a b : V} {e : E} {es : List E}
    (p : UpPath G keep a b (e :: es)) : a ≠ b := by
  intro hab
  cases p with
  | cons ht he rest =>
    subst b
    exact ha a (Relation.TransGen.tail' rest.directed ⟨e, rfl, ht⟩)

/-- Once an original parent edge is selected, the whole remaining rootward
kept-edge route is unique. This premise is local degree information, not the
route uniqueness conclusion itself. -/
theorem UpPath.unique_from_kept_source {G : EdgeGraph V E} {keep : E → Prop}
    (ha : G.Acyclic)
    (hu : ∀ e, keep e → ∀ f g, G.target f = G.source e →
      G.target g = G.source e → f = g)
    {a b : V} {es fs : List E} (p : UpPath G keep a b es)
    (q : UpPath G keep a b fs)
    (hsource : ∃ e, keep e ∧ G.source e = a) : es = fs := by
  induction p generalizing fs with
  | nil a =>
    cases q with
    | nil => rfl
    | cons ht he rest =>
      exact False.elim ((UpPath.cons ht he rest).nonempty_start_ne_end ha rfl)
  | @cons a b e es ht he rest ih =>
    cases q with
    | nil =>
      exact False.elim ((UpPath.cons ht he rest).nonempty_start_ne_end ha rfl)
    | @cons _ _ f fs htf hf tail =>
      obtain ⟨g, hg, hgs⟩ := hsource
      have hef : e = f := hu g hg e f (ht.trans hgs.symm) (htf.trans hgs.symm)
      subst f
      congr 1
      exact ih tail ⟨e, he, rfl⟩

/-- First-parent-edge equality already determines the complete nonbridge
route, even when the endpoint itself has two parent edges. -/
theorem UpPath.unique_of_same_first {G : EdgeGraph V E} {keep : E → Prop}
    (ha : G.Acyclic)
    (hu : ∀ e, keep e → ∀ f g, G.target f = G.source e →
      G.target g = G.source e → f = g)
    {a b : V} {e : E} {es fs : List E}
    (p : UpPath G keep a b (e :: es)) (q : UpPath G keep a b (e :: fs)) : es = fs := by
  cases p with
  | cons ht he rest =>
    cases q with
    | cons htf hf tail =>
      exact rest.unique_from_kept_source ha hu tail ⟨e, he, rfl⟩

section OriginalSource

variable {X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem incoming_equal_of_indegree_le_one (N : RootedBinary V E X) {v : V}
    (hdeg : N.graph.inDegree v ≤ 1) {e f : E}
    (he : N.graph.target e = v) (hf : N.graph.target f = v) : e = f := by
  classical
  exact Finset.card_le_one.mp hdeg e (by simp [he]) f (by simp [hf])

theorem nonhybrid_indegree_le_one (N : RootedBinary V E X) {v : V}
    (hv : ¬ N.graph.IsHybrid v) : N.graph.inDegree v ≤ 1 := by
  by_cases hr : v = N.root
  · rw [hr, N.root_degrees.1]
    omega
  · by_cases hl : ∃ x, N.leaf x = v
    · obtain ⟨x, rfl⟩ := hl
      rw [(N.leaf_degrees x).1]
    · rcases N.internal_degrees v hr (fun x hx => hl ⟨x, hx⟩) with ht | hh
      · rw [ht.1]
      · exact False.elim (hv hh)

theorem cut_child_nonbridge_incoming_unique (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (e : E) (he : ¬ N.graph.IsBridge e) (f g : E)
    (hf : N.graph.target f = N.graph.source e)
    (hg : N.graph.target g = N.graph.source e) : f = g := by
  apply incoming_equal_of_indegree_le_one N
    (nonhybrid_indegree_le_one N (fun hh => he (hcut e hh))) hf hg

/-- Actual binary cut-child source consequence. Selecting one of a hybrid's
at most two original parents fixes the rest of its nonbridge route. -/
theorem original_nonbridge_route_unique_of_first (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} {e : E} {es fs : List E}
    (p : UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b (e :: es))
    (q : UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b (e :: fs)) : es = fs := by
  exact p.unique_of_same_first N.acyclic (cut_child_nonbridge_incoming_unique N hcut) q

/-- Every finite family of distinct original nonbridge routes has cardinal
at most the actual incoming edge-occurrence count of its starting port. -/
theorem finite_nonbridge_route_family_card_le_indegree (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} (hab : a ≠ b) (R : Finset (List E))
    (hR : ∀ es ∈ R, UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b es) :
    R.card ≤ N.graph.inDegree a := by
  classical
  let incoming : Finset E := Finset.univ.filter (fun e => N.graph.target e = a)
  have hmap : Set.MapsTo List.head? (R : Set (List E))
      ((incoming.image Option.some) : Set (Option E)) := by
    intro es hes
    have hp := hR es hes
    cases es with
    | nil => cases hp; exact False.elim (hab rfl)
    | cons e tail =>
      cases hp with
      | cons ht _ _ =>
        simp only [List.head?_cons, Finset.mem_coe, Finset.mem_image]
        exact ⟨e, by simp [incoming, ht], rfl⟩
  have hinj : Set.InjOn List.head? (R : Set (List E)) := by
    intro es hes fs hfs heq
    have hp := hR es hes
    have hq := hR fs hfs
    cases es with
    | nil => cases hp; exact False.elim (hab rfl)
    | cons e tail =>
      cases fs with
      | nil => simp at heq
      | cons f rest =>
        simp only [List.head?_cons, Option.some.injEq] at heq
        subst f
        exact congrArg (List.cons e) (original_nonbridge_route_unique_of_first N hcut hp hq)
  have hc := Finset.card_le_card_of_injOn List.head? hmap hinj
  simpa only [Finset.card_image_of_injective incoming (Option.some_injective E), incoming, EdgeGraph.inDegree] using hc

/-- At a genuine hybrid port there are at most TWO original nonbridge routes
through the current component. Parallel parents still count as distinct choices. -/
theorem hybrid_nonbridge_route_family_card_le_two (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} (ha : N.graph.IsHybrid a) (hab : a ≠ b) (R : Finset (List E))
    (hR : ∀ es ∈ R, UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b es) :
    R.card ≤ 2 := by
  simpa only [ha.1] using finite_nonbridge_route_family_card_le_indegree N hcut hab R hR

/-- At an ordinary port the same actual-source argument supplies at most ONE
route, without assuming a canonical blob, planar embedding, or route oracle. -/
theorem ordinary_nonbridge_route_family_card_le_one (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} (ha : ¬ N.graph.IsHybrid a) (hab : a ≠ b) (R : Finset (List E))
    (hR : ∀ es ∈ R, UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b es) :
    R.card ≤ 1 := by
  exact (finite_nonbridge_route_family_card_le_indegree N hcut hab R hR).trans
    (nonhybrid_indegree_le_one N ha)

end OriginalSource

#print axioms UpPath.unique_from_kept_source
#print axioms UpPath.unique_of_same_first
#print axioms cut_child_nonbridge_incoming_unique
#print axioms original_nonbridge_route_unique_of_first
#print axioms finite_nonbridge_route_family_card_le_indegree
#print axioms hybrid_nonbridge_route_family_card_le_two
#print axioms ordinary_nonbridge_route_family_card_le_one

end GProgram.G5.NonbridgeRoutes
