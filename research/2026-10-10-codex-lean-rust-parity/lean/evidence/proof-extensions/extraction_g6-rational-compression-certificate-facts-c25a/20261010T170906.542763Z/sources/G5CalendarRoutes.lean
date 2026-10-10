import G5BridgeBarrier
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Calendar route test for the protective child-bridge assumption

New proof contribution: dot's dedicated Lean lane, 2026-10-01.
An original route is a finite list of original directed edge IDs, from the
original root to one selected tip. No pruned source or sampled ancestor is
substituted. An active population uses the older-side convention
age(target) <= t < age(source).

The module tests the deterministic source/calendar premise of G5. A stochastic
coalescent law, positive no-merger route probabilities, observed-germ recovery,
and the whole chronological algorithm are not encoded as hypotheses here.
-/

namespace GProgram.G5

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Strict original edge durations, without a source-replacement assumption. -/
structure Calendar (G : EdgeGraph V E) where
  age : V → ℝ
  edge_older : ∀ e, age (G.target e) < age (G.source e)

def Calendar.Active {G : EdgeGraph V E} (C : Calendar G) (t : ℝ) (e : E) : Prop :=
  C.age (G.target e) ≤ t ∧ t < C.age (G.source e)

/-- Explicit edge-ID paths, preserving parallel arcs. -/
inductive EdgePath (G : EdgeGraph V E) : V → V → List E → Prop
  | nil (a : V) : EdgePath G a a []
  | cons {a b : V} {e : E} {es : List E}
      (hs : G.source e = a) (rest : EdgePath G (G.target e) b es) :
      EdgePath G a b (e :: es)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.directed {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : EdgePath G a b es) : G.DReach a b := by
  induction p with
  | nil => exact .refl
  | cons hs rest ih =>
      exact (Relation.ReflTransGen.single ⟨_, hs, rfl⟩).trans ih

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.append {G : EdgeGraph V E} {a b c : V} {es fs : List E}
    (p : EdgePath G a b es) (q : EdgePath G b c fs) :
    EdgePath G a c (es ++ fs) := by
  induction p with
  | nil => exact q
  | cons hs rest ih => exact .cons hs (ih q)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem exists_edgePath_of_directed {G : EdgeGraph V E} {a b : V}
    (p : G.DReach a b) : ∃ es : List E, EdgePath G a b es := by
  induction p with
  | refl => exact ⟨[], .nil _⟩
  | @tail b c _ step ih =>
      obtain ⟨es, hp⟩ := ih
      obtain ⟨e, hs, ht⟩ := step
      have he : EdgePath G b c [e] := by
        exact .cons hs (by rw [ht]; exact .nil c)
      exact ⟨es ++ [e], hp.append he⟩

theorem original_tip_route_exists (N : RootedBinary V E X) (x : X) :
    ∃ es : List E, EdgePath N.graph N.root (N.leaf x) es :=
  exists_edgePath_of_directed (N.rooted (N.leaf x))

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem Calendar.age_le_of_directed {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} (p : G.DReach a b) : C.age b ≤ C.age a := by
  induction p with
  | refl => exact le_refl _
  | tail _ step ih =>
      obtain ⟨e, hs, ht⟩ := step
      have h := C.edge_older e
      rw [hs, ht] at h
      exact (le_of_lt h).trans ih

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.reach_without_of_not_mem {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E}
    (hne : e ∉ es) : G.ReachWithout e a b := by
  induction p with
  | nil => exact .refl
  | @cons a b f fs hs rest ih =>
      have hfe : f ≠ e := by
        intro hf
        exact hne (List.mem_cons.mpr (Or.inl hf.symm))
      have htail : e ∉ fs := fun hm => hne (List.mem_cons.mpr (Or.inr hm))
      exact (G.ureach_single ⟨f, hfe, Or.inl ⟨hs, rfl⟩⟩).trans (ih htail)

/-- Every original root-to-tip path to a downstream descendant crosses the
actual bridge edge, independent of the allowed parent choices along that path. -/
theorem bridge_mem_every_descendant_route (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) {x : X} {es : List E}
    (p : EdgePath N.graph N.root (N.leaf x) es)
    (hd : N.graph.DReach (N.graph.target e) (N.leaf x)) : e ∈ es := by
  classical
  by_contra hn
  have hr := p.reach_without_of_not_mem hn
  have hs := (N.root_on_source_side e).trans hr
  have ht := (bridge_selected_tip_iff N he x).mpr hd
  exact N.graph.bridge_sides_disjoint he hs ht

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.source_age_le {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E}
    (he : e ∈ es) : C.age (G.source e) ≤ C.age a := by
  induction p with
  | nil => simp at he
  | @cons a b f fs hs rest ih =>
      rcases List.mem_cons.mp he with hef | he
      · subst e
        rw [hs]
      · exact (ih he).trans (by
          have h := C.edge_older f
          rw [hs] at h
          exact le_of_lt h)

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- Strict edge ages make the active original population edge unique along
each complete route, including the older-side convention at node ages. -/
theorem EdgePath.active_unique {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : EdgePath G a b es)
    {t : ℝ} {e f : E} (he : e ∈ es) (hf : f ∈ es)
    (hae : C.Active t e) (haf : C.Active t f) : e = f := by
  induction p with
  | nil => simp at he
  | @cons a b g gs hs rest ih =>
      rcases List.mem_cons.mp he with heg | he
      · subst e
        rcases List.mem_cons.mp hf with hfg | hf
        · exact hfg.symm
        · have hsrc := rest.source_age_le C hf
          exact False.elim (not_lt_of_ge (hsrc.trans hae.1) haf.2)
      · rcases List.mem_cons.mp hf with hfg | hf
        · subst f
          have hsrc := rest.source_age_le C he
          exact False.elim (not_lt_of_ge (hsrc.trans haf.1) hae.2)
        · exact ih he hf

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.target_reaches_end_of_mem {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E}
    (he : e ∈ es) : G.DReach (G.target e) b := by
  induction p with
  | nil => simp at he
  | @cons a b f fs hs rest ih =>
      rcases List.mem_cons.mp he with hef | he
      · subst e
        exact rest.directed
      · exact ih he

/-- Throughout the protective child-edge interval, every descendant's original
route has exactly that edge as its active population. No law decoder is assumed. -/
theorem protective_edge_active_on_every_route (N : RootedBinary V E X)
    (C : Calendar N.graph) {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e)
    {x : X} (hd : N.graph.DReach h (N.leaf x)) {es : List E}
    (p : EdgePath N.graph N.root (N.leaf x) es) {t : ℝ}
    (ht : C.age (N.graph.target e) ≤ t ∧ t < C.age h) :
    e ∈ es ∧ C.Active t e ∧
      ∀ f ∈ es, C.Active t f → f = e := by
  have hdown := (descendant_via_unique_child N hh.2 hs
    (by intro hx; have hz := (N.leaf_degrees x).2; rw [← hx, hh.2] at hz; cases hz)).mp hd
  have hm := bridge_mem_every_descendant_route N he p hdown
  have ha : C.Active t e := by simpa only [Calendar.Active, hs] using ht
  exact ⟨hm, ha, fun f hf hfa => p.active_unique C hf hm hfa ha⟩

/-- No route from an outside tip can visit the hybrid's child population. -/
theorem protective_edge_absent_on_outside_route (N : RootedBinary V E X)
    {h : V} {e : E} (hs : N.graph.source e = h)
    {x : X} (hout : ¬ N.graph.DReach h (N.leaf x)) {es : List E}
    (p : EdgePath N.graph N.root (N.leaf x) es) : e ∉ es := by
  intro he
  apply hout
  exact (Relation.ReflTransGen.single ⟨e, hs, rfl⟩).trans
    (p.target_reaches_end_of_mem he)

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The source's strictly positive child-edge duration gives a nonempty
protective interval, with its youngest endpoint included. -/
theorem protective_interval_nonempty {G : EdgeGraph V E} (C : Calendar G) (e : E) :
    ∃ t : ℝ, C.Active t e :=
  ⟨C.age (G.target e), le_refl _, C.edge_older e⟩

/-- Assumption stress test: under the opposite endpoint convention a first
nontrivial block in this positive interval need not be attained. -/
theorem younger_side_open_interval_has_no_first :
    ¬ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ u : ℝ, 0 < u → u ≤ 1 → t ≤ u := by
  rintro ⟨t, ht, ht1, hmin⟩
  have h := hmin (t / 2) (by linarith) (by linarith)
  linarith

#print axioms bridge_mem_every_descendant_route
#print axioms original_tip_route_exists
#print axioms EdgePath.active_unique
#print axioms protective_edge_active_on_every_route
#print axioms protective_edge_absent_on_outside_route
#print axioms protective_interval_nonempty
#print axioms younger_side_open_interval_has_no_first

end GProgram.G5
