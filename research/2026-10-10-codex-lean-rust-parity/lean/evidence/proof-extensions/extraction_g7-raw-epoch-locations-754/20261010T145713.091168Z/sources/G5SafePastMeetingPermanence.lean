import G5PairOnlySureBlockChronology

/-!
# Actual original-route meetings cannot separate during an entire safe past

Contributor: dot, 2026-10-02. Rootward paths retain original parallel arc IDs.
Two routes with a common younger population can first diverge rootward only
at a hybrid. The entire-safe-past invariant excludes that shared hybrid, so
co-occupancy persists through every older safe calendar age. No survival law,
posterior route distribution or continuous stochastic process is assumed.
-/
namespace GProgram.G5.NonbridgeRoutes
open Nanuq.Source
variable {V E : Type*}

theorem UpPath.to_edgePath_reverse {G : EdgeGraph V E} {keep : E → Prop}
    {a b : V} {es : List E} (p : UpPath G keep a b es) :
    GProgram.G5.EdgePath G b a es.reverse := by
  induction p with
  | nil a => exact .nil a
  | @cons a b e es ht he rest ih =>
    have hs : GProgram.G5.EdgePath G (G.source e) a [e] :=
      .cons rfl (by rw [ht]; exact .nil _)
    simpa only [List.reverse_cons] using ih.append hs

#print axioms UpPath.to_edgePath_reverse
end GProgram.G5.NonbridgeRoutes

namespace GProgram.G5.SafePast
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Two selected descendants at a processed age cannot share that original
hybrid; the claim concerns the whole original descendant relation. -/
theorem shared_ancestor_not_hybrid (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) {t : ℝ} (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    {v : V} (hvx : N.graph.DReach v (N.leaf x))
    (hvy : N.graph.DReach v (N.leaf y)) (hvt : C.age v ≤ t) :
    ¬N.graph.IsHybrid v := by
  classical
  intro hh
  have hc := hsafe v hh hvt
  exact hne (Finset.card_le_one.mp hc x
    (Finset.mem_filter.mpr ⟨hx,hvx⟩) y (Finset.mem_filter.mpr ⟨hy,hvy⟩))

/-- Active populations of two rootward original paths agree if every shared
ancestor processed by this age is ordinary. This premise is vertex degree
information, not the active-edge equality conclusion. -/
theorem UpPath.active_edges_equal_of_no_processed_hybrid
    (N : RootedBinary V E X) (C : Calendar N.graph) {t : ℝ}
    {a b : V} {es fs : List E} (p : UpPath N.graph (fun _ => True) a b es)
    (q : UpPath N.graph (fun _ => True) a b fs)
    (hl : C.age a ≤ t) (hu : t < C.age b)
    (ho : ∀ v, N.graph.DReach v a → C.age v ≤ t → ¬N.graph.IsHybrid v)
    {f g : E} (hf : f ∈ es) (hg : g ∈ fs) (hfa : C.Active t f) (hga : C.Active t g) :
    f = g := by
  induction p generalizing fs f g with
  | nil a => exact False.elim (not_lt_of_ge hl hu)
  | @cons a b e es ht he rest ih =>
    cases q with
    | nil => exact False.elim (not_lt_of_ge hl hu)
    | @cons _ _ d ds htd hd qrest =>
      have hed : e = d := incoming_equal_of_indegree_le_one N
        (nonhybrid_indegree_le_one N (ho a .refl hl)) ht htd
      subst d
      by_cases hls : C.age (N.graph.source e) ≤ t
      · have hfn : f ≠ e := by
          intro h
          subst f
          exact not_lt_of_ge hls hfa.2
        have hgn : g ≠ e := by
          intro h
          subst g
          exact not_lt_of_ge hls hga.2
        have hft : f ∈ es := (List.mem_cons.mp hf).resolve_left hfn
        have hgt : g ∈ ds := (List.mem_cons.mp hg).resolve_left hgn
        apply ih qrest hls hu _ hft hgt hfa hga
        intro v hva hvage
        exact ho v (hva.tail ⟨e,rfl,ht⟩) hvage
      · have hae : C.Active t e := ⟨by simpa only [ht] using hl,lt_of_not_ge hls⟩
        have hfe : f = e := (UpPath.to_edgePath_reverse (.cons ht he rest)).active_unique
          C (List.mem_reverse.mpr hf) (List.mem_reverse.mpr List.mem_cons_self) hfa hae
        have hge : g = e := (UpPath.to_edgePath_reverse (.cons htd hd qrest)).active_unique
          C (List.mem_reverse.mpr hg) (List.mem_reverse.mpr List.mem_cons_self) hga hae
        exact hfe.trans hge.symm

/-- A younger original pair meeting persists to any older age covered by the
entire safe-past invariant. The routes themselves are arbitrary originals. -/
theorem coOccupy_persists_to_safe_age (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) (R : RouteFamily N)
    {u t : ℝ} (hut : u ≤ t) (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hmeeting : CoOccupy N R C u x y) : CoOccupy N R C t x y := by
  obtain ⟨e,hex,hey,heactive⟩ := hmeeting
  by_cases hls : C.age (N.graph.source e) ≤ t
  · obtain ⟨px,sx,hxroute,hpx,hsx⟩ :=
      GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge (R.valid x) hex
    obtain ⟨py,sy,hyroute,hpy,hsy⟩ :=
      GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge (R.valid y) hey
    obtain ⟨f,hfx,hfa⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C hpx hls hu
    obtain ⟨g,hgy,hga⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C hpy hls hu
    have hdx : N.graph.DReach (N.graph.source e) (N.leaf x) :=
      (Relation.ReflTransGen.single ⟨e,rfl,rfl⟩).trans hsx.directed
    have hdy : N.graph.DReach (N.graph.source e) (N.leaf y) :=
      (Relation.ReflTransGen.single ⟨e,rfl,rfl⟩).trans hsy.directed
    have hfg : f = g := UpPath.active_edges_equal_of_no_processed_hybrid N C
      (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hpx (fun _ _ => trivial))
      (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hpy (fun _ _ => trivial))
      hls hu (fun v hv hvage => shared_ancestor_not_hybrid N C B hsafe hx hy hne
        (hv.trans hdx) (hv.trans hdy) hvage)
      (List.mem_reverse.mpr hfx) (List.mem_reverse.mpr hgy) hfa hga
    subst g
    refine ⟨f,?_,?_,hfa⟩
    · rw [hxroute]
      exact List.mem_append_left _ hfx
    · rw [hyroute]
      exact List.mem_append_left _ hgy
  · exact ⟨e,hex,hey,heactive.1.trans hut,lt_of_not_ge hls⟩

/-- Contrapositive: current separation on a safe age means that these original
routes were separate at EVERY younger age, not just at the stage start. -/
theorem separated_at_safe_age_never_previously_met (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) (R : RouteFamily N)
    {t : ℝ} (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hseparate : ¬CoOccupy N R C t x y) :
    ∀ u : ℝ, u ≤ t → ¬CoOccupy N R C u x y := by
  intro u hut hm
  exact hseparate (coOccupy_persists_to_safe_age N C B R hut hu hsafe hx hy hne hm)

#print axioms shared_ancestor_not_hybrid
#print axioms UpPath.active_edges_equal_of_no_processed_hybrid
#print axioms coOccupy_persists_to_safe_age
#print axioms separated_at_safe_age_never_previously_met
end GProgram.G5.SafePast
