import G5ComponentCalendarCoverage

/-!
# Actual component calendar support is bounded by original port indegree

Contributor: dot, 2026-10-02. Original directed edge-occurrence paths are
reversed into the rootward nonbridge representation. Current populations are
then defined by active edges on ALL actual nonbridge component paths. Their
support bound is derived from original binary cut-child degrees and strict
calendar clocks; neither a route oracle nor the desired support bound is an
interface assumption. Source coin probabilities and observed chronology are
separate obligations.
-/

namespace GProgram.G5.NonbridgeRoutes
open Nanuq.Source
variable {V E : Type*}

theorem UpPath.append {G : EdgeGraph V E} {keep : E → Prop}
    {a b c : V} {es fs : List E} (p : UpPath G keep a b es)
    (q : UpPath G keep b c fs) : UpPath G keep a c (es ++ fs) := by
  induction p with
  | nil => exact q
  | cons ht he rest ih => exact .cons ht he (ih q)

theorem EdgePath.to_upPath_reverse {G : EdgeGraph V E} {keep : E → Prop}
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    (hk : ∀ e ∈ es, keep e) : UpPath G keep b a es.reverse := by
  induction p with
  | nil a => exact .nil a
  | @cons a b e es hs rest ih =>
    have hr := ih (fun f hf => hk f (List.mem_cons_of_mem e hf))
    have he : UpPath G keep (G.target e) a [e] := by
      exact .cons rfl (hk e List.mem_cons_self) (by rw [hs]; exact .nil a)
    simpa only [List.reverse_cons] using hr.append he

#print axioms UpPath.append
#print axioms EdgePath.to_upPath_reverse
end GProgram.G5.NonbridgeRoutes

namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- ALL original nonbridge paths from a component entry to a port contribute
current population edges. The definition contains no support cardinal bound. -/
noncomputable def activeComponentEdges (G : EdgeGraph V E) (C : Calendar G)
    (entry port : V) (t : ℝ) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ∃ es : List E,
    EdgePath G entry port es ∧ (∀ f ∈ es, ¬G.IsBridge f) ∧
    e ∈ es ∧ C.Active t e)

theorem mem_activeComponentEdges_iff (G : EdgeGraph V E) (C : Calendar G)
    (entry port : V) (t : ℝ) (e : E) :
    e ∈ activeComponentEdges G C entry port t ↔ ∃ es : List E,
      EdgePath G entry port es ∧ (∀ f ∈ es, ¬G.IsBridge f) ∧
      e ∈ es ∧ C.Active t e := by
  classical
  simp only [activeComponentEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Distinct actual current population edges require distinct original routes:
strict calendar clocks permit only one active edge along any one route. -/
theorem finite_active_nonbridge_edges_card_le_indegree
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {entry port : V} (hne : port ≠ entry) (t : ℝ) (A : Finset E)
    (hA : ∀ e ∈ A, ∃ es : List E, EdgePath N.graph entry port es ∧
      (∀ f ∈ es, ¬N.graph.IsBridge f) ∧ e ∈ es ∧ C.Active t e) :
    A.card ≤ N.graph.inDegree port := by
  classical
  have hw : ∀ u : {e // e ∈ A}, ∃ es : List E,
      EdgePath N.graph entry port es ∧
      (∀ f ∈ es, ¬N.graph.IsBridge f) ∧ u.val ∈ es ∧ C.Active t u.val :=
    fun u => hA u.val u.property
  choose route hroute using hw
  let R : Finset (List E) := A.attach.image (fun u => (route u).reverse)
  have hR : ∀ es ∈ R,
      UpPath N.graph (fun f => ¬N.graph.IsBridge f) port entry es := by
    intro es hes
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hes
    exact GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse (hroute u).1 (hroute u).2.1
  have hi : Function.Injective (fun u : {e // e ∈ A} => (route u).reverse) := by
    intro u v huv
    have huv' : route u = route v := List.reverse_inj.mp huv
    apply Subtype.ext
    exact (hroute u).1.active_unique C (hroute u).2.2.1
      (by simpa only [huv'] using (hroute v).2.2.1)
      (hroute u).2.2.2 (hroute v).2.2.2
  have hcard : R.card = A.card := by
    simp only [R, Finset.card_image_of_injective _ hi, Finset.card_attach]
  rw [← hcard]
  exact finite_nonbridge_route_family_card_le_indegree N hcut hne R hR

/-- The original source degree theorem bounds the defined actual active support. -/
theorem activeComponentEdges_card_le_indegree
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {entry port : V} {t : ℝ} (hl : C.age port ≤ t) (hu : t < C.age entry) :
    (activeComponentEdges N.graph C entry port t).card ≤ N.graph.inDegree port := by
  have hne : port ≠ entry := by
    intro h
    rw [h] at hl
    exact not_lt_of_ge hl hu
  apply finite_active_nonbridge_edges_card_le_indegree N C hcut hne t
  intro e he
  exact (mem_activeComponentEdges_iff N.graph C entry port t e).mp he

#print axioms finite_active_nonbridge_edges_card_le_indegree
#print axioms activeComponentEdges_card_le_indegree
end GProgram.G5.ComponentSupport
