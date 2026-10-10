import G5RootRouteCurrentSupport

/-!
# The original binary cut-child source has at most two current port positions

Contributor: dot, 2026-10-02. The current component interval is specified only
by actual graph connectivity, original incoming bridges and original clocks.
The population support over all complete original root routes is nonempty and
has at most two edge occurrences there. Ordinary ports have at most one. This
is a graph/calendar source theorem, not a claim of fair coin probabilities,
merger-free sampling, or the full G5 identification theorem.
-/
namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Calendar interval inside the actual bridge-deleted component of a port. -/
def InCurrentComponentInterval (N : RootedBinary V E X) (C : Calendar N.graph)
    (port : V) (t : ℝ) : Prop :=
  C.age port ≤ t ∧
    ((N.graph.SameBlob N.root port ∧ t < C.age N.root) ∨
      ∃ entry : E, N.graph.IsBridge entry ∧
        N.graph.SameBlob (N.graph.target entry) port ∧
        t < C.age (N.graph.target entry))

theorem binary_indegree_le_two (N : RootedBinary V E X) (v : V) :
    N.graph.inDegree v ≤ 2 := by
  by_cases h : N.graph.IsHybrid v
  · exact le_of_eq h.1
  · exact (nonhybrid_indegree_le_one N h).trans (by decide)

/-- Actual current-component support of complete original root routes is
bounded by the actual incoming occurrence count of its port. -/
theorem current_port_support_card_le_indegree
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} {t : ℝ} (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ N.graph.inDegree port := by
  rcases ht with ⟨hl,⟨hb,hu⟩ | ⟨entry,he,hb,hu⟩⟩
  · rw [activeRootRouteEdges_eq_root_component N C hb t]
    exact activeComponentEdges_card_le_indegree N C hcut hl hu
  · exact activeRootRouteEdges_card_le_indegree_of_entry N C hcut he hb hl hu

/-- The derived two-position source conclusion, with no assumed support bound. -/
theorem current_port_support_card_le_two
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} {t : ℝ} (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ 2 :=
  (current_port_support_card_le_indegree N C hcut ht).trans
    (binary_indegree_le_two N port)

/-- Ordinary ports have only one possible current population. -/
theorem current_ordinary_port_support_card_le_one
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} (ho : ¬N.graph.IsHybrid port) {t : ℝ}
    (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ 1 :=
  (current_port_support_card_le_indegree N C hcut ht).trans
    (nonhybrid_indegree_le_one N ho)

/-- Rootedness and the real component calendar interval guarantee an actual
active original population, rather than a vacuous support upper bound. -/
theorem current_port_support_nonempty
    (N : RootedBinary V E X) (C : Calendar N.graph)
    {port : V} {t : ℝ} (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).Nonempty := by
  obtain ⟨es,hp⟩ := exists_edgePath_of_directed (N.rooted port)
  have hu : t < C.age N.root := by
    rcases ht.2 with ⟨_,hu⟩ | ⟨entry,_,_,hu⟩
    · exact hu
    · exact hu.trans_le (C.age_le_of_directed (N.rooted (N.graph.target entry)))
  obtain ⟨e,hem,ha⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C hp ht.1 hu
  exact ⟨e,(mem_activeRootRouteEdges_iff N.graph C N.root port t e).mpr ⟨es,hp,hem,ha⟩⟩

/-- At an ordinary port the actual current source population is unique. -/
theorem current_ordinary_port_support_card_eq_one
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} (ho : ¬N.graph.IsHybrid port) {t : ℝ}
    (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card = 1 := by
  have hl := Finset.card_pos.mpr (current_port_support_nonempty N C ht)
  have hu := current_ordinary_port_support_card_le_one N C hcut ho ht
  omega

#print axioms binary_indegree_le_two
#print axioms current_port_support_card_le_indegree
#print axioms current_port_support_card_le_two
#print axioms current_ordinary_port_support_card_le_one
#print axioms current_port_support_nonempty
#print axioms current_ordinary_port_support_card_eq_one
end GProgram.G5.ComponentSupport
