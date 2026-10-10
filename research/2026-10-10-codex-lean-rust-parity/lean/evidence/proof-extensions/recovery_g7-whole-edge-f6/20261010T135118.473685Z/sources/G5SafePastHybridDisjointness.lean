import G5ProtectiveBlock
import G5ParentPositionPushforward

/-!
# Positive original child intervals enforce entire safe-past site separation

Contributor: dot, 2026-10-02. This is a deterministic chronological source
lemma on original edge occurrences and original-tip route families. Absence
of a sure exact nonsingleton block in a stage, together with the stage's
initial invariant, excludes every shared original hybrid up to the stage's
older endpoint. Entire original hybrid-past site sets are therefore disjoint.
It does not construct the observed stochastic support or prove that a deletion
algorithm establishes its initial invariant.
-/
namespace GProgram.G5.SafePast
open Nanuq.Source
open GProgram.G5
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Sure exact block over ALL original root-to-tip route families. -/
def SureExactBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) : Prop :=
  ∀ R : RouteFamily N, ∃ e : E, selectedPopulationBlock N R B C t e = D

/-- No such nonsingleton exact block has occurred at any stage age. -/
def NoSureNontrivialBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s t : ℝ) : Prop :=
  ∀ u : ℝ, s ≤ u → u < t → ∀ D : Finset X, D ⊆ B → 2 ≤ D.card →
    ¬SureExactBlock N C B D u

/-- Initial safe-past invariant, stated only at the stage's younger endpoint. -/
def SafeAt (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s : ℝ) : Prop :=
  ∀ h : V, N.graph.IsHybrid h → C.age h ≤ s →
    (selectedDescendants N B h).card ≤ 1

theorem selectedDescendants_subset (N : RootedBinary V E X)
    (B : Finset X) (h : V) : selectedDescendants N B h ⊆ B := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem protective_sure_exact_block (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X)
    {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e) {u : ℝ}
    (hu : C.age (N.graph.target e) ≤ u ∧ u < C.age h) :
    SureExactBlock N C B (selectedDescendants N B h) u := by
  intro R
  exact ⟨e, protective_population_block_eq N R B C hh hs he hu⟩

/-- A shared hybrid strictly after the stage start creates a sure block at
an earlier actual positive child-edge age, even if that edge straddles s. -/
theorem shared_hybrid_produces_earlier_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} {h : V} (hh : N.graph.IsHybrid h)
    (hs : s < C.age h) (ht : C.age h ≤ t)
    (hcard : 2 ≤ (selectedDescendants N B h).card) :
    ∃ u : ℝ, s ≤ u ∧ u < t ∧
      SureExactBlock N C B (selectedDescendants N B h) u := by
  obtain ⟨e,he,_⟩ := unique_child_edge N hh.2
  have hbridge := hcut e (by simpa only [he] using hh)
  have hage : C.age (N.graph.target e) < C.age h := by
    simpa only [he] using C.edge_older e
  refine ⟨max s (C.age (N.graph.target e)),le_max_left _ _,?_,?_⟩
  · exact (max_lt hs hage).trans_le ht
  · exact protective_sure_exact_block N C B hh he hbridge
      ⟨le_max_right _ _,max_lt hs hage⟩

/-- The safe invariant advances over the ENTIRE original past, including the
older endpoint. Nothing is asserted only about a current component or a
survival-conditioned pair. -/
theorem safeAt_of_no_earlier_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} (hstart : SafeAt N C B s)
    (hquiet : NoSureNontrivialBlock N C B s t) : SafeAt N C B t := by
  intro h hh ht
  by_cases hs : C.age h ≤ s
  · exact hstart h hh hs
  · by_contra hc
    have hcard : 2 ≤ (selectedDescendants N B h).card := by omega
    obtain ⟨u,hus,hut,hublock⟩ := shared_hybrid_produces_earlier_sure_block
      N C hcut B hh (lt_of_not_ge hs) ht hcard
    exact hquiet u hus hut (selectedDescendants N B h)
      (selectedDescendants_subset N B h) hcard hublock

/-- Full original hybrid site past: all original hybrids at ages <= t from
which this original tip descends, irrespective of its current route. -/
noncomputable def originalHybridPast (N : RootedBinary V E X)
    (C : Calendar N.graph) (x : X) (t : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun h => N.graph.IsHybrid h ∧ C.age h ≤ t ∧
    N.graph.DReach h (N.leaf x))

theorem mem_originalHybridPast_iff (N : RootedBinary V E X)
    (C : Calendar N.graph) (x : X) (t : ℝ) (h : V) :
    h ∈ originalHybridPast N C x t ↔
      N.graph.IsHybrid h ∧ C.age h ≤ t ∧ N.graph.DReach h (N.leaf x) := by
  classical
  simp only [originalHybridPast,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Any distinct retained original tips have disjoint ENTIRE past original
hybrid sites whenever the actual source safe invariant holds. -/
theorem originalHybridPast_disjoint (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) {t : ℝ} (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) :
    Disjoint (originalHybridPast N C x t) (originalHybridPast N C y t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro h hhx hhy
  have hp := (mem_originalHybridPast_iff N C x t h).mp hhx
  have hq := (mem_originalHybridPast_iff N C y t h).mp hhy
  have hcard := hsafe h hp.1 hp.2.1
  have hmemx : x ∈ selectedDescendants N B h := Finset.mem_filter.mpr ⟨hx,hp.2.2⟩
  have hmemy : y ∈ selectedDescendants N B h := Finset.mem_filter.mpr ⟨hy,hq.2.2⟩
  exact hne (Finset.card_le_one.mp hcard x hmemx y hmemy)

/-- Chronological no-sure-block progress gives the full original-site
separation needed before independent source product-law readouts. -/
theorem originalHybridPast_disjoint_of_no_earlier_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} (hstart : SafeAt N C B s)
    (hquiet : NoSureNontrivialBlock N C B s t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) :
    Disjoint (originalHybridPast N C x t) (originalHybridPast N C y t) :=
  originalHybridPast_disjoint N C B
    (safeAt_of_no_earlier_sure_block N C hcut B hstart hquiet) hx hy hne

#print axioms protective_sure_exact_block
#print axioms shared_hybrid_produces_earlier_sure_block
#print axioms safeAt_of_no_earlier_sure_block
#print axioms originalHybridPast_disjoint
#print axioms originalHybridPast_disjoint_of_no_earlier_sure_block
end GProgram.G5.SafePast
