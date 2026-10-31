import G1ActualDisplayedClusterSplitTransport
import GraphSourceCut

/-! Source draft only: exact actual switching edge sides and the inherited ALL
split target. No calendar, drawing, order, galledness or CutChild premise. -/
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.GraphSyntax
open GProgram.G5.Normalization
open G1ActualSelectedClusterTransport G1ActualDisplayedClusterSplitTransport
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- The same original retained edge ID, not an edge of reshaped syntax. -/
theorem actual_target_cluster (N : RootedBinary V E X) (S : N.Switching)
    (panel : Finset X) (e : S.Edge) :
    sampledDescendants N S panel (S.graph.target e) =
      panel.filter (fun x => S.graph.ReachWithout e (S.graph.target e) (N.leaf x)) := by
  ext x
  simp only [sampledDescendants, Finset.mem_filter]
  exact and_congr_right (fun _ =>
    (target_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming e (N.leaf x)).symm)

/-- The complementary side is the original source-side component, including
pendant cuts and arbitrary selected panels. -/
theorem actual_source_cluster (N : RootedBinary V E X) (S : N.Switching)
    (panel : Finset X) (e : S.Edge) :
    panel \ sampledDescendants N S panel (S.graph.target e) =
      panel.filter (fun x => S.graph.ReachWithout e (S.graph.source e) (N.leaf x)) := by
  ext x
  simp only [Finset.mem_sdiff, sampledDescendants, Finset.mem_filter]
  have hc := source_cut_iff S.graph S.selected_acyclic S.selected_uniqueIncoming
    N.root S.selected_rooted e (N.leaf x)
  tauto

/-- Every proper nonempty source-selected cluster comes from a retained
original edge; root/full and empty twigs are excluded by the actual target. -/
theorem proper_selected_cluster_edge (N : RootedBinary V E X) (S : N.Switching)
    (panel D : Finset X) (hD : D ∈ selectedClusters N S panel)
    (hproper : (panel \ D).Nonempty) :
    ∃ e : S.Edge, sampledDescendants N S panel (S.graph.target e) = D := by
  obtain ⟨_, v, hv⟩ := (mem_selectedClusters N S panel D).mp hD
  have hn : v ≠ N.root := by
    intro he
    have hr : sampledDescendants N S panel v = panel := by
      subst v
      ext x
      simp only [sampledDescendants, Finset.mem_filter]
      exact ⟨And.left, fun hx => ⟨hx, S.selected_rooted (N.leaf x)⟩⟩
    have hd : D = panel := hv.symm.trans hr
    simpa [hd] using hproper
  obtain ⟨e, he⟩ := S.selected_parent hn
  exact ⟨e, he.symm ▸ hv⟩

/-- Existing ALL displayed split target equals actual retained-edge cuts,
with both panel sides nonempty. No new 'displayed' predicate is introduced. -/
theorem actual_displayed_split_edge_iff (N : RootedBinary V E X)
    (panel : Finset X) (cut : Finset (Finset X)) :
    cut ∈ actualDisplayedSplits N panel ↔
      ∃ S : N.Switching, ∃ e : S.Edge,
        let D := sampledDescendants N S panel (S.graph.target e)
        D.Nonempty ∧ (panel \ D).Nonempty ∧ cut = {D, panel \ D} := by
  constructor
  · intro h
    obtain ⟨D, hD, hcut⟩ := Finset.mem_image.mp h
    obtain ⟨hD, _, hn, hp⟩ := Finset.mem_filter.mp hD
    obtain ⟨S, hs⟩ := (mem_actualDisplayedClusters N panel D).mp hD
    obtain ⟨e, he⟩ := proper_selected_cluster_edge N S panel D hs hp
    refine ⟨S, e, ?_⟩
    dsimp
    rw [he]
    exact ⟨hn, hp, hcut.symm⟩
  · rintro ⟨S, e, hn, hp, hcut⟩
    let D := sampledDescendants N S panel (S.graph.target e)
    have hs : D ∈ selectedClusters N S panel :=
      (mem_selectedClusters N S panel D).mpr ⟨hn, S.graph.target e, rfl⟩
    have hd : D ⊆ panel := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    exact Finset.mem_image.mpr ⟨D, Finset.mem_filter.mpr
      ⟨(mem_actualDisplayedClusters N panel D).mpr ⟨S, hs⟩, hd, hn, hp⟩, hcut.symm⟩

/-- Literal edge-side identification with the EXISTING unordered split
encoding; complementary orientation is allowed without reversing any edge. -/
theorem actual_split_of_edge_side (N : RootedBinary V E X)
    (S : N.Switching) (e : S.Edge) (B : Finset X)
    (hB : B.Nonempty) (hBc : (Finset.univ \ B).Nonempty)
    (hor :
      (∀ x, S.graph.DReach (S.graph.target e) (N.leaf x) ↔ x∈B) ∨
      (∀ x, ¬S.graph.DReach (S.graph.target e) (N.leaf x) ↔ x∈B)) :
    ({B,Finset.univ \ B} : Finset (Finset X)) ∈ actualDisplayedSplits N Finset.univ := by
  apply (actual_displayed_split_edge_iff N Finset.univ _).mpr
  refine ⟨S,e,?_⟩
  dsimp
  rcases hor with hor | hor
  · have hd : sampledDescendants N S Finset.univ (S.graph.target e)=B := by
      ext x
      simp [sampledDescendants,hor x]
    rw [hd]
    exact ⟨hB,hBc,rfl⟩
  · have hd : sampledDescendants N S Finset.univ (S.graph.target e)=Finset.univ \ B := by
      ext x
      simp only [sampledDescendants,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.mem_sdiff,true_and]
      have hx := hor x
      tauto
    have hcc : Finset.univ \ (Finset.univ \ B)=B := by ext x; simp
    rw [hd,hcc]
    exact ⟨hBc,hB,by ext D; simp [or_comm]⟩

/-- Pendant support is inherited from the exact selected leaf cluster,
not from a four-distinct-label query (which may not exist on small panels). -/
theorem actual_pendant_split_mem (N : RootedBinary V E X) (panel : Finset X)
    (x : X) (hx : x∈panel) (hother : (panel \ {x}).Nonempty) :
    ({({x} : Finset X),panel \ {x}} : Finset (Finset X)) ∈ actualDisplayedSplits N panel := by
  let S : N.Switching := Classical.choice inferInstance
  have hd : sampledDescendants N S panel (N.leaf x)={x} := by
    simpa [hx] using sampledDescendants_taxon N S panel x
  have hc : ({x} : Finset X) ∈ selectedClusters N S panel :=
    (mem_selectedClusters N S panel {x}).mpr
      ⟨Finset.singleton_nonempty x,N.leaf x,hd⟩
  apply Finset.mem_image.mpr
  refine ⟨{x},Finset.mem_filter.mpr ⟨?_,?_,Finset.singleton_nonempty x,hother⟩,rfl⟩
  · exact (mem_actualDisplayedClusters N panel {x}).mpr ⟨S,hc⟩
  · exact Finset.singleton_subset_iff.mpr hx

end Nanuq.ActualCutClusters
