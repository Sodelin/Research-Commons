import G1SwitchingDescendantTransport
import G5OriginalPruningClusterPreservation

/-! ALL original selected taxon clusters survive the actual physical splice.
The removed original U/H nodes both have the actual descendant-interface
cluster; no target-preservation equation is assumed. -/
namespace G1ActualSelectedClusterTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1SpliceDegrees G1SplicedSourceAdmission G1SplicedOriginalSwitching
open G1SwitchingDescendantTransport G1CutChildPorts
open GProgram.G5.Normalization
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

theorem actual_selected_hybrid_descendants (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (S : N.Switching) (x : X) :
    S.graph.DReach A.fragment.parents.hybrid (N.leaf x) ↔
      S.graph.DReach (N.graph.target A.child) (N.leaf x) := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with he | ⟨v,step,tail⟩
    · exact False.elim (N.no_edge_source_leaf x A.child (A.child_source.trans he))
    · obtain ⟨e,hs,ht⟩ := step
      have he := actual_child_unique N b A e.val hs
      have hw : N.graph.target A.child = v := he ▸ ht
      exact hw.symm ▸ tail
  · intro h
    exact (Relation.ReflTransGen.single ⟨⟨A.child,child_kept N b A S⟩,A.child_source,rfl⟩).trans h

theorem actual_selected_upper_descendants (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (S : N.Switching) (x : X) :
    S.graph.DReach A.fragment.upper (N.leaf x) ↔
      S.graph.DReach (N.graph.target A.child) (N.leaf x) := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with he | ⟨v,step,tail⟩
    · exact False.elim (N.no_edge_source_leaf x A.fragment.parents.parent0
        ((A.fragment.arm_sources false).trans he))
    · obtain ⟨e,hs,ht⟩ := step
      have hw : v = A.fragment.parents.hybrid := by
        rcases actual_upper_children_exhaustive N hc b A e.val hs with he | he
        · have ht' : N.graph.target e.val = v := ht
          rw [he,A.fragment.parents.target0] at ht'
          exact ht'.symm
        · have ht' : N.graph.target e.val = v := ht
          rw [he,A.fragment.parents.target1] at ht'
          exact ht'.symm
      exact (actual_selected_hybrid_descendants N b A S x).mp (hw ▸ tail)
  · intro h
    obtain ⟨p,ht,hp,_⟩ := S.hybrid_unique A.fragment.parents.hybrid A.fragment.parents.isHybrid
    have hs : N.graph.source p = A.fragment.upper := by
      rcases actual_hybrid_parents_exhaustive N b A p ht with he | he
      · rw [he]; exact A.fragment.arm_sources false
      · rw [he]; exact A.fragment.arm_sources true
    exact (Relation.ReflTransGen.single ⟨⟨p,hp⟩,hs,ht⟩).trans
      ((actual_selected_hybrid_descendants N b A S x).mpr h)

theorem actual_retained_selected_cluster (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) (panel : Finset X) (v : SplicedVertex N b A) :
    sampledDescendants (splicedNetwork N hc b hb A) (restrictSwitching N hc b hb A S) panel v =
      sampledDescendants N S panel v.val := by
  ext x
  simp only [sampledDescendants,Finset.mem_filter]
  exact and_congr_right (fun _ => actual_retained_selected_descendants_iff N hc b hb A S v (retainedTaxa N b A x))

noncomputable def selectedClusters (N : RootedBinary V E X) (S : N.Switching) (panel : Finset X) :
    Finset (Finset X) :=
  (Finset.univ.image (sampledDescendants N S panel)).filter Finset.Nonempty

lemma mem_selectedClusters (N : RootedBinary V E X) (S : N.Switching) (panel D : Finset X) :
    D ∈ selectedClusters N S panel ↔ D.Nonempty ∧ ∃ v, sampledDescendants N S panel v = D := by
  simp [selectedClusters,and_comm]

/-- Every selected cluster of the old actual switching equals a cluster of
the actual reduced switching, and conversely, for ANY selected taxon panel. -/
theorem actual_selected_clusters_splice (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) (panel : Finset X) :
    selectedClusters (splicedNetwork N hc b hb A) (restrictSwitching N hc b hb A S) panel =
      selectedClusters N S panel := by
  ext D
  rw [mem_selectedClusters,mem_selectedClusters]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨v.val,(actual_retained_selected_cluster N hc b hb A S panel v).symm.trans hv⟩
  · rintro ⟨v,hv⟩
    by_cases hU : v = A.fragment.upper
    · refine ⟨descendantInterface N b A,?_⟩
      rw [actual_retained_selected_cluster]
      calc
        sampledDescendants N S panel (N.graph.target A.child) = sampledDescendants N S panel A.fragment.upper := by
          ext x
          simp only [sampledDescendants,Finset.mem_filter]
          exact and_congr_right (fun _ => (actual_selected_upper_descendants N hc b A S x).symm)
        _ = D := hU ▸ hv
    · by_cases hH : v = A.fragment.parents.hybrid
      · refine ⟨descendantInterface N b A,?_⟩
        rw [actual_retained_selected_cluster]
        calc
          sampledDescendants N S panel (N.graph.target A.child) = sampledDescendants N S panel A.fragment.parents.hybrid := by
            ext x
            simp only [sampledDescendants,Finset.mem_filter]
            exact and_congr_right (fun _ => (actual_selected_hybrid_descendants N b A S x).symm)
          _ = D := hH ▸ hv
      · let w : SplicedVertex N b A := ⟨v,hU,hH⟩
        exact ⟨w,(actual_retained_selected_cluster N hc b hb A S panel w).trans hv⟩

#print axioms actual_selected_clusters_splice
end G1ActualSelectedClusterTransport
