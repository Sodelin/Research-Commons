/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué.

Modified derivative proof, not an unchanged upstream file.
Derived from Álvaro Begué's Schoenflies.FaceCyclesProof (Apache-2.0),
upstream pin 05a43d29cde026618777db3d4e4316204ccca237,
source SHA256 46902b10c30553fd56099fcc5e1f491391f2d9596631ddd4f2f4284ba5721a70.
Original proof authorship retained. Continuous-source adaptation: dot, 2026-10-31.
UNCOMPILED CANDIDATE. No fixed taxon order or full NANUQ claim.
-/
import Schoenflies.FaceCyclesProof
import Schoenflies.JordanClosed
import ContinuousRegionCrosscut

namespace Nanuq.ContinuousFaceCycles
open Schoenflies

theorem component_region {C P A₁ A₂ Ω : Set Plane} {p q z : Plane}
    (hC : IsJordanCurve C) (hcut : IsCutPair C p q A₁ A₂)
    (hP : IsArcBetween P p q) (hPC : P ∩ C = {p,q})
    (hΩ : IsRegionOf C Ω) (hPD : P \ {p,q} ⊆ Ω) (hz : z ∈ Ω \ P) :
    IsRegionOf (A₁ ∪ P) (connectedComponentIn (Ω \ P) z) ∨
      IsRegionOf (A₂ ∪ P) (connectedComponentIn (Ω \ P) z) := by
  obtain ⟨V₁,V₂,h₁,h₂,heq,_,_,_,_,hc₁,hc₂,_,_⟩ :=
    Nanuq.ContinuousRegionCrosscut.continuous_crosscut_region hC hcut hP hPC hΩ hPD
  rw [heq] at hz
  rcases hz with hz | hz
  · exact Or.inl ((hc₁ z hz).symm ▸ h₁)
  · exact Or.inr ((hc₂ z hz).symm ▸ h₂)
end Nanuq.ContinuousFaceCycles

namespace Graph
open Schoenflies
open scoped Graph
variable {β : Type*} {G B : Graph Plane β} {drawing : β → ℝ → Plane}
variable {a b : Plane}

theorem IsDrawing.hasFaceCycles_cycleGraph_continuous (h : IsDrawing G drawing)
    {e : β} {u v : Plane} {D : List β}
    (hc : G.IsCycleThrough e u v D) : HasFaceCycles (G.cycleGraph u e D) drawing := by
  have hsep : IsSeparating (edgesCover drawing (e :: D)) := jordan_curve_theorem (h.cycle_isJordanCurve hc)
  -- The same cycle, read inside the subgraph it spans.
  have hcyc : (G.cycleGraph u e D).IsCycleThrough e u v D :=
    ⟨hc.cycleGraph_isLink,
      hc.isPath.anti hc.cycleGraph_le hc.left_mem_cycleGraph fun g hg => by
        rw [hc.cycleGraph_edgeSet]; exact List.mem_append_left _ hg,
      hc.notMem⟩
  intro z hz
  refine ⟨e, u, v, D, hcyc, hsep, ?_⟩
  rw [face, exterior, h.pointSet_cycleGraph hc]
  refine hsep.isRegionOf_connectedComponentIn ?_
  rw [exterior, h.pointSet_cycleGraph hc] at hz
  exact hz

theorem IsDrawing.hasFaceCycles_union_continuous [G.Finite] (h : IsDrawing G drawing)
    (hBG : B ≤ G) (hmot : HasFaceCycles B drawing) {D' : List β}
    (hpath : G.IsPath a D' b) (hab : a ≠ b) (ha : a ∈ V(B)) (hb : b ∈ V(B))
    (hint : ∀ y ∈ G.walkVertices a D', y ≠ a → y ≠ b → y ∉ V(B))
    (hnew : ∀ g ∈ D', g ∉ E(B)) :
    HasFaceCycles (B.union (G.pathGraphOf a D')) drawing := by
  haveI : B.Finite := Finite.of_le hBG
  have hB : IsDrawing B drawing := h.mono hBG
  have hne : D' ≠ [] := hpath.ne_nil hab
  have hPG : G.pathGraphOf a D' ≤ G := pathGraphOf_le hpath.isWalk
  have hB'G : B.union (G.pathGraphOf a D') ≤ G := union_le hBG hPG
  have hBB' : B ≤ B.union (G.pathGraphOf a D') := left_le_union _ _
  have hB' : IsDrawing (B.union (G.pathGraphOf a D')) drawing := h.mono hB'G
  have hQarc : IsArcBetween (edgesCover drawing D') a b := h.path_isArcBetween hpath hne
  have hext : exterior (B.union (G.pathGraphOf a D')) drawing =
      exterior B drawing \ edgesCover drawing D' := by
    rw [exterior_union, h.pointSet_pathGraphOf hpath.isWalk hne]
  -- The ear lies in one face of the old subgraph.
  obtain ⟨z₀, hz₀, hsub₀⟩ := h.exists_face_of_ear hBG hpath hab hint hnew
  have hQinter : ∀ w ∈ edgesCover drawing D', w ∈ exterior B drawing →
      w ∈ face B drawing z₀ := by
    intro w hw hwe
    refine hsub₀ ⟨hw, fun hcon => hwe ?_⟩
    rcases hcon with rfl | rfl
    exacts [vertexSet_subset_pointSet ha, vertexSet_subset_pointSet hb]
  intro z hz
  rw [hext] at hz
  obtain ⟨hzB, hzQ⟩ := hz
  obtain ⟨e, u, v, D, hface⟩ := hmot z hzB
  by_cases hsame : face B drawing z = face B drawing z₀
  · -- The face the ear cuts.
    have hopenF : IsOpen (face B drawing z₀) := hB.isOpen_face z₀
    obtain ⟨haF, hbF⟩ := h.ends_mem_frontier_face hopenF hpath hab ha hb hsub₀
    have hfr : frontier (face B drawing z₀) = edgesCover drawing (e :: D) := by
      rw [← hsame]; exact hface.frontier_eq
    have haW : a ∈ B.walkVertices u D :=
      hB.mem_walkVertices_of_mem_edgesCover hface.isCycle ha (hfr ▸ haF)
    have hbW : b ∈ B.walkVertices u D :=
      hB.mem_walkVertices_of_mem_edgesCover hface.isCycle hb (hfr ▸ hbF)
    obtain ⟨D₁, D₂, hD1, hD2, hperm, hmeet⟩ := hface.isCycle.split_at haW hbW hab
    -- The two arcs use disjoint edge lists, because the cycle's own list repeats nothing.
    have hnodup : (e :: D).Nodup := List.nodup_cons.2 ⟨hface.isCycle.notMem,
      hface.isCycle.isPath.nodup⟩
    have hdisj : ∀ g ∈ D₁, g ∉ D₂ := fun g hg hg₂ =>
      (List.nodup_append.1 (hperm.nodup_iff.2 hnodup)).2.2 g hg g hg₂ rfl
    obtain ⟨harc₁, harc₂, hinter⟩ := hB.arcs_of_split hD1 hD2 hab hdisj hmeet
    have hunion : edgesCover drawing D₁ ∪ edgesCover drawing D₂ = edgesCover drawing (e :: D) := by
      rw [← edgesCover_append, edgesCover_perm hperm]
    -- The ear meets the cycle exactly in its own two ends.
    have hJsub : edgesCover drawing (e :: D) ⊆ pointSet B drawing :=
      edgesCover_subset_pointSet fun g hg => by
        rcases List.mem_cons.1 hg with rfl | hg'
        exacts [hface.isCycle.isLink.edge_mem, hface.isCycle.isPath.edge_mem hg']
    have hmeetJ : edgesCover drawing D' ∩ edgesCover drawing (e :: D) = {a, b} := by
      refine Set.Subset.antisymm (fun w hw =>
        h.edgesCover_inter_pointSet hBG hpath hint hnew ⟨hw.1, hJsub hw.2⟩) ?_
      rintro w (rfl | rfl)
      exacts [⟨hQarc.left_mem, hfr ▸ haF⟩, ⟨hQarc.right_mem, hfr ▸ hbF⟩]
    -- The crosscut hypothesis.
    have hzF : z ∈ face B drawing z \ edgesCover drawing D' := ⟨mem_face hzB, hzQ⟩
    have hfaceEq : face (B.union (G.pathGraphOf a D')) drawing z =
        connectedComponentIn (face B drawing z \ edgesCover drawing D') z := by
      have hstep : face (B.union (G.pathGraphOf a D')) drawing z =
          connectedComponentIn (exterior B drawing \ edgesCover drawing D') z := by
        rw [face, hext]
      rw [hstep, connectedComponentIn_diff]
      rfl
    have hcross := Nanuq.ContinuousFaceCycles.component_region
      (hB.cycle_isJordanCurve hface.isCycle)
      (show IsCutPair (edgesCover drawing (e :: D)) a b
        (edgesCover drawing D₁) (edgesCover drawing D₂) from
        ⟨harc₁,harc₂.reverse,hunion,hinter⟩)
      hQarc hmeetJ hface.isRegionOf (by rw [hsame]; exact hsub₀) hzF
    -- Either way, the new face is a region of the arc closed up by the ear.
    rcases hcross with hreg | hreg
    · obtain ⟨f, x, y, T, hcyc, hpermT⟩ := exists_spliced_cycle hBG hD1 hpath hab hnew hint
      have hcov : edgesCover drawing (f :: T) =
          edgesCover drawing D₁ ∪ edgesCover drawing D' := by
        rw [edgesCover_perm hpermT, edgesCover_append]
      exact ⟨f, x, y, T, hcyc, jordan_curve_theorem (hB'.cycle_isJordanCurve hcyc),
        by rw [hcov, hfaceEq]; exact hreg⟩
    · obtain ⟨f, x, y, T, hcyc, hpermT⟩ :=
        exists_spliced_cycle hBG hD2.reverse hpath hab hnew hint
      have hcov : edgesCover drawing (f :: T) =
          edgesCover drawing D₂ ∪ edgesCover drawing D' := by
        rw [edgesCover_perm hpermT, edgesCover_append, edgesCover_reverse]
      exact ⟨f, x, y, T, hcyc, jordan_curve_theorem (hB'.cycle_isJordanCurve hcyc),
        by rw [hcov, hfaceEq]; exact hreg⟩
  · -- The ear misses this face, which therefore survives unchanged.
    have hdis : Disjoint (face B drawing z) (pointSet (G.pathGraphOf a D') drawing) := by
      rw [h.pointSet_pathGraphOf hpath.isWalk hne, Set.disjoint_left]
      intro w hw hwQ
      refine absurd ?_ hsame
      refine (face_eq_or_disjoint (G := B) (drawing := drawing) z z₀).resolve_right fun hd => ?_
      exact Set.disjoint_left.1 hd hw (hQinter w hwQ (face_subset_exterior _ _ _ hw))
    exact ⟨e, u, v, D, hface.mono hBB' (face_union_eq_of_disjoint hzB hdis)⟩

theorem face_cycles_continuous [G.Finite] (h : IsDrawing G drawing)
    (hG : G.IsTwoConnected) :
    HasFaceCycles G drawing := by
  have hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x := fun g x => h.not_isLoopAt g x
  obtain ⟨e, u, v, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  refine hG.ear_decomposition (motive := fun B => HasFaceCycles B drawing) hnl
    hcyc.isTwoConnected hcyc.isCycle.cycleGraph_le
    (h.hasFaceCycles_cycleGraph_continuous hcyc.isCycle) ?_
  intro B a b D' _ _ hBG hmot hpathD hab haB hbB hintB
  -- Either the ear is genuinely new, or it is an edge the subgraph already had and adding it
  -- changes nothing.
  rcases ear_edges_notMem_or_union_eq hBG hpathD hab haB hbB hintB with hnew | heq
  · exact h.hasFaceCycles_union_continuous hBG hmot hpathD hab haB hbB hintB hnew
  · rw [heq]; exact hmot

end Graph
#print axioms Nanuq.ContinuousFaceCycles.component_region
#print axioms Graph.IsDrawing.hasFaceCycles_cycleGraph_continuous
#print axioms Graph.face_cycles_continuous
