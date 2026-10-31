/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license; see LICENSE.
Authors: Álvaro Begué (retained sampled-square proof); dot (compact-obstacle
and Jordan-neighborhood adaptation), 2026-10-31.

Modified derivative, not unchanged upstream. Core proof adapted from
Schoenflies/ArcComplement.lean, exists_face_of_notMem_arc,
upstream 05a43d29cde026618777db3d4e4316204ccca237.
UNCOMPILED CANDIDATE. No source-order, pendant one-exit, or full NANUQ claim.
-/
import Schoenflies.JordanClosed
import ContinuousFaceCycles

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.CompactArcNeighborhood
open Metric Set Schoenflies unitInterval
open scoped Graph

/-- ONE Jordan curve encloses the arc and excludes the WHOLE compact obstacle
set. The sample overlay and its cut list are fixed before arbitrary x∈L.
The final clause controls the actual boundary, not only its parameterization. -/
theorem compact_obstacle_jordan {A L : Set Plane} (hA : IsArc A)
    (hL : IsCompact L) (hLne : L.Nonempty) (hdisj : Disjoint L A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set Plane, IsJordanCurve C ∧ A ⊆ inside C ∧ L ⊆ outside C ∧
      ∀ x ∈ C, ∃ y ∈ A, Plane.supDist x y < ε := by
  obtain ⟨α, hα, hinj, rfl⟩ := hA
  have hAc : IsCompact (α '' I) := isCompact_image_of_subset_I hα subset_rfl isCompact_I.isClosed
  -- ONE compact separation, fixed before any individual obstacle point.
  obtain ⟨ρ0,hρ0,hbound0⟩ := Plane.exists_dist_pos hL hAc hdisj
  let ρ := min ρ0 ε
  have hρ : 0 < ρ := lt_min hρ0 hε
  have hρε : ρ ≤ ε := min_le_right _ _
  have hbound : ∀ x ∈ L, ∀ y ∈ α '' I, ρ ≤ dist x y := by
    intro x hx y hy
    exact (min_le_left _ _).trans (hbound0 x hx y hy)
  set d : ℝ := ρ / 8 with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  have hfar4 : ∀ z ∈ L, ∀ y ∈ α '' I, 4 * d < Plane.supDist z y := by
    intro z hz y hy
    have hlt := lt_supDist_of_le_dist hρ (hbound z hz y hy)
    rw [hd_def]; linarith
  -- **Step 2.** The coarse partition, into `K = 3·m₁ ≥ 3` cells of diameter less than `d`.
  obtain ⟨m₁, hm₁, hmesh₁⟩ := exists_mesh hα hd 3 (by norm_num)
  obtain ⟨n, hK⟩ : ∃ n, 3 * m₁ = n + 1 := ⟨3 * m₁ - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  rw [hK] at hmesh₁
  -- **Step 3.** `δ = min(d, d')`, the second the separation of nonadjacent coarse subarcs.
  obtain ⟨ρ', hρ', hsep⟩ := exists_pos_dist_nonadjacent hα hinj (n := n + 1)
  set δ : ℝ := min d ρ' with hδ_def
  have hδ : 0 < δ := lt_min hd hρ'
  have hδd : δ ≤ d := min_le_left _ _
  have hδρ : δ ≤ ρ' := min_le_right _ _
  -- **Step 4.** The fine partition, refining the coarse one, of mesh less than `δ/4`.
  obtain ⟨m, hm, hmesh₂⟩ := exists_mesh hα (by linarith : (0 : ℝ) < δ / 4) (n + 1) (by omega)
  -- **Step 5.** The squares of radius `δ/4` about the fine samples, overlaid all at once.
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Plane, ∀ j, c j = α (sample ((n + 1) * m) j) := ⟨_, fun _ => rfl⟩
  set r : ℝ := δ / 4 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  -- Consecutive centres are closer than one radius.
  have hstep : ∀ q < (n + 1) * m, Plane.supDist (c q) (c (q + 1)) < r := by
    intro q hq
    have hmem : sample ((n + 1) * m) (q + 1) ∈
        Icc (sample ((n + 1) * m) q) (sample ((n + 1) * m) (q + 1)) :=
      ⟨sample_mono (Nat.le_succ q), le_rfl⟩
    have hlt := hmesh₂ q hq _ hmem
    rw [Plane.supDist_comm, hc, hc]
    exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) hlt
  -- A fine sample of the `p`-th block lies on the `p`-th coarse subarc.
  have hcell : ∀ p j, p * m ≤ j → j ≤ p * m + m → c j ∈ subarcCell α (n + 1) p := by
    intro p j h₁ h₂
    refine ⟨sample ((n + 1) * m) j, sample_mem_Icc_of_block hm h₁ ?_, (hc j).symm⟩
    calc j ≤ p * m + m := h₂
      _ = (p + 1) * m := by ring
  -- Centres of nonconsecutive links are more than two radii apart.
  have hfarblock : ∀ p q, p ≤ n → q ≤ n → p + 1 < q →
      ∀ j, p * m ≤ j → j ≤ p * m + m → ∀ j', q * m ≤ j' → j' ≤ q * m + m →
        2 * r < Plane.supDist (c j) (c j') := by
    intro p q hp hq hpq j hj hj' k hk hk'
    have hdist := hsep p (by omega) q (by omega) (by omega) _ (hcell p j hj hj')
      _ (hcell q k hk hk')
    have hlt := lt_supDist_of_le_dist hρ' hdist
    rw [hr_def]; linarith
  -- **Step 6.** The chain is a plane chain.
  have hchain := isPlaneChain_familyChain (c := c) (N := (n + 1) * m) (m := m) (r := r) (n := n)
    squaresTwoConnected hr hn (le_of_eq (by ring)) hstep hfarblock
  -- **Step 7.** Each consecutive pair sits in the square of radius `3d` about its first centre.
  have hcpm : ∀ p, c (p * m) = α (sample (n + 1) p) := fun p => by
    rw [hc, sample_mul (k := n + 1) hm]
  have hnear : ∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
      Plane.supDist (c j) (c (p * m)) < 2 * d := by
    intro p hp j h₁ h₂
    -- Membership of a fine sample in a coarse cell, as a distance bound from its base point.
    have base : ∀ q, q < n + 1 → ∀ k, q * m ≤ k → k ≤ q * m + m →
        Plane.supDist (c k) (α (sample (n + 1) q)) < d := by
      intro q hq k hk hk'
      have hmem : sample ((n + 1) * m) k ∈ Icc (sample (n + 1) q) (sample (n + 1) (q + 1)) :=
        sample_mem_Icc_of_block hm hk (by calc k ≤ q * m + m := hk'
          _ = (q + 1) * m := by ring)
      have hlt := hmesh₁ q hq _ hmem
      rw [hc]
      exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) hlt
    by_cases hcase : j ≤ p * m + m
    · have := base p (by omega) j h₁ hcase
      rw [hcpm]; linarith
    · -- `j` is in the next block: go through the shared sample `α(t_{p+1})`.
      have h₁' : (p + 1) * m ≤ j := by
        have : (p + 1) * m = p * m + m := by ring
        omega
      have h₂' : j ≤ (p + 1) * m + m := by
        have : (p + 1) * m = p * m + m := by ring
        omega
      have hA' := base (p + 1) (by omega) j h₁' h₂'
      -- The two consecutive coarse samples are themselves within `d`.
      have hB' : Plane.supDist (α (sample (n + 1) (p + 1))) (α (sample (n + 1) p)) < d := by
        have hmem : sample (n + 1) (p + 1) ∈
            Icc (sample (n + 1) p) (sample (n + 1) (p + 1)) :=
          ⟨sample_mono (Nat.le_succ p), le_rfl⟩
        exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) (hmesh₁ p (by omega) _ hmem)
      have htri := Plane.supDist_triangle (c j) (α (sample (n + 1) (p + 1))) (c (p * m))
      rw [hcpm] at htri ⊢
      linarith
  have hcontain : ∀ p, p + 1 ≤ n → ∀ j, p * m ≤ j → j ≤ p * m + m + m →
      Plane.supDist (c j) (c (p * m)) + r ≤ 3 * d := by
    intro p hp j h₁ h₂
    have := hnear p hp j h₁ h₂
    rw [hr_def]; linarith
  have hxfar : ∀ z ∈ L, ∀ p, p + 1 ≤ n →
      3 * d < Plane.supDist z (c (p * m)) := by
    intro z hz p hp
    have hmemA : c (p * m) ∈ α '' I :=
      ⟨sample (n + 1) p, sample_mem_I (by omega), (hcpm p).symm⟩
    have := hfar4 z hz _ hmemA
    linarith
  -- **Step 8.** `lem:outer-chain`.
  -- The single graph/face is chosen before a universally quantified x∈L.
  let G := Graph.chainUnion (familyChain c ((n+1)*m) m r) 0 n
  haveI : G.Finite := hchain.block_finite (i := 0) (m := n) (by omega)
  have hdraw : G.IsDrawing segmentDrawing := hchain.block_isDrawing (by omega)
  have htwo : G.IsTwoConnected := hchain.block_isTwoConnected (by omega)
  have hout : ∀ x ∈ L, x ∈ Graph.exterior G segmentDrawing ∧
      ¬ Bornology.IsBounded (Graph.face G segmentDrawing x) := by
    intro x hx
    exact outer_face_familyChain hchain (outerOnPairs_familyChain hcontain (hxfar x hx))
  obtain ⟨z,hzL⟩ := hLne
  have hzout := hout z hzL
  obtain ⟨e,u,v,D,hface⟩ :=
    Graph.face_cycles_continuous hdraw htwo z hzout.1
  let C := Graph.edgesCover segmentDrawing (e :: D)
  have hC : IsJordanCurve C := hdraw.cycle_isJordanCurve hface.isCycle
  have hFout : Graph.face G segmentDrawing z = outside C := by
    rcases hface.isRegionOf with hi | ho
    · exact False.elim (hzout.2 (hi.symm ▸ hface.isSeparating.isBounded_inside))
    · exact ho
  have hLout : L ⊆ outside C := by
    intro x hx
    have hox := hout x hx
    have hsame := Graph.unbounded_face_unique hdraw hox.2 hzout.2
    rw [← hFout]
    exact hsame ▸ Graph.mem_face hox.1
  -- Retain STRICT mesh coverage; the upstream public helper weakens this to ≤.
  have hcover : ∀ x ∈ α '' I, ∃ j, j < (n+1)*m ∧
      x ∈ Plane.openSquare (c j) r := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨j,hj,hjt⟩ := exists_mem_Icc_sample (by positivity : 0 < (n+1)*m) ht
    refine ⟨j,hj,?_⟩
    change Plane.supDist (α t) (c j) < r
    rw [hc]
    exact lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) (hmesh₂ j hj t hjt)
  have hfront : ∀ j, j ≤ (n+1)*m →
      frontier (Plane.closedSquare (c j) r) ⊆ Graph.pointSet G segmentDrawing := by
    intro j hj
    obtain ⟨i,hi,h₁,h₂⟩ := exists_block_index (j := j) (n := n) (m := m) hj
    have hle₁ : familySquare c ((n+1)*m) r j ≤ familyChain c ((n+1)*m) m r i :=
      Graph.le_chainUnion (G := familyOverlay c ((n+1)*m) r)
        (fun _ _ _ => familySquare_le) h₁ h₂
    have hle₂ : familyChain c ((n+1)*m) m r i ≤ G :=
      Graph.le_chainUnion (G := familyOverlay c ((n+1)*m) r)
        (fun _ _ _ => familyChain_le) (Nat.zero_le _) (by omega)
    rw [← pointSet_familySquare (c := c) hr hj]
    exact Graph.pointSet_mono (hle₁.trans hle₂)
  have hAin : α '' I ⊆ inside C := by
    intro x hx
    obtain ⟨j,hj,hxO⟩ := hcover x hx
    have hOF : Plane.openSquare (c j) r ⊆ (Graph.face G segmentDrawing z)ᶜ :=
      fun _ hy => notMem_face_of_mem_openSquare (hfront j hj.le) hzout.2 hy
    have hFO : Graph.face G segmentDrawing z ⊆ (Plane.openSquare (c j) r)ᶜ :=
      fun y hy hyO => hOF hyO hy
    have hcl := closure_minimal hFO (Plane.isOpen_openSquare (c j) r).isClosed_compl
    have hxnotcl : x ∉ closure (Graph.face G segmentDrawing z) := fun hxcl => hcl hxcl hxO
    have hxnotC : x ∉ C := by
      intro hxC
      have hfr : x ∈ frontier (Graph.face G segmentDrawing z) := hface.frontier_eq.symm ▸ hxC
      exact hxnotcl (frontier_subset_closure hfr)
    have hxnotout : x ∉ outside C := by
      rw [← hFout]
      exact hOF hxO
    have hsplit : x ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hxnotC
    exact hsplit.resolve_right hxnotout
  refine ⟨C,hC,hAin,hLout,?_⟩
  intro x hxC
  have hxG : x ∈ Graph.pointSet G segmentDrawing :=
    Graph.edgesCover_subset_pointSet (fun g hg => hface.isCycle.mem_edgeSet_cons hg) hxC
  obtain ⟨i,hi0,hin,hxi⟩ := Graph.IsPlaneChain.mem_pointSet_block hxG
  obtain ⟨j,hj0,hj1,hxj⟩ := exists_mem_frontier_of_mem_pointSet_familyChain hxi
  have hjN : j ≤ (n+1)*m := by
    calc j ≤ i*m+m := hj1
      _ ≤ n*m+m := by simpa only [Nat.zero_add] using Nat.add_le_add_right (Nat.mul_le_mul_right m hin) m
      _ = (n+1)*m := by ring
  refine ⟨c j,⟨sample ((n+1)*m) j,sample_mem_I hjN,(hc j).symm⟩,?_⟩
  have hdist : Plane.supDist x (c j) = r := by
    rw [Plane.frontier_closedSquare,mem_setOf_eq] at hxj
    exact hxj
  rw [hdist]
  have hrd : r ≤ d/4 := by rw [hr_def]; exact div_le_div_of_nonneg_right hδd (by norm_num)
  rw [hd_def] at hrd
  linarith

#print axioms compact_obstacle_jordan
end Nanuq.CompactArcNeighborhood
