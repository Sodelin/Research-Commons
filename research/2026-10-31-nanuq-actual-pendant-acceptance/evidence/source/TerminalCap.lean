import SampledNeighborhood

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Pendant
open Set Metric Schoenflies unitInterval

/-- A source-derived terminal condition used only at this intermediate layer:
each prefix point is on the preceding horizontal carrier or uniformly away
from the actual continuation corridor. The original-edge join must derive it. -/
def TerminalPrefix (A : Set Plane) (b δ : ℝ) : Prop :=
  ∀ a ∈ A, (a 1 = 0 ∧ a 0 ≤ 0) ∨
    (∀ x ∈ Icc 0 b, δ ≤ Plane.supDist a (Plane.mk x 0))

def rightStrip (r b : ℝ) : Set Plane :=
  {x | r < x 0 ∧ x 0 ≤ b ∧ -r < x 1 ∧ x 1 < r}

theorem rightStrip_preconnected (r b : ℝ) : IsPreconnected (rightStrip r b) := by
  have he : rightStrip r b =
      ({x : Plane | r < x 0} ∩ {x : Plane | x 0 ≤ b}) ∩
      ({x : Plane | -r < x 1} ∩ {x : Plane | x 1 < r}) := by
    ext x; simp [rightStrip]; tauto
  rw [he]
  exact (((Plane.convex_coord_gt 0 r).inter (Plane.convex_coord_le 0 b)).inter
    ((Plane.convex_coord_gt 1 (-r)).inter (Plane.convex_coord_lt 1 r))).isPreconnected

theorem strip_misses_square {A : Set Plane} {b δ r : ℝ}
    (hterm : TerminalPrefix A b δ) (hr : 0 < r) (hsmall : 2*r < δ)
    {a x : Plane} (ha : a ∈ A) (hx : x ∈ rightStrip r b) :
    x ∉ Plane.closedSquare a r := by
  intro hsq
  change Plane.supDist x a ≤ r at hsq
  rcases hterm a ha with hline | hfar
  · have hc : |x 0-a 0| ≤ r := (Plane.abs_zero_le_supNorm (x-a)).trans hsq
    have hh := (le_abs_self (x 0-a 0)).trans hc
    have hxr := hx.1
    linarith [hline.2]
  · have hδ := hfar (x 0) ⟨by linarith [hx.1],hx.2.1⟩
    have hcoord : Plane.supDist x (Plane.mk (x 0) 0) = |x 1| := by
      simp [Plane.supDist,Plane.supNorm]
    have htri := Plane.supDist_triangle a x (Plane.mk (x 0) 0)
    rw [Plane.supDist_comm a x,hcoord] at htri
    have hy : |x 1| < r := abs_lt.mpr ⟨hx.2.2.1,hx.2.2.2⟩
    linarith

/-- The whole vertical terminal cap belongs to the same actual Jordan curve;
this is stronger than an unlabelled one-point intersection assertion. -/
theorem vertical_cap_of_squares {C : Set Plane} {r b : ℝ}
    (hC : IsJordanCurve C) (hr : 0 < r) (hrb : r < b)
    (hleft : Plane.openSquare 0 r ⊆ inside C)
    (hright : rightStrip r b ⊆ outside C) :
    ∀ y : ℝ, |y| < r → Plane.mk r y ∈ C := by
  intro y hy
  let f : ℝ → Plane := fun x => Plane.mk x y
  have hfc : Continuous f := by fun_prop
  have hrightim : f '' Ioc r b ⊆ outside C := by
    rintro x ⟨t,ht,rfl⟩
    exact hright ⟨ht.1,ht.2,(abs_lt.mp hy).1,(abs_lt.mp hy).2⟩
  have hrcl : r ∈ closure (Ioc r b) := by
    rw [closure_Ioc (ne_of_lt hrb)]
    exact ⟨le_rfl,hrb.le⟩
  have houtcl : f r ∈ closure (outside C) :=
    closure_mono hrightim (image_closure_subset_closure_image hfc ⟨r,hrcl,rfl⟩)
  have hleftim : f '' Ioo (r/2) r ⊆ inside C := by
    rintro x ⟨t,ht,rfl⟩
    apply hleft
    have htpos : 0 < t := by linarith [ht.1]
    simpa [f,Plane.openSquare,Plane.supDist,Plane.supNorm] using
      (max_lt (show |t| < r by simpa only [abs_of_pos htpos] using ht.2) hy)
  have hlcl : r ∈ closure (Ioo (r/2) r) := by
    rw [closure_Ioo (by linarith : r/2 ≠ r)]
    exact ⟨by linarith,le_rfl⟩
  have hincl : f r ∈ closure (inside C) :=
    closure_mono hleftim (image_closure_subset_closure_image hfc ⟨r,hlcl,rfl⟩)
  have hsep := jordan_curve_theorem hC
  have hnotin : f r ∉ inside C := by
    have hh : outside C ⊆ (inside C)ᶜ :=
      fun x hx hxi => Set.disjoint_left.1 disjoint_inside_outside hxi hx
    exact closure_minimal hh hsep.isOpen_inside.isClosed_compl houtcl
  have hnotout : f r ∉ outside C := by
    have hh : inside C ⊆ (outside C)ᶜ :=
      fun x hx hxo => Set.disjoint_left.1 disjoint_inside_outside hx hxo
    exact closure_minimal hh hsep.isOpen_outside.isClosed_compl hincl
  by_contra hn
  have hs : f r ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hn
  exact hs.elim hnotin hnotout

/-- Endpoint-pinned construction. The terminal shape and compact unwanted set
will be DERIVED from the same original edge in the source-facing theorem. -/
theorem sampled_terminal_cap (α : ℝ → Plane) (hα : ContinuousOn α I)
    (hi : InjOn α I) (hend : α 1 = 0) {L : Set Plane}
    (hL : IsCompact L) (hdisj : Disjoint L (α '' I))
    {b δ : ℝ} (hb : 0 < b) (hδ : 0 < δ)
    (hbase : Plane.mk b 0 ∈ L) (hterm : TerminalPrefix (α '' I) b δ) :
    ∃ (r : ℝ) (C : Set Plane),
      0 < r ∧ r < b ∧ IsJordanCurve C ∧ α '' I ⊆ inside C ∧
      L ⊆ outside C ∧ Plane.openSquare 0 r ⊆ inside C ∧
      rightStrip r b ⊆ outside C ∧
      (∀ y : ℝ, |y| < r → Plane.mk r y ∈ C) := by
  let ε := min (b/4) (δ/8)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨N,r,C,hN,hr,hrε,hC,hAin,hLout,hCsub,hOpen⟩ :=
    sampled_neighborhood α hα hi hL ⟨_,hbase⟩ hdisj hε
  have hrb : r < b := by
    have hh : ε ≤ b/4 := min_le_left _ _
    linarith
  have hsmall : 2*r < δ := by
    have hh : ε ≤ δ/8 := min_le_right _ _
    linarith
  have hleft : Plane.openSquare 0 r ⊆ inside C := by
    have hh := hOpen N le_rfl
    simpa only [sample_last hN,hend] using hh
  have hSC : rightStrip r b ⊆ Cᶜ := by
    intro x hx hxC
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (hCsub hxC)
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    have ha : α (sample N j) ∈ α '' I := ⟨_,sample_mem_I hjN,rfl⟩
    exact strip_misses_square hterm hr hsmall ha hx
      ((Plane.isClosed_closedSquare _ _).frontier_subset hxj)
  have hbS : Plane.mk b 0 ∈ rightStrip r b := by
    simpa [rightStrip] using
      (show r < b ∧ b ≤ b ∧ -r < (0:ℝ) ∧ (0:ℝ) < r from
        ⟨hrb,le_rfl,by linarith,hr⟩)
  have hScomp : rightStrip r b ⊆ connectedComponentIn Cᶜ (Plane.mk b 0) :=
    (rightStrip_preconnected r b).subset_connectedComponentIn hbS hSC
  have hright : rightStrip r b ⊆ outside C :=
    hScomp.trans (connectedComponentIn_subset_outside (hLout hbase))
  exact ⟨r,C,hr,hrb,hC,hAin,hLout,hleft,hright,
    vertical_cap_of_squares hC hr hrb hleft hright⟩

#print axioms sampled_terminal_cap
end Nanuq.Pendant
