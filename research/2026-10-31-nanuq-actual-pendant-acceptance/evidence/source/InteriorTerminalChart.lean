import HorizontalArc
import TerminalCap
import ThreeGermFrame

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Pendant
open Set Schoenflies unitInterval

/-- The terminal shape is derived from TWO portions of the SAME actual full
edge, not from an added graph vertex, local collar or endpoint-access premise. -/
theorem interior_terminal_chart (f : ℝ → Plane) (hc : ContinuousOn f I)
    (hi : InjOn f I) :
    ∃ (H : Plane ≃ₜ Plane) (b δ : ℝ),
      0 < b ∧ 0 < δ ∧ H (f (1/2)) = 0 ∧ H (f (13/24)) = Plane.mk b 0 ∧
      H '' (f '' Icc (1/2) (13/24)) = segment ℝ (0:Plane) (Plane.mk b 0) ∧
      TerminalPrefix (H '' (f '' Icc 0 (1/2))) b δ := by
  let g : ℝ → Plane := fun t => f (1/2+t/4)
  let k : ℝ → Plane := fun t => f (1/2-t/4)
  have hgI : ∀ t ∈ I, (1/2:ℝ)+t/4 ∈ I := by
    intro t ht; exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hkI : ∀ t ∈ I, (1/2:ℝ)-t/4 ∈ I := by
    intro t ht; exact ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hgc : ContinuousOn g I := hc.comp (by fun_prop) hgI
  have hkc : ContinuousOn k I := hc.comp (by fun_prop) hkI
  have hgi : InjOn g I := by
    intro t ht u hu he
    have hh := hi (hgI t ht) (hgI u hu) he
    linarith
  have hki : InjOn k I := by
    intro t ht u hu he
    have hh := hi (hkI t ht) (hkI u hu) he
    linarith
  have hgk0 : g 0 = k 0 := by simp [g,k]
  have hmeet : ∀ z ∈ g '' I, z ∈ k '' I → z = g 0 := by
    rintro z ⟨t,ht,rfl⟩ ⟨u,hu,he⟩
    have hh := hi (hkI u hu) (hgI t ht) he
    have ht0 : t=0 := by linarith [ht.1,hu.1]
    rw [ht0]
  obtain ⟨H0,hcarrier,hplus,hminus,hvy,hvc⟩ :=
    Nanuq.ActualStar.straighten_two_continued_germs g k hgc hkc hgi hki hgk0 hmeet
  let v := H0 (f (1/2))
  let H := H0.trans (Nanuq.ActualStar.shiftVertex v)
  have hv0 : v 1 = 0 := by simpa [v,g] using hvy
  have hH0 : H (f (1/2)) = 0 := by change H0 (f (1/2))-v=0; simp [v]
  have hplus' : H0 (f (7/12)) = Plane.mk 2 0 := by
    norm_num [g] at hplus
    exact hplus
  have hminus' : H0 (f (5/12)) = Plane.mk (-2) 0 := by
    norm_num [k] at hminus
    exact hminus
  have hI : Icc (5/12:ℝ) (7/12) ⊆ I := by
    intro t ht; exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hline0 : ∀ t ∈ Icc (5/12:ℝ) (7/12), (H0 (f t)) 1 = 0 := by
    intro t ht
    have hmem : f t ∈ g '' Icc 0 (1/3) ∪ k '' Icc 0 (1/3) := by
      by_cases hmid : (1/2:ℝ) ≤ t
      · left
        refine ⟨4*(t-1/2),⟨by linarith,by linarith [ht.2]⟩,?_⟩
        dsimp [g]
        congr 1
        ring
      · right
        refine ⟨4*(1/2-t),⟨by linarith,by linarith [ht.1]⟩,?_⟩
        dsimp [k]
        congr 1
        ring
    have hh : H0 (f t) ∈ Nanuq.CornerShear.horizontal := hcarrier ▸ mem_image_of_mem H0 hmem
    exact hh.1
  have hline : ∀ t ∈ Icc (5/12:ℝ) (7/12), H (f t) 1 = 0 := by
    intro t ht
    change (H0 (f t)) 1-v 1=0
    rw [hline0 t ht,hv0,sub_self]
  have hHc : ContinuousOn (fun t => H (f t)) I := H.continuous.comp_continuousOn hc
  have hHi : InjOn (fun t => H (f t)) I := fun t ht u hu he => hi ht hu (H.injective he)
  have hsc : ContinuousOn (fun t => H (f t) 0) (Icc (5/12) (7/12)) :=
    (show Continuous (fun z : Plane => z 0) by fun_prop).comp_continuousOn (hHc.mono hI)
  have hsi := horizontal_coordinate_inj (hHi.mono hI) hline
  have hends : H (f (5/12)) 0 ≤ H (f (7/12)) 0 := by
    change (H0 (f (5/12))) 0-v 0 ≤ (H0 (f (7/12))) 0-v 0
    rw [hminus',hplus']
    norm_num [Plane.mk] <;> linarith
  have hmono : StrictMonoOn (fun t => H (f t) 0) (Icc (5/12) (7/12)) :=
    ContinuousOn.strictMonoOn_of_injOn_Icc (by norm_num) hends hsc hsi
  let b := H (f (13/24)) 0
  have hhalf : (1/2:ℝ) ∈ Icc (5/12) (7/12) := by norm_num
  have hend : (13/24:ℝ) ∈ Icc (5/12) (7/12) := by norm_num
  have hb : 0 < b := by
    have hh := hmono hhalf hend (by norm_num : (1/2:ℝ)<13/24)
    change H (f (1/2)) 0 < H (f (13/24)) 0 at hh
    rw [hH0] at hh
    simpa [b] using hh
  have hHb : H (f (13/24)) = Plane.mk b 0 := by
    ext i
    fin_cases i
    · rfl
    · exact hline _ hend
  have hsub : Icc (1/2:ℝ) (13/24) ⊆ Icc (5/12) (7/12) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have hseg : H '' (f '' Icc (1/2) (13/24)) = segment ℝ (0:Plane) (Plane.mk b 0) := by
    rw [Set.image_image]
    have hh := horizontal_arc_image (f := fun t => H (f t))
      (show (1/2:ℝ) ≤ 13/24 by norm_num) (hHc.mono (hsub.trans hI))
      (hHi.mono (hsub.trans hI)) (fun t ht => hline t (hsub ht))
    simpa only [hH0,hHb] using hh
  let R := H '' (f '' Icc 0 (5/12))
  let Q := segment ℝ (0:Plane) (Plane.mk b 0)
  have hRI : Icc (0:ℝ) (5/12) ⊆ I := Icc_subset_Icc le_rfl (by norm_num)
  have hRc : IsCompact R :=
    (isCompact_Icc.image_of_continuousOn (hc.mono hRI)).image H.continuous
  have hQc : IsCompact Q := by
    simpa only [Q] using (isCompact_segment (0:Plane) (Plane.mk b 0))
  have hRQ : Disjoint R Q := by
    rw [Set.disjoint_left]
    rintro z ⟨x,⟨t,ht,rfl⟩,rfl⟩ hzQ
    have hzIm : H (f t) ∈ H '' (f '' Icc (1/2) (13/24)) := hseg.symm ▸ hzQ
    obtain ⟨y,⟨u,hu,rfl⟩,he⟩ := hzIm
    have htu := hi (hsub.trans hI hu) (hRI ht) (H.injective he)
    linarith [ht.2,hu.1]
  obtain ⟨ρ,hρ,hsep⟩ := Plane.exists_dist_pos hRc hQc hRQ
  refine ⟨H,b,ρ/2,hb,by linarith,hH0,hHb,hseg,?_⟩
  rintro a ⟨x,⟨t,ht,rfl⟩,rfl⟩
  by_cases hnear : (5/12:ℝ) ≤ t
  · left
    have htcentral : t ∈ Icc (5/12:ℝ) (7/12) := ⟨hnear,by linarith [ht.2]⟩
    refine ⟨hline t htcentral,?_⟩
    have hh := hmono.monotoneOn htcentral hhalf ht.2
    change H (f t) 0 ≤ H (f (1/2)) 0 at hh
    rw [hH0] at hh
    simpa using hh
  · right
    intro x hx
    have htR : t ∈ Icc (0:ℝ) (5/12) := ⟨ht.1,(lt_of_not_ge hnear).le⟩
    have haR : H (f t) ∈ R := ⟨f t,⟨t,htR,rfl⟩,rfl⟩
    have hxQ : Plane.mk x 0 ∈ Q := by
      dsimp only [Q]
      have hz : (0:Plane) = Plane.mk 0 0 := by
        ext i; fin_cases i <;> simp
      rw [hz,mem_segment_horiz,segment_eq_Icc hb.le]
      exact ⟨rfl,hx⟩
    exact (lt_supDist_of_le_dist hρ (hsep _ haR _ hxQ)).le

#print axioms interior_terminal_chart
end Nanuq.Pendant
