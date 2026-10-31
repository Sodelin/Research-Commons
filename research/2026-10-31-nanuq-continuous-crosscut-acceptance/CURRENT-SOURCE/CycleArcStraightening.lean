import PrescribedLoopAmbient

set_option debug.skipKernelTC false
/-! UNCOMPILED source-only adapter. A single ambient map sends the TWO given
cycle arcs to the two prescribed model arcs, preserving their individual
endpoint labels. All later conclusions must be pulled back to the original
drawing. This is not a simultaneous independent redrawing of graph edges. -/
namespace Nanuq.PrescribedLoopAmbient
open Set Schoenflies unitInterval

 theorem image_lower_half (f g : ℝ → Plane) :
    concatenate f g '' lowerHalf = f '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨2*t, double_mem_I ht, (concatenate_of_le ht.2).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t/2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [concatenate_of_le (by linarith [ht.2])]
    congr 1
    ring

 theorem image_upper_half (f g : ℝ → Plane) (hm : f 1 = g 0) :
    concatenate f g '' upperHalf = g '' I := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨2*t-1, doubleBack_mem_I ht, (concatenate_upperHalf hm ht).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(t+1)/2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [concatenate_upperHalf hm ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1
    ring

/-- Exact same-map straightening, including original parallel-edge bigons. -/
theorem cycle_arc_straightening {P Q : Set Plane} {p q : Plane}
    (hP : IsArcBetween P p q) (hQ : IsArcBetween Q q p)
    (hmeet : ∀ z ∈ P, z ∈ Q → z = p ∨ z = q) :
    ∃ H : Plane ≃ₜ Plane,
      H '' P = sideTop ∪ sideLeft ∧ H '' Q = sideBottom ∪ sideRight ∧
      H p = cornerNE ∧ H q = cornerSW ∧ IsPolygonal (H '' P) := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hP
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hQ
  obtain ⟨u, huc, hui, huim, hu0, hu1⟩ := isArcBetween_upperSides
  obtain ⟨v, hvc, hvi, hvim, hv0, hv1⟩ := isArcBetween_lowerSides
  have hm : f 1 = g 0 := by rw [hf1,hg0]
  have hm' : u 1 = v 0 := by rw [hu1,hv0]
  have hl : IsLoop (concatenate f g) := IsLoop.concatenate hfc hfi hgc hgi hm
    (by rw [hg1,hf0]) (by
      intro z hz hz'
      rw [hfim] at hz
      rw [hgim] at hz'
      rw [hf0,hf1]
      exact hmeet z hz hz')
  have hl' : IsLoop (concatenate u v) := IsLoop.concatenate huc hui hvc hvi hm'
    (by rw [hv1,hu0]) (by
      intro z hz hz'
      rw [huim] at hz
      rw [hvim] at hz'
      rw [hu0,hu1]
      exact upperSides_meet_lowerSides z hz hz')
  obtain ⟨H, hp, hs⟩ := loop_parameters hl hl'
  have hPim := hs lowerHalf lowerHalf_subset_I
  rw [image_lower_half, image_lower_half, hfim, huim] at hPim
  have hQim := hs upperHalf upperHalf_subset_I
  rw [image_upper_half f g hm, image_upper_half u v hm', hgim, hvim] at hQim
  have hp0 := hp 0 zero_mem_I
  rw [concatenate_zero,concatenate_zero,hf0,hu0] at hp0
  have hp1 := hp (1/2) (show (1/2:ℝ) ∈ I by norm_num)
  rw [concatenate_of_le le_rfl,concatenate_of_le le_rfl] at hp1
  have hp1' : H q = cornerSW := by
    have he : (2:ℝ)*(1/2)=1 := by norm_num
    simpa only [he,hf1,hu1] using hp1
  refine ⟨H,hPim,hQim,hp0,hp1',?_⟩
  rw [hPim]
  refine ⟨[cornerNE,cornerNW,cornerSW], ?_⟩
  rw [poly_cons_cons, poly_pair]
  rfl

#print axioms cycle_arc_straightening
end Nanuq.PrescribedLoopAmbient
