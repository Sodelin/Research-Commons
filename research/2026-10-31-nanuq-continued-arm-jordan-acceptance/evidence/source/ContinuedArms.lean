import Schoenflies.JordanClosed
import Schoenflies.Graph.VertexSquares
import Schoenflies.Concatenate

/-! UNCOMPILED. Compact-extrema joining of actual access continuations.
No finite-intersection, polygonal-accessibility, collar or cyclic-order premise. -/
noncomputable section
namespace Nanuq.ContinuedArms
open Set Schoenflies unitInterval

/-- Two disjoint continuous continuations from the endpoints of A give a
complementary arc. The connecting polygonal arc is only required OFF A. -/
theorem complementary_arc_of_continuations
    {A J₁ J₂ : Set Plane} {q₁ q₂ r₁ r₂ : Plane}
    (hA : IsArcBetween A q₁ q₂)
    (hJ₁ : IsArcBetween J₁ q₁ r₁) (hJ₂ : IsArcBetween J₂ q₂ r₂)
    (hdisj : Disjoint J₁ J₂) (hr₁ : r₁ ∉ A) (hr₂ : r₂ ∉ A)
    (hmeet₁ : ∀ z ∈ J₁, z ∈ A → z = q₁)
    (hmeet₂ : ∀ z ∈ J₂, z ∈ A → z = q₂) :
    ∃ B, IsArcBetween B q₁ q₂ ∧ A ∩ B = {q₁,q₂} ∧ IsJordanCurve (A ∪ B) := by
  have hrne : r₁ ≠ r₂ := fun h => Set.disjoint_left.mp hdisj
    hJ₁.right_mem (h.symm ▸ hJ₂.right_mem)
  obtain ⟨P,_,hP,hPA⟩ := arc_complement_poly hA.isArc hrne hr₁ hr₂
  obtain ⟨p,hpc,hpi,hpim,hp0,hp1⟩ := hP
  have hpend₂ : p 1 ∈ J₂ := hp1.symm ▸ hJ₂.right_mem
  obtain ⟨s,hsI,_,hsJ₂,hfirst⟩ := exists_first_mem hpc hJ₂.isArc.isClosed one_mem_I hpend₂
  have hzero : (0 : ℝ) ∈ Icc 0 s := ⟨le_rfl,hsI.1⟩
  have hpc' : ContinuousOn p (Icc 0 s) := hpc.mono (Icc_subset_Icc le_rfl hsI.2)
  have hpend₁ : p 0 ∈ J₁ := hp0.symm ▸ hJ₁.right_mem
  obtain ⟨t,htI,_,htJ₁,hlast⟩ := exists_last_mem_Icc hpc' hJ₁.isArc.isClosed hzero hpend₁
  have htI' : t ∈ I := ⟨htI.1,htI.2.trans hsI.2⟩
  have hts : t < s := lt_of_le_of_ne htI.2 (fun h =>
    Set.disjoint_left.mp hdisj htJ₁ (h.symm ▸ hsJ₂))
  have hsubI : Icc t s ⊆ I := Icc_subset_Icc htI.1 hsI.2
  let M := p '' Icc t s
  have hM : IsArcBetween M (p t) (p s) := by
    simpa only [M,uIcc_of_le hts.le] using
      isArcBetween_subarc_of_injOn_I hpc hpi htI' hsI (ne_of_lt hts)
  have hM₁ : ∀ z ∈ M, z ∈ J₁ → z = p t := by
    rintro z ⟨u,hu,rfl⟩ hz
    have hut : u = t := by
      by_contra hn
      exact hlast u ⟨htI.1.trans hu.1,hu.2⟩
        (lt_of_le_of_ne hu.1 (Ne.symm hn)) hz
    rw [hut]
  have hM₂ : ∀ z ∈ M, z ∈ J₂ → z = p s := by
    rintro z ⟨u,hu,rfl⟩ hz
    have hus : u = s := by
      by_contra hn
      exact hfirst u (hsubI hu) (lt_of_le_of_ne hu.2 hn) hz
    rw [hus]
  have hMA : Disjoint M A := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u,hu,rfl⟩ hz
    exact hPA (hpim ▸ mem_image_of_mem p (hsubI hu)) hz
  have hq₁t : q₁ ≠ p t := by
    intro h
    exact Set.disjoint_left.mp hMA (mem_image_of_mem p ⟨le_rfl,hts.le⟩)
      (h ▸ hA.left_mem)
  have hq₂s : q₂ ≠ p s := by
    intro h
    exact Set.disjoint_left.mp hMA (mem_image_of_mem p ⟨hts.le,le_rfl⟩)
      (h ▸ hA.right_mem)
  obtain ⟨L,hLsub,hL⟩ := hJ₁.isArc.exists_isArcBetween_subset hJ₁.left_mem htJ₁ hq₁t
  obtain ⟨R,hRsub,hR⟩ := hJ₂.isArc.exists_isArcBetween_subset hJ₂.left_mem hsJ₂ hq₂s
  have hLM : IsArcBetween (L ∪ M) q₁ (p s) :=
    hL.concatenate hM (fun z hzL hzM => hM₁ z hzM (hLsub hzL))
  have hB : IsArcBetween ((L ∪ M) ∪ R) q₁ q₂ := by
    apply hLM.concatenate hR.reverse
    intro z hz hzR
    rcases hz with hzL | hzM
    · exact False.elim (Set.disjoint_left.mp hdisj (hLsub hzL) (hRsub hzR))
    · exact hM₂ z hzM (hRsub hzR)
  have hmeet : ∀ z ∈ A, z ∈ (L ∪ M) ∪ R → z = q₁ ∨ z = q₂ := by
    intro z hzA hz
    rcases hz with (hzL | hzM) | hzR
    · exact Or.inl (hmeet₁ z (hLsub hzL) hzA)
    · exact False.elim (Set.disjoint_left.mp hMA hzM hzA)
    · exact Or.inr (hmeet₂ z (hRsub hzR) hzA)
  refine ⟨(L ∪ M) ∪ R,hB,?_,IsJordanCurve.of_two_arcs hA hB.reverse hmeet⟩
  apply Set.Subset.antisymm
  · rintro z ⟨hzA,hzB⟩
    exact hmeet z hzA hzB
  · intro z hz
    rcases hz with rfl | rfl
    · exact ⟨hA.left_mem,hB.left_mem⟩
    · exact ⟨hA.right_mem,hB.right_mem⟩


/-- Named fractions are merely interior cutpoints on the actual continued germs. -/
theorem jordan_through_two_germs
    (f g : ℝ → Plane) (hfc : ContinuousOn f I) (hgc : ContinuousOn g I)
    (hfi : InjOn f I) (hgi : InjOn g I) (h0 : f 0 = g 0)
    (hmeet : ∀ z ∈ f '' I, z ∈ g '' I → z = f 0) :
    ∃ B : Set Plane,
      IsArcBetween B (f (1/3)) (g (1/3)) ∧
      (f '' Icc 0 (1/3) ∪ g '' Icc 0 (1/3)) ∩ B = {f (1/3),g (1/3)} ∧
      IsJordanCurve ((f '' Icc 0 (1/3) ∪ g '' Icc 0 (1/3)) ∪ B) ∧ f 0 ∉ B := by
  let a : ℝ := 1/3
  let b : ℝ := 2/3
  have haI : a ∈ I := by
    change 0 ≤ a ∧ a ≤ 1
    norm_num [a]
  have hbI : b ∈ I := by
    change 0 ≤ b ∧ b ≤ 1
    norm_num [b]
  have ha0 : 0 < a := by norm_num [a]
  have hab : a < b := by norm_num [a,b]
  have hIa : Icc 0 a ⊆ I := Icc_subset_Icc le_rfl haI.2
  have hIab : Icc a b ⊆ I := Icc_subset_Icc haI.1 hbI.2
  let A₁ := f '' Icc 0 a
  let A₂ := g '' Icc 0 a
  let J₁ := f '' Icc a b
  let J₂ := g '' Icc a b
  have hA₁ : IsArcBetween A₁ (f 0) (f a) := by
    simpa only [A₁,uIcc_of_le ha0.le] using
      isArcBetween_subarc_of_injOn_I hfc hfi zero_mem_I haI (ne_of_lt ha0)
  have hA₂ : IsArcBetween A₂ (f 0) (g a) := by
    rw [h0]
    simpa only [A₂,uIcc_of_le ha0.le] using
      isArcBetween_subarc_of_injOn_I hgc hgi zero_mem_I haI (ne_of_lt ha0)
  have hA : IsArcBetween (A₁ ∪ A₂) (f a) (g a) :=
    hA₁.reverse.concatenate hA₂ (fun z hz₁ hz₂ =>
      hmeet z (image_mono hIa hz₁) (image_mono hIa hz₂))
  have hJ₁ : IsArcBetween J₁ (f a) (f b) := by
    simpa only [J₁,uIcc_of_le hab.le] using
      isArcBetween_subarc_of_injOn_I hfc hfi haI hbI (ne_of_lt hab)
  have hJ₂ : IsArcBetween J₂ (g a) (g b) := by
    simpa only [J₂,uIcc_of_le hab.le] using
      isArcBetween_subarc_of_injOn_I hgc hgi haI hbI (ne_of_lt hab)
  have hdisj : Disjoint J₁ J₂ := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u,hu,rfl⟩ ⟨w,hw,he⟩
    have he0 := hmeet (f u) ⟨u,hIab hu,rfl⟩ ⟨w,hIab hw,he⟩
    have hu0 := hfi (hIab hu) zero_mem_I he0
    exact (not_le_of_gt ha0) (hu0 ▸ hu.1)
  have hmeet₁ : ∀ z ∈ J₁, z ∈ A₁ ∪ A₂ → z = f a := by
    rintro z ⟨u,hu,rfl⟩ (⟨w,hw,he⟩ | ⟨w,hw,he⟩)
    · have hwu := hfi (hIa hw) (hIab hu) he
      have hua : u = a := le_antisymm (hwu ▸ hw.2) hu.1
      rw [hua]
    · have he0 := hmeet (f u) ⟨u,hIab hu,rfl⟩ ⟨w,hIa hw,he⟩
      have hu0 := hfi (hIab hu) zero_mem_I he0
      exact False.elim ((not_le_of_gt ha0) (hu0 ▸ hu.1))
  have hmeet₂ : ∀ z ∈ J₂, z ∈ A₁ ∪ A₂ → z = g a := by
    rintro z ⟨u,hu,rfl⟩ (⟨w,hw,he⟩ | ⟨w,hw,he⟩)
    · have he0 := hmeet (g u) ⟨w,hIa hw,he⟩ ⟨u,hIab hu,rfl⟩
      have hu0 := hgi (hIab hu) zero_mem_I (he0.trans h0)
      exact False.elim ((not_le_of_gt ha0) (hu0 ▸ hu.1))
    · have hwu := hgi (hIa hw) (hIab hu) he
      have hua : u = a := le_antisymm (hwu ▸ hw.2) hu.1
      rw [hua]
  have hr₁ : f b ∉ A₁ ∪ A₂ := by
    intro hz
    have hba := hfi hbI haI (hmeet₁ _ hJ₁.right_mem hz)
    exact (ne_of_gt hab) hba
  have hr₂ : g b ∉ A₁ ∪ A₂ := by
    intro hz
    have hba := hgi hbI haI (hmeet₂ _ hJ₂.right_mem hz)
    exact (ne_of_gt hab) hba
  obtain ⟨B,hB,hAB,hJordan⟩ := complementary_arc_of_continuations hA hJ₁ hJ₂ hdisj hr₁ hr₂ hmeet₁ hmeet₂
  refine ⟨B,hB,hAB,hJordan,?_⟩
  intro hvB
  have hvA : f 0 ∈ A₁ ∪ A₂ := Or.inl hA₁.left_mem
  have hv : f 0 = f a ∨ f 0 = g a := by
    change f 0 ∈ ({f a,g a} : Set Plane)
    rw [← hAB]
    exact ⟨hvA,hvB⟩
  rcases hv with hv | hv
  · exact (ne_of_lt ha0) (hfi zero_mem_I haI hv)
  · exact (ne_of_lt ha0) (hgi zero_mem_I haI (h0.symm.trans hv))

#print axioms complementary_arc_of_continuations
#print axioms jordan_through_two_germs
end Nanuq.ContinuedArms
