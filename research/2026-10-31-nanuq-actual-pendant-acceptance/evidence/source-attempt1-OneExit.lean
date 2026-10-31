import TerminalCap
import Schoenflies.TwoArcs

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Pendant
open Set Schoenflies unitInterval

/-- A Jordan curve with one point removed is connected. The second retained
point is explicit, so no nonemptiness or singleton convention is hidden. -/
theorem punctured_jordan_preconnected {C : Set Plane} (hC : IsJordanCurve C)
    {q z : Plane} (hq : q ∈ C) (hz : z ∈ C) (hqz : q ≠ z) :
    IsPreconnected (C \ {q}) := by
  obtain ⟨A,B,hA,hB,hcover,hmeet⟩ := hC.two_arcs hq hz hqz
  have harc : ∀ S : Set Plane, IsArcBetween S q z → IsPreconnected (S \ {q}) := by
    intro S hS
    obtain ⟨f,hfc,hfi,hfim,hf0,hf1⟩ := hS
    have heq : S \ {q} = f '' Ioc 0 1 := by
      rw [← hfim]
      ext x
      constructor
      · rintro ⟨⟨t,ht,rfl⟩,hne⟩
        refine ⟨t,⟨lt_of_le_of_ne ht.1 ?_,ht.2⟩,rfl⟩
        intro he
        exact hne (by simpa [he.symm,hf0])
      · rintro ⟨t,ht,rfl⟩
        refine ⟨⟨t,⟨ht.1.le,ht.2⟩,rfl⟩,?_⟩
        intro he
        have ht0 := hfi ⟨ht.1.le,ht.2⟩ zero_mem_I
          ((show f t=q from he).trans hf0.symm)
        linarith [ht.1]
    rw [heq]
    exact (isPreconnected_Ioc.image _ (hfc.mono Ioc_subset_Icc_self))
  have hzA : z ∈ A \ {q} := ⟨hA.right_mem,Ne.symm hqz⟩
  have hzB : z ∈ B \ {q} := ⟨hB.right_mem,Ne.symm hqz⟩
  have hu := IsPreconnected.union z hzA hzB (harc A hA) (harc B hB)
  have heq : (A \ {q}) ∪ (B \ {q}) = C \ {q} := by
    rw [← union_diff_distrib,hcover]
  exact heq ▸ hu

/-- The same sampled boundary has exactly one intersection with the WHOLE
trace. The two explicitly labelled upper/lower side points return through
that punctured boundary in the original trace complement. This is not a
claim of global face-orbit order or relative slit-domain connectedness. -/
theorem terminal_one_exit {A L C : Set Plane} {r b : ℝ}
    (hr : 0 < r) (hrb : r < b) (hC : IsJordanCurve C)
    (hA : A ⊆ inside C) (hL : L ⊆ outside C)
    (hleft : Plane.openSquare 0 r ⊆ inside C)
    (hright : rightStrip r b ⊆ outside C)
    (hcap : ∀ y : ℝ, |y| < r → Plane.mk r y ∈ C) :
    let T := A ∪ segment ℝ (0:Plane) (Plane.mk b 0) ∪ L
    C ∩ T = {Plane.mk r 0} ∧
    (C ∪ inside C) ∩ T = A ∪ segment ℝ (0:Plane) (Plane.mk r 0) ∧
    Plane.mk r (r/2) ∈ C \ T ∧ Plane.mk r (-r/2) ∈ C \ T ∧
    Plane.mk r (-r/2) ∈ connectedComponentIn Tᶜ (Plane.mk r (r/2)) := by
  dsimp only
  let Q := segment ℝ (0:Plane) (Plane.mk b 0)
  let T := A ∪ Q ∪ L
  have hq : Plane.mk r 0 ∈ C := hcap 0 (by simpa using hr)
  have hqQ : Plane.mk r 0 ∈ Q := by
    change Plane.mk r 0 ∈ segment ℝ (Plane.mk 0 0) (Plane.mk b 0)
    rw [mem_segment_horiz,segment_eq_Icc (by linarith : (0:ℝ)≤b)]
    exact ⟨rfl,hr.le,hrb.le⟩
  have hline : ∀ x ∈ Q, x 1=0 ∧ x 0 ∈ Icc 0 b := by
    intro x hx
    change x ∈ segment ℝ (Plane.mk 0 0) (Plane.mk b 0) at hx
    rwa [mem_segment_horiz,segment_eq_Icc (by linarith : (0:ℝ)≤b)] at hx
  have hsmall : ∀ x ∈ Q, x 0 < r → x ∈ inside C := by
    intro x hx hxr
    obtain ⟨hy,hxx⟩ := hline x hx
    apply hleft
    change max |x 0| |x 1| < r
    rw [hy,abs_zero,abs_of_nonneg hxx.1]
    exact max_lt hxr hr
  have hlarge : ∀ x ∈ Q, r < x 0 → x ∈ outside C := by
    intro x hx hxr
    obtain ⟨hy,hxx⟩ := hline x hx
    exact hright ⟨hxr,hxx.2,by rw [hy]; linarith,by simpa [hy] using hr⟩
  have hnotCin : Disjoint C (inside C) := by
    rw [Set.disjoint_left]
    intro x hx hxi
    have hh : x ∈ Cᶜ := by rw [← inside_union_outside]; exact Or.inl hxi
    exact hh hx
  have hnotCout : Disjoint C (outside C) := by
    rw [Set.disjoint_left]
    intro x hx hxo
    have hh : x ∈ Cᶜ := by rw [← inside_union_outside]; exact Or.inr hxo
    exact hh hx
  have hinter : C ∩ T = {Plane.mk r 0} := by
    ext x
    constructor
    · rintro ⟨hxC,(hxA | hxQ) | hxL⟩
      · exact False.elim (Set.disjoint_left.mp hnotCin hxC (hA hxA))
      · have hxr : x 0=r := by
          rcases lt_trichotomy (x 0) r with h | h | h
          · exact False.elim (Set.disjoint_left.mp hnotCin hxC (hsmall x hxQ h))
          · exact h
          · exact False.elim (Set.disjoint_left.mp hnotCout hxC (hlarge x hxQ h))
        have hy := (hline x hxQ).1
        change x=Plane.mk r 0
        ext i
        fin_cases i <;> assumption
      · exact False.elim (Set.disjoint_left.mp hnotCout hxC (hL hxL))
    · intro hx
      rcases hx with rfl
      exact ⟨hq,Or.inl (Or.inr hqQ)⟩
  have hclosed : (C ∪ inside C) ∩ T = A ∪ segment ℝ (0:Plane) (Plane.mk r 0) := by
    ext x
    constructor
    · rintro ⟨hx,(hxA | hxQ) | hxL⟩
      · exact Or.inl hxA
      · right
        obtain ⟨hy,hxx⟩ := hline x hxQ
        have hxr : x 0 ≤ r := by
          by_contra hn
          have hxo := hlarge x hxQ (lt_of_not_ge hn)
          exact hx.elim (fun hc => Set.disjoint_left.mp hnotCout hc hxo)
            (fun hi => Set.disjoint_left.mp disjoint_inside_outside hi hxo)
        change x ∈ segment ℝ (Plane.mk 0 0) (Plane.mk r 0)
        rw [mem_segment_horiz,segment_eq_Icc hr.le]
        exact ⟨hy,hxx.1,hxr⟩
      · exact False.elim (hx.elim (fun hc => Set.disjoint_left.mp hnotCout hc (hL hxL))
          (fun hi => Set.disjoint_left.mp disjoint_inside_outside hi (hL hxL)))
    · intro hx
      rcases hx with hxA | hxR
      · exact ⟨Or.inr (hA hxA),Or.inl (Or.inl hxA)⟩
      · have hrcoords : x 1=0 ∧ x 0 ∈ Icc 0 r := by
          change x ∈ segment ℝ (Plane.mk 0 0) (Plane.mk r 0) at hxR
          rwa [mem_segment_horiz,segment_eq_Icc hr.le] at hxR
        have hxQ : x∈Q := by
          change x ∈ segment ℝ (Plane.mk 0 0) (Plane.mk b 0)
          rw [mem_segment_horiz,segment_eq_Icc (by linarith : (0:ℝ)≤b)]
          exact ⟨hrcoords.1,hrcoords.2.1,hrcoords.2.2.trans hrb.le⟩
        refine ⟨?_,Or.inl (Or.inr hxQ)⟩
        rcases lt_or_eq_of_le hrcoords.2.2 with hlt | heq
        · exact Or.inr (hsmall x hxQ hlt)
        · left
          have hxq : x=Plane.mk r 0 := by
            ext i
            fin_cases i
            · exact heq
            · exact hrcoords.1
          exact hxq ▸ hq
  have huC : Plane.mk r (r/2)∈C := hcap _ (by rw [abs_of_pos (by linarith)]; linarith)
  have hdC : Plane.mk r (-r/2)∈C := hcap _ (by rw [abs_of_neg (by linarith)]; linarith)
  have huq : Plane.mk r (r/2) ≠ Plane.mk r 0 := by intro he; have := congrArg (fun p : Plane => p 1) he; simp at this; linarith
  have hdq : Plane.mk r (-r/2) ≠ Plane.mk r 0 := by intro he; have := congrArg (fun p : Plane => p 1) he; simp at this; linarith
  have hpunct : C \ {Plane.mk r 0} ⊆ Tᶜ := by
    intro x hx hxt
    exact hx.2 (hinter ▸ ⟨hx.1,hxt⟩)
  have hpre := punctured_jordan_preconnected hC hq huC (Ne.symm huq)
  have hcomp := hpre.subset_connectedComponentIn ⟨huC,huq⟩ hpunct
  exact ⟨hinter,hclosed,⟨huC,hpunct ⟨huC,huq⟩⟩,
    ⟨hdC,hpunct ⟨hdC,hdq⟩⟩,hcomp ⟨hdC,hdq⟩⟩

#print axioms terminal_one_exit
end Nanuq.Pendant
