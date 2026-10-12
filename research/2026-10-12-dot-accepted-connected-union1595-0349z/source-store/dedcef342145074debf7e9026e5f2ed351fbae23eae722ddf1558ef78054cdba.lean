import G1RootSuppressedPlanarCurves

/-! Genuine injective HALF-arc reparameterization. Path.truncate has constant
pieces and is unsuitable for faithful edge subdivision. These affine maps
cover the two halves exactly and meet only at the midpoint. -/
namespace G1InjectiveHalfArcSubdivision
open Set
variable {P : Type*} [TopologicalSpace P] {a b : P}

noncomputable def halfTime : unitInterval := ⟨(1:ℝ)/2,by norm_num,by norm_num⟩
noncomputable def leftTime (t : unitInterval) : unitInterval :=
  ⟨(t:ℝ)/2,by have h0 := t.property.1; have h1 := t.property.2; constructor <;> linarith⟩
noncomputable def rightTime (t : unitInterval) : unitInterval :=
  ⟨((t:ℝ)+1)/2,by have h0 := t.property.1; have h1 := t.property.2; constructor <;> linarith⟩

@[simp] theorem leftTime_zero : leftTime 0 = 0 := by apply Subtype.ext; norm_num [leftTime]
@[simp] theorem leftTime_one : leftTime 1 = halfTime := by apply Subtype.ext; norm_num [leftTime,halfTime]
@[simp] theorem rightTime_zero : rightTime 0 = halfTime := by apply Subtype.ext; norm_num [rightTime,halfTime]
@[simp] theorem rightTime_one : rightTime 1 = 1 := by apply Subtype.ext; norm_num [rightTime]

theorem halfTime_ne_zero : halfTime ≠ 0 := by intro h; have := congrArg Subtype.val h; norm_num [halfTime] at this
theorem halfTime_ne_one : halfTime ≠ 1 := by intro h; have := congrArg Subtype.val h; norm_num [halfTime] at this

noncomputable def leftHalf (γ : Path a b) : Path a (γ halfTime) where
  toFun t := γ (leftTime t)
  continuous_toFun := γ.continuous.comp (by unfold leftTime; fun_prop)
  source' := by simp
  target' := by simp
noncomputable def rightHalf (γ : Path a b) : Path (γ halfTime) b where
  toFun t := γ (rightTime t)
  continuous_toFun := γ.continuous.comp (by unfold rightTime; fun_prop)
  source' := by simp
  target' := by simp

theorem actual_left_half_injective (γ : Path a b) (hi : Function.Injective γ) :
    Function.Injective (leftHalf γ) := by
  intro t u he
  have h := congrArg Subtype.val (hi he)
  apply Subtype.ext
  change (t:ℝ)/2 = (u:ℝ)/2 at h
  linarith

theorem actual_right_half_injective (γ : Path a b) (hi : Function.Injective γ) :
    Function.Injective (rightHalf γ) := by
  intro t u he
  have h := congrArg Subtype.val (hi he)
  apply Subtype.ext
  change ((t:ℝ)+1)/2 = ((u:ℝ)+1)/2 at h
  linarith

theorem actual_half_arcs_meet_only_at_midpoint (γ : Path a b) (hi : Function.Injective γ)
    (t u : unitInterval) (he : leftHalf γ t = rightHalf γ u) :
    leftHalf γ t = γ halfTime := by
  have hv := congrArg Subtype.val (hi he)
  change (t:ℝ)/2 = ((u:ℝ)+1)/2 at hv
  have ht : t = 1 := Subtype.ext (by have ht0 := t.property.1; have ht1 := t.property.2; have hu0 := u.property.1; have hu1 := u.property.2; change (t:ℝ)=1; linarith)
  rw [ht,Path.target]

theorem actual_half_arcs_cover (γ : Path a b) : range (leftHalf γ) ∪ range (rightHalf γ) = range γ := by
  apply Subset.antisymm
  · rintro p (⟨t,ht⟩ | ⟨t,ht⟩)
    · exact ⟨leftTime t,ht⟩
    · exact ⟨rightTime t,ht⟩
  · rintro p ⟨t,ht⟩
    by_cases hh : (t:ℝ) ≤ 1/2
    · left
      let q : unitInterval := ⟨2*(t:ℝ),by have h0 := t.property.1; have h1 := t.property.2; constructor <;> linarith⟩
      refine ⟨q,?_⟩
      have hq : leftTime q = t := Subtype.ext (by dsimp [leftTime,q]; ring)
      change γ (leftTime q) = p
      rw [hq,ht]
    · right
      let q : unitInterval := ⟨2*(t:ℝ)-1,by have h0 := t.property.1; have h1 := t.property.2; constructor <;> linarith⟩
      refine ⟨q,?_⟩
      have hq : rightTime q = t := Subtype.ext (by dsimp [rightTime,q]; ring)
      change γ (rightTime q) = p
      rw [hq,ht]

#print axioms actual_half_arcs_cover
end G1InjectiveHalfArcSubdivision
