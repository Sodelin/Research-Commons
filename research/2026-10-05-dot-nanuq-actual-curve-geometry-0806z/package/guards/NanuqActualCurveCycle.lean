import guards.NanuqActualCurveOpening
import Mathlib.Topology.Instances.AddCircle.Defs

set_option debug.skipKernelTC false

/-! Cycle parameterization infrastructure for the actual edge-indexed curve
carrier. Intersections are stated on physical arc images. No Jordan or cyclic
order assertion is postulated. -/
namespace Nanuq.Source.EdgeGraph.CurveDrawing
open Set
variable {P : Type*} [TopologicalSpace P]

theorem trans_injective_of_only_joint {a b c : P} (p : Path a b) (q : Path b c)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hjoint : ∀ t u, p t = q u → t = 1 ∧ u = 0) :
    Function.Injective (p.trans q) := by
  intro t u h
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with ht hu hu
  · have he := hp h
    have he := congrArg (fun z : unitInterval => (z:ℝ)) he
    apply Subtype.ext
    dsimp at he
    linarith
  · obtain ⟨he,hf⟩ := hjoint _ _ h
    have he := congrArg (fun z : unitInterval => (z:ℝ)) he
    have hf := congrArg (fun z : unitInterval => (z:ℝ)) hf
    apply Subtype.ext
    dsimp at he hf
    linarith
  · obtain ⟨he,hf⟩ := hjoint _ _ h.symm
    have he := congrArg (fun z : unitInterval => (z:ℝ)) he
    have hf := congrArg (fun z : unitInterval => (z:ℝ)) hf
    apply Subtype.ext
    dsimp at he hf
    linarith
  · have he := hq h
    have he := congrArg (fun z : unitInterval => (z:ℝ)) he
    apply Subtype.ext
    dsimp at he
    linarith

/-- A path made from two simple arms with the same endpoints is injective
except for its intentional endpoint identification. This covers parallel
edge bigons as well as cycles whose arms contain many edges. -/
theorem two_arm_loop_eq {a b : P} (p q : Path a b)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hjoint : ∀ t u, p t = q u → (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1))
    (t u : unitInterval) (h : (p.trans q.symm) t = (p.trans q.symm) u) :
    t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with ht hu hu
  · left
    have he := congrArg (fun z : unitInterval => (z:ℝ)) (hp h)
    apply Subtype.ext;dsimp at he;linarith
  · rw [Path.symm_apply] at h
    rcases hjoint _ _ h with ⟨he,hf⟩ | ⟨he,hf⟩
    · right;left
      have he := congrArg (fun z : unitInterval => (z:ℝ)) he
      have hf := congrArg (fun z : unitInterval => (z:ℝ)) hf
      constructor <;> apply Subtype.ext <;> dsimp at * <;> linarith
    · left
      have he := congrArg (fun z : unitInterval => (z:ℝ)) he
      have hf := congrArg (fun z : unitInterval => (z:ℝ)) hf
      apply Subtype.ext;dsimp at *;linarith
  · rw [Path.symm_apply] at h
    rcases hjoint _ _ h.symm with ⟨he,hf⟩ | ⟨he,hf⟩
    · right;right
      have he := congrArg (fun z : unitInterval => (z:ℝ)) he
      have hf := congrArg (fun z : unitInterval => (z:ℝ)) hf
      constructor <;> apply Subtype.ext <;> dsimp at * <;> linarith
    · left
      have he := congrArg (fun z : unitInterval => (z:ℝ)) he
      have hf := congrArg (fun z : unitInterval => (z:ℝ)) hf
      apply Subtype.ext;dsimp at *;linarith
  · left
    rw [Path.symm_apply,Path.symm_apply] at h
    have he := congrArg (fun z : unitInterval => (z:ℝ)) (hq h)
    apply Subtype.ext;dsimp at *;linarith
noncomputable def twoArmCircle {a b : P} (p q : Path a b) : AddCircle (1:ℝ) → P :=
  AddCircle.liftIco 1 0 (p.trans q.symm).extend

theorem twoArmCircle_continuous {a b : P} (p q : Path a b) :
    Continuous (twoArmCircle p q) := by
  apply AddCircle.liftIco_zero_continuous
  · simp
  · exact (p.trans q.symm).continuous_extend.continuousOn

theorem twoArmCircle_injective {a b : P} (p q : Path a b)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hjoint : ∀ t u, p t = q u → (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1)) :
    Function.Injective (twoArmCircle p q) := by
  intro x y h
  obtain ⟨t,ht,rfl⟩ := by
    simpa only [Set.mem_image] using AddCircle.coe_image_Ico_eq (1:ℝ) 0 ▸ Set.mem_univ x
  obtain ⟨u,hu,rfl⟩ := by
    simpa only [Set.mem_image] using AddCircle.coe_image_Ico_eq (1:ℝ) 0 ▸ Set.mem_univ y
  have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1,by simpa using ht.2.le⟩
  have hu' : u ∈ Set.Icc (0:ℝ) 1 := ⟨hu.1,by simpa using hu.2.le⟩
  change AddCircle.liftIco 1 0 (p.trans q.symm).extend (t:AddCircle (1:ℝ)) =
    AddCircle.liftIco 1 0 (p.trans q.symm).extend (u:AddCircle (1:ℝ)) at h
  rw [AddCircle.liftIco_coe_apply ht,AddCircle.liftIco_coe_apply hu,
    Path.extend_apply _ ht',Path.extend_apply _ hu'] at h
  rcases two_arm_loop_eq p q hp hq hjoint ⟨t,ht'⟩ ⟨u,hu'⟩ h with he | ⟨_,he⟩ | ⟨he,_⟩
  · exact congrArg (fun z : ℝ => (z:AddCircle (1:ℝ))) (congrArg Subtype.val he)
  · have he := congrArg (fun z : unitInterval => (z:ℝ)) he
    have hu1 : u < 1 := by simpa using hu.2
    dsimp at he
    exact False.elim (hu1.ne he)
  · have he := congrArg (fun z : unitInterval => (z:ℝ)) he
    have ht1 : t < 1 := by simpa using ht.2
    dsimp at he
    exact False.elim (ht1.ne he)

theorem twoArmCircle_range {a b : P} (p q : Path a b) :
    Set.range (twoArmCircle p q) = Set.range p ∪ Set.range q := by
  rw [← Path.symm_range q,← Path.trans_range p q.symm]
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨t,ht,rfl⟩ := by
      simpa only [Set.mem_image] using AddCircle.coe_image_Ico_eq (1:ℝ) 0 ▸ Set.mem_univ x
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1,by simpa using ht.2.le⟩
    refine ⟨⟨t,ht'⟩,?_⟩
    change (p.trans q.symm) _ = AddCircle.liftIco 1 0 (p.trans q.symm).extend _
    rw [AddCircle.liftIco_coe_apply ht,Path.extend_apply _ ht']
  · rintro ⟨t,rfl⟩
    by_cases ht : (t:ℝ) < 1
    · refine ⟨((t:ℝ):AddCircle (1:ℝ)),?_⟩
      change AddCircle.liftIco 1 0 (p.trans q.symm).extend _ = _
      rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1,ht⟩,Path.extend_apply _ t.property]
    · have he : t = 1 := Subtype.ext (le_antisymm t.property.2 (not_lt.mp ht))
      subst t
      refine ⟨(0:AddCircle (1:ℝ)),?_⟩
      change AddCircle.liftIco 1 0 (p.trans q.symm).extend ((0:ℝ):AddCircle (1:ℝ)) = _
      rw [AddCircle.liftIco_zero_coe_apply (by constructor <;> norm_num)]
      simp

section ActualParallelArcs
variable {V E : Type*} {G : EdgeGraph V E} (D : CurveDrawing (P := P) G)

theorem parallel_arc_joint (e f : E) (hne : e ≠ f)
    (hs : G.source e = G.source f) (ht : G.target e = G.target f)
    (t u : unitInterval) (h : D.arc e t = D.arc f u) :
    (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1) := by
  obtain ⟨he,hf⟩ := D.edge_incidence e f hne t u h
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · exact Or.inl ⟨rfl,rfl⟩
  · have heq : D.arc e 0 = D.arc e 1 := by simpa [ht] using h
    have bad := D.arc_injective e heq
    have bad := congrArg (fun z : unitInterval => (z:ℝ)) bad
    norm_num at bad
  · have heq : D.arc e 1 = D.arc e 0 := by simpa [hs] using h
    have bad := D.arc_injective e heq
    have bad := congrArg (fun z : unitInterval => (z:ℝ)) bad
    norm_num at bad
  · exact Or.inr ⟨rfl,rfl⟩

/-- Two distinct actual parallel edge occurrences produce a genuine embedded
circle with precisely their physical union as image. Parallel incidences are
not collapsed to one edge. -/
theorem actual_parallel_edges_circle (e f : E) (hne : e ≠ f)
    (hs : G.source e = G.source f) (ht : G.target e = G.target f) :
    ∃ r : AddCircle (1:ℝ) → P, Continuous r ∧ Function.Injective r ∧
      Set.range r = Set.range (D.arc e) ∪ Set.range (D.arc f) := by
  let q : Path (D.point (G.source e)) (D.point (G.target e)) :=
    (D.arc f).cast (congrArg D.point hs) (congrArg D.point ht)
  refine ⟨twoArmCircle (D.arc e) q,twoArmCircle_continuous _ _,?_,?_⟩
  · exact twoArmCircle_injective _ _ (D.arc_injective e) (D.arc_injective f)
      (D.parallel_arc_joint e f hne hs ht)
  · exact twoArmCircle_range _ _
end ActualParallelArcs

end Nanuq.Source.EdgeGraph.CurveDrawing
