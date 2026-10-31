import Schoenflies.AccessibleJoin
import Schoenflies.ModelCurve
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Connected.LocallyConnected

/-! UNCOMPILED source draft. Uniform compact clearance supplies ACTUAL radial
access for the two fixed endpoints; accessibility is not an input assumption. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ClosedDiskNoncrossing
open Set Metric Schoenflies

private theorem scaled_square_interior {x : Plane} {t : ℝ}
    (hx : x∈Plane.closedSquare 0 1) (ht : 0≤t) (ht1 : t<1) :
    t • x ∈ Plane.openSquare 0 1 := by
  have hx' := mem_closedSquare_zero_one.mp hx
  apply mem_openSquare_zero_one.mpr
  change max |(t • x) 0| |(t • x) 1| < 1
  have h0 := (le_max_left |x 0| |x 1|).trans hx'
  have h1 := (le_max_right |x 0| |x 1|).trans hx'
  simp only [smul_coord,abs_mul,abs_of_nonneg ht]
  exact max_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_left h0 ht) (by simpa using ht1))
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 ht) (by simpa using ht1))

/-- A compact connected subset of the closed square can be replaced, only as
an auxiliary proof device, by a proper polygonal arc with the SAME two
specified endpoints, avoiding the ENTIRE disjoint compact obstacle. -/
theorem square_carrier_proper_arc
    {P K : Set Plane} {p q : Plane}
    (hP : IsCompact P) (hPc : IsPreconnected P) (hK : IsCompact K)
    (hPK : Disjoint P K) (hPsq : P ⊆ Plane.closedSquare 0 1)
    (hp : p∈P) (hq : q∈P) (hpq : p≠q) :
    ∃ A : Set Plane, IsPolygonal A ∧ IsArcBetween A p q ∧
      A \ {p,q} ⊆ Plane.openSquare 0 1 ∧ Disjoint A K := by
  obtain ⟨ρ,hρ,hsep⟩ := Plane.exists_dist_pos hP hK hPK
  obtain ⟨R,hR⟩ := hP.isBounded.exists_norm_le
  have hR0 : 0≤R := (norm_nonneg p).trans (hR p hp)
  have hRp : 0<R+1 := by linarith
  let δ : ℝ := min (1/2) (ρ/(2*(R+1)))
  have hδ : 0<δ := lt_min (by norm_num) (div_pos hρ (by positivity))
  have hδhalf : δ≤1/2 := min_le_left _ _
  have hδratio : δ≤ρ/(2*(R+1)) := min_le_right _ _
  have hδR : δ*(R+1)<ρ := by
    have h := (le_div_iff₀ (show 0<2*(R+1) by positivity)).mp hδratio
    nlinarith
  have hλ0 : ∀ t : ℝ, 1-δ≤t → 0≤t := by intro t ht; linarith
  have hclear : ∀ x∈P, ∀ t : ℝ, 1-δ≤t → t≤1 → t • x ∉ K := by
    intro x hx t ht ht1 hbad
    have hdist : dist (t • x) x < ρ := by
      calc
        dist (t • x) x = ‖(t-1) • x‖ := by
          rw [dist_eq_norm]
          congr 1
          rw [sub_smul,one_smul]
        _ = (1-t)*‖x‖ := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
          ring
        _ ≤ δ*(R+1) := mul_le_mul (by linarith) (by linarith [hR x hx])
          (norm_nonneg x) (le_of_lt hδ)
        _ < ρ := hδR
    exact (not_lt_of_ge (hsep x hx (t • x) hbad)) (by simpa [dist_comm] using hdist)
  let U : Set Plane := Plane.openSquare 0 1 \ K
  let f : Plane → Plane := fun x => (1-δ) • x
  have hf : Continuous f := continuous_const.smul continuous_id
  have hsub : f '' P ⊆ U := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨scaled_square_interior (hPsq hx) (hλ0 _ le_rfl) (by linarith),
      hclear x hx _ le_rfl (by linarith)⟩
  let Ω : Set Plane := connectedComponentIn U (f p)
  have hΩopen : IsOpen Ω := ((Plane.isOpen_openSquare 0 1).sdiff hK.isClosed).connectedComponentIn
  have hΩpre : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hPΩ : f '' P ⊆ Ω :=
    (hPc.image f hf.continuousOn).subset_connectedComponentIn (mem_image_of_mem f hp) hsub
  have haccess : ∀ x∈P, PolyAccessible Ω x := by
    intro x hx
    let T : Set Plane := (fun t : ℝ => t • x) '' Ico (1-δ) 1
    have hTpre : IsPreconnected T :=
      isPreconnected_Ico.image (fun t : ℝ => t • x) (continuous_id.smul continuous_const).continuousOn
    have hxT : f x ∈ T := ⟨1-δ,⟨le_rfl,by linarith⟩,rfl⟩
    have hTU : T ⊆ U := by
      rintro z ⟨t,ht,rfl⟩
      exact ⟨scaled_square_interior (hPsq hx) (hλ0 t ht.1) ht.2,
        hclear x hx t ht.1 ht.2.le⟩
    have hxΩ : f x ∈ Ω := hPΩ (mem_image_of_mem f hx)
    have hTΩ : T ⊆ Ω := by
      have hh := hTpre.subset_connectedComponentIn hxT hTU
      rw [connectedComponentIn_eq hxΩ] at hh
      exact hh
    apply PolyAccessible.of_openSegment hxΩ
    intro z hz
    rw [openSegment_eq_image] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    apply hTΩ
    refine ⟨1-t*δ,⟨?_,?_⟩,?_⟩
    · nlinarith [ht.2.le,hδ]
    · nlinarith [ht.1,hδ]
    · dsimp [f]
      rw [smul_smul,← add_smul]
      congr 1
      ring
  obtain ⟨A,hpoly,hA,hAΩ⟩ := exists_simple_arc_of_polyAccessible
    hΩopen hΩpre hpq (haccess p hp) (haccess q hq)
  have hΩU : Ω ⊆ U := connectedComponentIn_subset _ _
  refine ⟨A,hpoly,hA,fun z hz => (hΩU (hAΩ hz)).1,?_⟩
  apply Set.disjoint_left.mpr
  intro z hz hzk
  by_cases he : z∈({p,q}:Set Plane)
  · rcases he with rfl | rfl
    · exact Set.disjoint_left.mp hPK hp hzk
    · exact Set.disjoint_left.mp hPK hq hzk
  · exact (hΩU (hAΩ ⟨hz,he⟩)).2 hzk

#print axioms square_carrier_proper_arc
end Nanuq.ClosedDiskNoncrossing
