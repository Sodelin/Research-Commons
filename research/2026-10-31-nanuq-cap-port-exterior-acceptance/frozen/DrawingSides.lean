import G1OuterLabelledMultigraphCurves
import Mathlib.Topology.Connected.Basic

/-! WORKING, UNCOMPILED. Original-ID vertex-side traces for the actual cap
exterior proof. No order, local-radius, or face assumption. -/
namespace Nanuq.CapExterior
open Nanuq.Source G1OuterLabelledMultigraphCurves Set
variable {V E : Type*} {G : EdgeGraph V E} (D : PlanarCurves G)

/-- The literal trace induced by a vertex set, keeping each original edge ID. -/
def sideTrace (S : Set V) : Set Plane :=
  D.point '' S ∪ {z | ∃ e, G.source e ∈ S ∧ G.target e ∈ S ∧ z ∈ range (D.arc e)}

lemma point_mem_sideTrace_iff (S : Set V) (v : V) :
    D.point v ∈ sideTrace D S ↔ v ∈ S := by
  constructor
  · rintro (⟨w,hw,he⟩ | ⟨e,hs,ht,t,he⟩)
    · exact D.point_injective he ▸ hw
    · rcases D.vertex_incidence e v t he with hv | hv
      · exact hv.symm ▸ hs
      · exact hv.symm ▸ ht
  · intro hv
    exact Or.inl ⟨v,hv,rfl⟩

lemma arc_meets_sideTrace_endpoint (S : Set V) (e : E)
    (he : ¬ (G.source e ∈ S ∧ G.target e ∈ S)) (t : unitInterval)
    (hz : D.arc e t ∈ sideTrace D S) :
    (t = 0 ∧ G.source e ∈ S) ∨ (t = 1 ∧ G.target e ∈ S) := by
  have hend : t = 0 ∨ t = 1 := by
    rcases hz with ⟨v,hv,hpv⟩ | ⟨f,hfs,hft,u,hfu⟩
    · rcases D.vertex_incidence e v t hpv.symm with hs | ht
      · left
        apply D.arc_injective e
        exact hpv.symm.trans ((congrArg D.point hs).trans (D.arc e).source.symm)
      · right
        apply D.arc_injective e
        exact hpv.symm.trans ((congrArg D.point ht).trans (D.arc e).target.symm)
    · by_cases hef : e = f
      · subst f
        exact False.elim (he ⟨hfs,hft⟩)
      · exact (D.edge_incidence e f hef t u hfu.symm).1
  rcases hend with rfl | rfl
  · exact Or.inl ⟨rfl,(point_mem_sideTrace_iff D S _).mp (by simpa using hz)⟩
  · exact Or.inr ⟨rfl,(point_mem_sideTrace_iff D S _).mp (by simpa using hz)⟩

lemma sideTrace_disjoint {S T : Set V} (hst : Disjoint S T) :
    Disjoint (sideTrace D S) (sideTrace D T) := by
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  rcases hzS with ⟨v,hv,rfl⟩ | ⟨e,hs,ht,t,rfl⟩
  · exact Set.disjoint_left.mp hst hv ((point_mem_sideTrace_iff D T v).mp hzT)
  · have hns : G.source e ∉ T := fun h => Set.disjoint_left.mp hst hs h
    rcases arc_meets_sideTrace_endpoint D T e (fun h => hns h.1) t hzT with h | h
    · exact hns h.2
    · exact Set.disjoint_left.mp hst ht h.2

lemma arc_range_subset_sideTrace {S : Set V} (e : E)
    (hs : G.source e ∈ S) (ht : G.target e ∈ S) :
    range (D.arc e) ⊆ sideTrace D S :=
  fun _ hz => Or.inr ⟨e,hs,ht,hz⟩

lemma point_same_component_of_original_walk {U : Set Plane} {keep : E → Prop}
    (hrange : ∀ e, keep e → range (D.arc e) ⊆ U) {a b : V}
    (ha : D.point a ∈ U) (hw : G.UReach keep a b) :
    D.point b ∈ connectedComponentIn U (D.point a) := by
  induction hw with
  | refl => exact mem_connectedComponentIn ha
  | @tail b c _ step ih =>
    obtain ⟨e,hkeep,hinc⟩ := step
    have hb : D.point b ∈ range (D.arc e) := by
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · rw [← hs]
        exact ⟨0,(D.arc e).source⟩
      · rw [← ht]
        exact ⟨1,(D.arc e).target⟩
    have hc : D.point c ∈ range (D.arc e) := by
      rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
      · rw [← ht]
        exact ⟨1,(D.arc e).target⟩
      · rw [← hs]
        exact ⟨0,(D.arc e).source⟩
    have hcU := (isPreconnected_range (D.arc e).continuous).subset_connectedComponentIn
      hb (hrange e hkeep) hc
    rw [connectedComponentIn_eq ih]
    exact hcU

end Nanuq.CapExterior
