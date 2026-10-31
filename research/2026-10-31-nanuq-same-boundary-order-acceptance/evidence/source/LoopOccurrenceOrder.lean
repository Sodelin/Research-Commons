import ActualSharedBoundary
import Schoenflies.TwoArcs
import Mathlib.Data.Finset.Sort

/-! UNCOMPILED. Derive a finite occurrence order from the SAME Jordan loop;
no arbitrary circular order or adjacency certificate is an input. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.BoundaryOrder
open Set Schoenflies
open scoped Classical

/-- Unique before-finish parameters and a sorted finite occurrence list. -/
theorem finite_occurrence_parameters {T : Type*} [Fintype T]
    {C : Set Plane} (hC : IsJordanCurve C) (point : T → Plane)
    (hinj : Function.Injective point) (hmem : ∀ t, point t∈C) :
    ∃ (f : ℝ → Plane) (θ : T → ℝ) (xs : List T),
      IsLoop f ∧ f '' unitInterval=C ∧
      (∀ t, θ t∈Ico (0:ℝ) 1 ∧ f (θ t)=point t) ∧
      Function.Injective θ ∧ xs.Nodup ∧ (∀ t, t∈xs) ∧
      xs.Pairwise (fun a c => θ a≤θ c) := by
  classical
  obtain ⟨f,hf,himage⟩ := hC
  have hp : ∀ t, ∃ s∈unitInterval, s≠1 ∧ f s=point t := by
    intro t
    exact hf.parameter_before_finish (himage.symm ▸ hmem t)
  choose θ hθ hθ1 hpoint using hp
  have hθinj : Function.Injective θ := by
    intro a c hac
    apply hinj
    rw [← hpoint a,← hpoint c,hac]
  let r : T → T → Prop := fun a c => θ a≤θ c
  letI : IsTrans T r := ⟨fun a c d hac hcd => le_trans hac hcd⟩
  letI : Std.Antisymm r := ⟨fun a c hac hca => hθinj (le_antisymm hac hca)⟩
  letI : Std.Total r := ⟨fun a c => le_total (θ a) (θ c)⟩
  let xs := Finset.univ.sort r
  refine ⟨f,θ,xs,hf,himage,?_,hθinj,Finset.sort_nodup _ _,?_,Finset.pairwise_sort _ _⟩
  · intro t
    exact ⟨⟨(hθ t).1,lt_of_le_of_ne (hθ t).2 (hθ1 t)⟩,hpoint t⟩
  · intro t
    exact (Finset.mem_sort r).mpr (Finset.mem_univ t)

/-- Explicit interval pieces of the selected loop, including its wraparound seam. -/
theorem parameter_cut_pair {f : ℝ → Plane} (hf : IsLoop f)
    {s t : ℝ} (hs : s∈Ico (0:ℝ) 1) (ht : t∈Ico (0:ℝ) 1) (hst : s<t) :
    IsCutPair (f '' unitInterval) (f s) (f t)
      (f '' Icc s t) (f '' Icc 0 s ∪ f '' Icc t 1) := by
  have hsI : s∈unitInterval := ⟨hs.1,hs.2.le⟩
  have htI : t∈unitInterval := ⟨ht.1,ht.2.le⟩
  exact ⟨hf.middle_IsArcBetween hsI htI (ne_of_lt ht.2) hst,
    (hf.outside_IsArcBetween hsI htI (ne_of_lt hs.2) (ne_of_lt ht.2) hst).reverse,
    IsLoop.pieces_cover hsI htI,
    hf.pieces_meet_at_ends hsI htI (ne_of_lt hs.2) (ne_of_lt ht.2) hst⟩

/-- A connected boundary subset cannot cross between cut arcs while avoiding
both cut points. This needs no planar collar or subarc-uniqueness theorem. -/
theorem connected_boundary_cut_false {C B A₁ A₂ : Set Plane} {p q x y : Plane}
    (hcut : IsCutPair C p q A₁ A₂) (hB : IsPreconnected B) (hBC : B⊆C)
    (hp : p∉B) (hq : q∉B) (hx : x∈B) (hy : y∈B)
    (hxA : x∈A₁) (hyA : y∈A₂) : False := by
  obtain ⟨z,hzB,hzA⟩ := isPreconnected_closed_iff.mp hB A₁ A₂
    hcut.fst.isArc.isClosed hcut.snd.isArc.isClosed
    (hcut.union_eq.symm ▸ hBC) ⟨x,hx,hxA⟩ ⟨y,hy,hyA⟩
  have hz : z=p ∨ z=q := by
    have hzEnds : z ∈ ({p, q} : Set Plane) := by
      rw [← hcut.inter_eq]
      exact hzA
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzEnds
  rcases hz with rfl | rfl
  · exact hp hzB
  · exact hq hzB

/-- Empty same-boundary pair arc gives an empty linear gap OR empty wrap gap
in the actual loop parameters. Every other occurrence is quantified. -/
theorem empty_pair_arc_parameter_gap {T : Type*}
    {f : ℝ → Plane} (hf : IsLoop f) (θ : T → ℝ)
    (hθ : ∀ t, θ t∈Ico (0:ℝ) 1)
    {a c : T} (hac : θ a<θ c) {B : Set Plane}
    (hB : IsArcBetween B (f (θ a)) (f (θ c)))
    (hBC : B⊆f '' unitInterval)
    (honly : ∀ w, f (θ w)∈B ↔ w=a ∨ w=c) :
    (∀ w, ¬(θ a<θ w ∧ θ w<θ c)) ∨
      (∀ w, ¬(θ w<θ a ∨ θ c<θ w)) := by
  classical
  by_cases hgap : ∀ w, ¬(θ a<θ w ∧ θ w<θ c)
  · exact Or.inl hgap
  · right
    push_neg at hgap
    obtain ⟨x,hax,hxc⟩ := hgap
    have hxB : f (θ x)∉B := by
      intro hx
      rcases (honly x).mp hx with h | h <;> subst x <;> linarith
    intro y hy
    have hyB : f (θ y)∉B := by
      intro h
      rcases (honly y).mp h with h | h <;> subst y <;> rcases hy with hy | hy <;> linarith
    rcases hy with hya | hcy
    · have hcut := parameter_cut_pair hf (hθ y) (hθ x) (by linarith)
      exact connected_boundary_cut_false hcut hB.isArc.isConnected.isPreconnected hBC
        hyB hxB hB.left_mem hB.right_mem
        ⟨θ a,⟨hya.le,hax.le⟩,rfl⟩
        (Or.inr ⟨θ c,⟨hxc.le,(hθ c).2.le⟩,rfl⟩)
    · have hcut := parameter_cut_pair hf (hθ x) (hθ y) (by linarith)
      exact connected_boundary_cut_false hcut hB.isArc.isConnected.isPreconnected hBC
        hxB hyB hB.right_mem hB.left_mem
        ⟨θ c,⟨hxc.le,hcy.le⟩,rfl⟩
        (Or.inl ⟨θ a,⟨(hθ a).1,hax.le⟩,rfl⟩)

#print axioms finite_occurrence_parameters
#print axioms empty_pair_arc_parameter_gap
end Nanuq.BoundaryOrder
