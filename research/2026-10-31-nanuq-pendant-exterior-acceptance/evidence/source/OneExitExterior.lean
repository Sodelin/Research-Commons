import OneExit
import Schoenflies.JordanClosed

/-! UNCOMPILED one-exit component association. Qualified arc-complement
connectedness and the supplier's exact first-meeting theorem are reused.
No relative slit-domain connectedness or finite-intersection premise. -/
namespace Nanuq.Pendant
open Set Schoenflies unitInterval

/-- Any point inside the one-exit disk and off the complete trace reaches
its punctured boundary in the COMPLETE trace complement. -/
theorem one_exit_boundary_component {K A C : Set Plane} {q z u : Plane}
    (hC : IsJordanCurve C) (hA : IsArc A)
    (hinter : C ∩ K = {q}) (hclosed : (C ∪ inside C) ∩ K = A)
    (hz : z ∈ inside C) (hzK : z∉K) (hu : u∈C\K) :
    C\{q} ⊆ connectedComponentIn Kᶜ z := by
  have hAK : A ⊆ K := by
    intro x hx
    have hx' : x∈(C ∪ inside C) ∩ K := hclosed.symm ▸ hx
    exact hx'.2
  have hq : q∈C ∩ K := hinter.symm ▸ (show q∈({q}:Set Plane) from rfl)
  have hqu : q≠u := fun heq => hu.2 (heq ▸ hq.2)
  have hCK : C\{q} ⊆ Kᶜ := by
    intro x hx hxK
    have heq : x=q := by
      have hm : x∈({q}:Set Plane) := hinter ▸ (show x∈C∩K from ⟨hx.1,hxK⟩)
      exact hm
    exact hx.2 heq
  obtain ⟨vs,hvs,hPA,hstart,hfinish⟩ :=
    exists_poly_of_isPreconnected hA.isClosed.isOpen_compl (arc_complement hA).isPreconnected
      (show z∈Aᶜ from fun ha => hzK (hAK ha))
      (show u∈Aᶜ from fun ha => hu.2 (hAK ha))
  cases vs with
  | nil => exact False.elim (hvs rfl)
  | cons z' vs =>
    simp only [List.head_cons] at hstart
    subst z'
    have hmeet : (poly (z::vs) ∩ C).Nonempty := by
      refine ⟨u,?_,hu.1⟩
      rw [← hfinish]
      exact getLast_mem_poly (List.cons_ne_nil z vs)
    obtain ⟨w,hw,Q,_,hQ,hQP,hbefore⟩ := exists_arc_to_first_meeting (U := Cᶜ)
      hC.isClosed (Set.disjoint_left.mpr (fun _ hx hy => hx hy)) hz.1
      (show poly (z::vs) ⊆ Cᶜ ∪ C from fun x _ => by
        by_cases hx : x∈C
        · exact Or.inr hx
        · exact Or.inl hx) hmeet
    have hQA : Q ⊆ Aᶜ := hQP.trans hPA
    have hQK : Q ⊆ Kᶜ := by
      intro x hx hxK
      have hxclosed : x∈C ∪ inside C := by
        by_cases hxw : x=w
        · exact Or.inl (hxw.symm ▸ hw.2)
        · exact Or.inr (connectedComponentIn_subset_inside hz
            (hbefore ⟨hx,by simpa using hxw⟩))
      exact hQA hx (hclosed ▸ (show x∈(C ∪ inside C)∩K from ⟨hxclosed,hxK⟩))
    have hwcomp : w ∈ connectedComponentIn Kᶜ z :=
      hQ.isArc.isConnected.isPreconnected.subset_connectedComponentIn hQ.right_mem hQK hQ.left_mem
    have hwC : w∈C\{q} := ⟨hw.2,fun heq => hQK hQ.left_mem (heq.symm ▸ hq.2)⟩
    have hsub := (punctured_jordan_preconnected hC hq.1 hu.1 hqu).subset_connectedComponentIn hwC hCK
    rwa [← connectedComponentIn_eq hwcomp] at hsub

/-- The specified original component, not an arbitrarily selected face.
Closure at an interior leaf supplies the starting point automatically. -/
theorem one_exit_specified_component {K A C : Set Plane} {q p o u : Plane}
    (hC : IsJordanCurve C) (hA : IsArc A)
    (hinter : C∩K={q}) (hclosed : (C ∪ inside C)∩K=A)
    (hp : p∈inside C) (hpcl : p∈closure (connectedComponentIn Kᶜ o))
    (hu : u∈C\K) :
    C\{q} ⊆ connectedComponentIn Kᶜ o := by
  obtain ⟨z,hz,hzF⟩ := (mem_closure_iff.mp hpcl) (inside C) (isOpen_inside hC.isClosed) hp
  have hzK : z∉K := connectedComponentIn_subset _ _ hzF
  have hsub := one_exit_boundary_component hC hA hinter hclosed hz hzK hu
  rwa [← connectedComponentIn_eq hzF] at hsub

#print axioms one_exit_boundary_component
#print axioms one_exit_specified_component
end Nanuq.Pendant
