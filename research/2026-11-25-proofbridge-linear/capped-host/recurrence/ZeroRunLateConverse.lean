import ZeroRunTriangleConsumer
set_option warningAsError true

namespace AlexanderZeroRun
open AlexanderOmnibus ResearchCommons.TriangleRun ResearchCommons.TwoLiftTriangle

private theorem length_le_start (m j : Nat) : m ≤ slotStart m j := by
  have hb : m ≤ pairCode m j := by
    unfold pairCode
    omega
  have h : (pairCode m j+2)*1 ≤ (pairCode m j+2)*(pairCode m j+2) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [Nat.mul_one] at h
  unfold slotStart startIndex
  omega

private theorem reach_trans {E : Vertex → Vertex → Prop} {x y z : Vertex}
    (hxy : Reach E x y) (hyz : Reach E y z) : Reach E x z := by
  induction hyz with
  | here => exact hxy
  | next _ e ih => exact .next ih e

private theorem reach_reverse {E : Vertex → Vertex → Prop}
    (symm : ∀ x y, E x y → E y x) {x y : Vertex} (h : Reach E x y) :
    Reach E y x := by
  induction h with
  | here => exact .here
  | next _ e ih => exact reach_trans (.next .here (symm _ _ e)) ih

private theorem graph_triangle_symmetric (tw : Nat → Bool) (keep : Vertex → Prop)
    (u v : Vertex) (he : GraphTriangleEdge tw keep u v) : GraphTriangleEdge tw keep v u := by
  obtain ⟨ne,a,b,c,hab,hbc,hac,hu,hv,ka,kb,kc⟩ := he
  exact ⟨Ne.symm ne,a,b,c,hab,hbc,hac,hv,hu,ka,kb,kc⟩

/-- Every late representative incident to an actual triangle edge belongs to
one complete selected slot, even after deletion of any vertices below D. -/
theorem every_late_incident_component (A : Nat → Prop) (keep : Vertex → Prop) (D : Nat)
    (after : ∀ v, D < v.1 → keep v) (u v : Vertex) (late : 2*D+2 < u.1)
    (edge : GraphTriangleEdge (twist A) keep u v) :
    ∃ m j, A m ∧ D < slotStart m j ∧
      let lo := slotStart m j
      let vs := runVertices lo (lo+m) u.2
      vs.Nodup ∧ vs.length = m+3 ∧
        ∀ w, Reach (GraphTriangleEdge (twist A) keep) u w ↔ w ∈ vs := by
  obtain ⟨_,n,b,_,hz,hu,_,_,_,_⟩ := (at_iff_actual _ _ _ _).mpr edge
  obtain ⟨m,j,hm,hlo,hhi,_⟩ := every_zero_in_maximal_run A n hz
  let lo := slotStart m j
  have huhi := hu.2.2
  have hmlo := length_le_start m j
  have hloD : D < lo := by omega
  have huBand : InBand lo (lo+m+2) u.2 u :=
    ⟨rfl,Nat.le_trans hlo hu.2.1,by omega⟩
  have hs : u ∈ runVertices lo (lo+m) u.2 := (run_vertices_exact _ _ _ _).2 huBand
  obtain ⟨nd,sz,exactSlot⟩ := selected_slot_actual_component A hm j keep
    (fun w hw => after w (Nat.lt_of_lt_of_le hloD hw)) u.2
  have reachU := (exactSlot u).2 hs
  have revU := reach_reverse (graph_triangle_symmetric (twist A) keep) reachU
  refine ⟨m,j,hm,hloD,nd,sz,fun w => ?_⟩
  constructor
  · intro h
    exact (exactSlot w).1 (reach_trans reachU h)
  · intro h
    exact reach_trans revU ((exactSlot w).2 h)

#print axioms every_late_incident_component
end AlexanderZeroRun
