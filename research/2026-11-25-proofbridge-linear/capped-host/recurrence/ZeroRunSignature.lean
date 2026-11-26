import ZeroRunLateConverse
set_option warningAsError true

namespace AlexanderZeroRun
open ResearchCommons.TriangleRun ResearchCommons.TwoLiftTriangle

def HasComponentSize (E : Vertex → Vertex → Prop) (u : Vertex) (k : Nat) : Prop :=
  ∃ vs : List Vertex, vs.Nodup ∧ vs.length = k ∧ ∀ v, Reach E u v ↔ v ∈ vs

private theorem first_edge {E : Vertex → Vertex → Prop} {u w : Vertex}
    (rw : Reach E u w) (hne : w ≠ u) : ∃ v, E u v := by
  induction rw with
  | here => exact False.elim (hne rfl)
  | @next a b _ edge ih =>
    by_cases h : a = u
    · exact ⟨b,h ▸ edge⟩
    · exact ih h

private theorem incident_of_size {E : Vertex → Vertex → Prop} {u : Vertex} {k : Nat}
    (h : HasComponentSize E u k) (hk : 1 < k) : ∃ v, E u v := by
  classical
  obtain ⟨xs,nd,len,rw⟩ := h
  by_cases hx : ∃ w, w ∈ xs ∧ w ≠ u
  · obtain ⟨w,hw,hn⟩ := hx
    exact first_edge ((rw w).2 hw) hn
  · exfalso
    have hs : xs ⊆ [u] := by
      intro w hw
      have ht : w = u := Classical.byContradiction (fun hne => hx ⟨w,hw,hne⟩)
      exact List.mem_singleton.mpr ht
    have hlen := List.Nodup.length_le_of_subset nd hs
    simp only [List.length_cons, List.length_nil] at hlen
    omega

private theorem size_unique {E : Vertex → Vertex → Prop} {u : Vertex} {k l : Nat}
    (h1 : HasComponentSize E u k) (h2 : HasComponentSize E u l) : k = l := by
  obtain ⟨xs,nx,lx,rx⟩ := h1
  obtain ⟨ys,ny,ly,ry⟩ := h2
  have a : xs ⊆ ys := fun v h => (ry v).1 ((rx v).2 h)
  have b : ys ⊆ xs := fun v h => (rx v).1 ((ry v).2 h)
  have h₁ := List.Nodup.length_le_of_subset nx a
  have h₂ := List.Nodup.length_le_of_subset ny b
  omega

/-- The exact selected-size signature persists after arbitrary deletions
bounded in level. Component sizes m+3 exclude isolated vertices. -/
theorem late_component_size_iff (A : Nat → Prop) (keep : Vertex → Prop) (D m : Nat)
    (after : ∀ v, D < v.1 → keep v) :
    (∀ bound, ∃ u : Vertex, bound ≤ u.1 ∧
      HasComponentSize (GraphTriangleEdge (twist A) keep) u (m+3)) ↔ A m := by
  constructor
  · intro h
    obtain ⟨u,hl,hs⟩ := h (2*D+3)
    obtain ⟨v,e⟩ := incident_of_size hs (by omega)
    obtain ⟨p,j,hp,_,nd,sz,spec⟩ :=
      every_late_incident_component A keep D after u v (by omega) e
    have hp' : HasComponentSize (GraphTriangleEdge (twist A) keep) u (p+3) :=
      ⟨runVertices (slotStart p j) (slotStart p j+p) u.2,nd,sz,spec⟩
    have eq : p = m := by have := size_unique hp' hs; omega
    exact eq ▸ hp
  · intro hm bound
    obtain ⟨lo,hl,hc⟩ := arbitrarily_late_exact_components A hm keep (D+1) bound
      (fun v h => after v (by omega))
    obtain ⟨nd,sz,spec⟩ := hc false
    exact ⟨(lo,false), Nat.le_trans (Nat.le_max_right _ _) hl,
      ⟨runVertices lo (lo+m) false,nd,sz,spec⟩⟩

#print axioms late_component_size_iff
end AlexanderZeroRun
