import FixedGender

namespace ResearchCommons.FixedColorExact
open CappedLabeledGrid FixedGender

private theorem east_source_unique {n : Nat} {a b c : Cell n}
    (ha : east a c) (hb : east b c) : a = b :=
  Prod.ext (ha.1.trans hb.1.symm) (Fin.ext (by have x := ha.2; have y := hb.2; omega))

private theorem north_source_unique {n : Nat} {a b c : Cell n}
    (ha : north a c) (hb : north b c) : a = b :=
  Prod.ext (Fin.ext (by have x := ha.1; have y := hb.1; omega)) (ha.2.trans hb.2.symm)

private theorem east_north_colors_ne {n k : Nat} {a b c : Cell n}
    (ha : east a c) (hb : north b c) :
    gender (.inr a : Vertex n k) ≠ gender (.inr b : Vertex n k) := by
  intro h
  have e := congrArg Fin.val ha.1
  have north := hb.1
  change a.1.val % 2 = b.1.val % 2 at h
  omega

private theorem source_missing_imp {n k : Nat} {o : Cell n} {g : Fin k}
    {b : Cell n} {l : Nat}
    (h : fixedEdge (.inl (o,g)) (.inr b) = some l) :
    o = b ∧ g.val = l ∧ unserved b l := by
  by_cases h' : o = b ∧ unserved b g.val
  · have h'' : g.val = l := by simpa [fixedEdge,h'] using h
    exact ⟨h'.1,h'',h'' ▸ h'.2⟩
  · simp [fixedEdge,h'] at h

private theorem missing_not_cell {n k : Nat} {a b : Cell n} {l : Nat}
    (missing : unserved b l) (h : @fixedEdge n k (.inr a) (.inr b) = some l) :
    False := by
  have label := fixedLabel (.inr a : Vertex n k) (.inr b) l h
  change a.1.val % 2 = l at label
  by_cases hb : east a b ∨ north a b
  · rcases hb with e | q
    · have same := congrArg Fin.val e.1
      exact missing.1 ⟨by have z := e.2; omega, by omega⟩
    · exact missing.2 ⟨by have z := q.1; omega, by have z := q.1; omega⟩
  · simp [fixedEdge,hb] at h

theorem source_per_color_unique {n k : Nat} (b : Cell n) (l : Nat)
    (u v : Vertex n k) (hu : fixedEdge u (.inr b) = some l)
    (hv : fixedEdge v (.inr b) = some l) : u = v := by
  rcases u with ⟨u,g⟩ | u <;> rcases v with ⟨v,h⟩ | v
  · obtain ⟨r,e,_⟩ := source_missing_imp hu
    obtain ⟨s,f,_⟩ := source_missing_imp hv
    exact congrArg Sum.inl (Prod.ext (r.trans s.symm) (Fin.ext (e.trans f.symm)))
  · exact (missing_not_cell (source_missing_imp hu).2.2 hv).elim
  · exact (missing_not_cell (source_missing_imp hv).2.2 hu).elim
  · have hu' : east u b ∨ north u b := by
      by_cases hh : east u b ∨ north u b
      · exact hh
      · simp [fixedEdge,hh] at hu
    have hv' : east v b ∨ north v b := by
      by_cases hh : east v b ∨ north v b
      · exact hh
      · simp [fixedEdge,hh] at hv
    have hcolor := (fixedLabel _ _ _ hu).trans (fixedLabel _ _ _ hv).symm
    rcases hu' with ue | un <;> rcases hv' with ve | vn
    · exact congrArg Sum.inr (east_source_unique ue ve)
    · exact (east_north_colors_ne ue vn hcolor).elim
    · exact (east_north_colors_ne ve un hcolor.symm).elim
    · exact congrArg Sum.inr (north_source_unique un vn)

theorem exact_incoming_per_color {n k : Nat} (b : Cell n) (l : Fin k) :
    ∃ u : Vertex n k, fixedEdge u (.inr b) = some l.val ∧
      ∀ v : Vertex n k, fixedEdge v (.inr b) = some l.val → v = u := by
  obtain ⟨u,hu⟩ := everyLabel b l
  exact ⟨u,hu,fun v hv => source_per_color_unique b l.val v u hv hu⟩

#print axioms exact_incoming_per_color
end ResearchCommons.FixedColorExact
