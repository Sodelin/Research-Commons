import CappedGridCross

namespace ResearchCommons.SeparateCrossCoordinates
open CappedGridCross

/-- At a given cut, a vertex need not be assigned a cell at all.
    It can certify a row only, a column only, or both. Coordinate uniqueness
    is required only for bag vertices and only for indices of this grid. -/
theorem width_from_incidence {V : Type} (n : Nat) (bag : List V)
    (row col : V → Nat → Prop)
    (rowUnique : ∀ v ∈ bag, ∀ i j, i < n → j < n → row v i → row v j → i = j)
    (colUnique : ∀ v ∈ bag, ∀ i j, i < n → j < n → col v i → col v j → i = j)
    (hits : ∀ i j, i < n → j < n → ∃ v ∈ bag, row v i ∨ col v j) :
    n ≤ bag.length := by
  classical
  let coord (incident : V → Nat → Prop) (v : V) : Nat :=
    if h : ∃ i, i < n ∧ incident v i then Classical.choose h else n
  have coord_of (incident : V → Nat → Prop)
      (unique : ∀ v ∈ bag, ∀ i j, i < n → j < n → incident v i → incident v j → i = j)
      (v : V) (hv : v ∈ bag) (i : Nat) (hi : i < n) (hinc : incident v i) :
      coord incident v = i := by
    have hex : ∃ j, j < n ∧ incident v j := ⟨i, hi, hinc⟩
    simpa only [coord, dif_pos hex] using
      unique v hv (Classical.choose hex) i
        (Classical.choose_spec hex).1 hi (Classical.choose_spec hex).2 hinc
  let point (v : V) := (coord row v, coord col v)
  have hitPoints : ∀ i j, i < n → j < n →
      ∃ p ∈ bag.map point, p.1 = i ∨ p.2 = j := by
    intro i j hi hj
    obtain ⟨v,hv,h⟩ := hits i j hi hj
    exact ⟨point v, List.mem_map.mpr ⟨v,hv,rfl⟩,
      h.elim (fun hr => Or.inl (coord_of row rowUnique v hv i hi hr))
        (fun hc => Or.inr (coord_of col colUnique v hv j hj hc))⟩
  simpa using crossHittingLowerBound n (bag.map point) hitPoints

/-- Logically, hitting all crosses means covering all rows or all columns. -/
theorem all_crosses_iff_one_side {V : Type} (n : Nat) (bag : List V)
    (row col : V → Nat → Prop) :
    (∀ i j, i < n → j < n → ∃ v ∈ bag, row v i ∨ col v j) ↔
      (∀ i, i < n → ∃ v ∈ bag, row v i) ∨
      (∀ j, j < n → ∃ v ∈ bag, col v j) := by
  classical
  constructor
  · intro h
    by_cases allRows : ∀ i, i < n → ∃ v ∈ bag, row v i
    · exact Or.inl allRows
    · right
      have missing : ∃ i, i < n ∧ ∀ v ∈ bag, ¬ row v i := by
        apply Classical.byContradiction
        intro hn
        apply allRows
        intro i hi
        apply Classical.byContradiction
        intro hnone
        exact hn ⟨i, hi, fun v hv hr => hnone ⟨v,hv,hr⟩⟩
      obtain ⟨i,hi,miss⟩  := missing
      intro j hj
      obtain ⟨v,hv,hits⟩ := h i j hi hj
      exact ⟨v,hv,hits.resolve_left (miss v hv)⟩
  · rintro (rows | cols) i j hi hj
    · obtain ⟨v,hv,hr⟩ := rows i hi
      exact ⟨v,hv,Or.inl hr⟩
    · obtain ⟨v,hv,hc⟩ := cols j hj
      exact ⟨v,hv,Or.inr hc⟩

/-- Separation on just one covered side suffices. The other side can
    overlap without restriction and does not enter the proof. -/
theorem width_from_one_separated_cover {V : Type} (n : Nat) (bag : List V)
    (inc : V → Nat → Prop)
    (unique : ∀ v ∈ bag, ∀ i j, i < n → j < n → inc v i → inc v j → i = j)
    (cover : ∀ i, i < n → ∃ v ∈ bag, inc v i) :
    n ≤ bag.length := by
  apply width_from_incidence n bag inc (fun _ _ => False) unique
  · intro _ _ _ _ _ _ h _
    exact h.elim
  · intro i j hi _
    obtain ⟨v,hv,hr⟩ := cover i hi
    exact ⟨v,hv,Or.inl hr⟩

/-- A single vertex in both rows hits all 2x2 crosses, despite bag width one. -/
theorem missing_row_separation_false_bound :
    (∀ i j : Nat, i < 2 → j < 2 →
      ∃ v ∈ ([()] : List Unit), (fun (_ : Unit) i => i < 2) v i ∨ False) ∧
      ¬ 2 ≤ ([()] : List Unit).length := by
  constructor
  · intro i j hi _
    exact ⟨(), by simp, Or.inl hi⟩
  · decide

#print axioms width_from_incidence
#print axioms all_crosses_iff_one_side
#print axioms width_from_one_separated_cover
#print axioms missing_row_separation_false_bound
end ResearchCommons.SeparateCrossCoordinates
