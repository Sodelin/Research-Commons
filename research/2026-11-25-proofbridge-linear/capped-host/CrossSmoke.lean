import CappedGridCross

open ResearchCommons.CappedGridCross

/-- One selected point cannot hit every cross of a 2 by 2 grid. -/
theorem onePointFails :
    ¬ (∀ i j, i < 2 → j < 2 →
       ∃ p ∈ [(0, 0)], p.1 = i ∨ p.2 = j) := by
  intro hit
  have h := crossHittingLowerBound 2 [(0, 0)] hit
  simp at h

/-- The verified lower bound is attained for a concrete 2 by 2 grid. -/
theorem twoPointsSuffice :
    ∀ i j, i < 2 → j < 2 →
      ∃ p ∈ [(0, 0), (1, 0)], p.1 = i ∨ p.2 = j := by
  intro i j hi hj
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · exact ⟨(0,0), by simp, Or.inl rfl⟩
  · exact ⟨(1,0), by simp, Or.inl rfl⟩

#print axioms onePointFails
#print axioms twoPointsSuffice
