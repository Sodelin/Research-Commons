import Lean

namespace ResearchCommons.CappedGridCross

private theorem missingBelow (n : Nat) (xs : List Nat) (h : xs.length < n) :
    ∃ i, i < n ∧ i ∉ xs := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    by_cases hn : n ∈ xs
    · have hpos : 0 < xs.length := by
        cases xs with
        | nil => simp at hn
        | cons _ _ => simp
      have hlen := List.length_erase_of_mem hn
      have hlt : (xs.erase n).length < n := by omega
      obtain ⟨i, hi, hm⟩ := ih (xs.erase n) hlt
      refine ⟨i, by omega, ?_⟩
      intro hmem
      have hne : i ≠ n := by omega
      exact hm ((List.mem_erase_of_ne hne).2 hmem)
    · exact ⟨n, by omega, hn⟩

/-- Each cross is the union of one row and one column. Even a list
with duplicate or off-grid points needs at least n entries to hit all crosses. -/
theorem crossHittingLowerBound (n : Nat) (xs : List (Nat × Nat))
    (hits : ∀ i j, i < n → j < n →
      ∃ p ∈ xs, p.1 = i ∨ p.2 = j) :
    n ≤ xs.length := by
  by_cases enough : n ≤ xs.length
  · exact enough
  exfalso
  have h : xs.length < n := by omega
  have hr : (xs.map Prod.fst).length < n := by simpa using h
  have hc : (xs.map Prod.snd).length < n := by simpa using h
  obtain ⟨i, hi, hrow⟩ := missingBelow n (xs.map Prod.fst) hr
  obtain ⟨j, hj, hcol⟩ := missingBelow n (xs.map Prod.snd) hc
  obtain ⟨p, hp, he⟩ := hits i j hi hj
  rcases he with he | he
  · exact hrow (List.mem_map.mpr ⟨p, hp, he⟩)
  · exact hcol (List.mem_map.mpr ⟨p, hp, he⟩)

end ResearchCommons.CappedGridCross

#print axioms ResearchCommons.CappedGridCross.crossHittingLowerBound
