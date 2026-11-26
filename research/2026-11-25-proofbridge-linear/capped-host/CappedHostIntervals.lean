import Lean

namespace ResearchCommons.CappedHostIntervals

structure BagInterval where
  lo : Nat
  hi : Nat

private theorem maxLower (a : BagInterval) (xs : List BagInterval) :
    ∃ anchor ∈ a :: xs, ∀ b ∈ a :: xs, b.lo ≤ anchor.lo := by
  induction xs generalizing a with
  | nil =>
    refine ⟨a, by simp, ?_⟩
    intro b hb
    simp at hb
    subst b
    exact Nat.le_refl _
  | cons b tail ih =>
    obtain ⟨anchor, hm, ha⟩ := ih b
    rcases Nat.le_total a.lo anchor.lo with h | h
    · refine ⟨anchor, List.mem_cons_of_mem a hm, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with he | he
      · subst d
        exact h
      · exact ha d he
    · refine ⟨a, by simp, ?_⟩
      intro d hd
      rcases List.mem_cons.mp hd with he | he
      · subst d
        exact Nat.le_refl _
      · exact Nat.le_trans (ha d he) h

/-- A finite nonempty pairwise-intersecting family of bag intervals
has a common bag index. The overlap hypotheses include the diagonal. -/
theorem commonBag (a : BagInterval) (xs : List BagInterval)
    (overlap : ∀ b ∈ a :: xs, ∀ c ∈ a :: xs,
      ∃ n : Nat, b.lo ≤ n ∧ n ≤ b.hi ∧ c.lo ≤ n ∧ n ≤ c.hi) :
    ∃ n : Nat, ∀ b ∈ a :: xs, b.lo ≤ n ∧ n ≤ b.hi := by
  obtain ⟨anchor, hm, hmax⟩ := maxLower a xs
  refine ⟨anchor.lo, ?_⟩
  intro b hb
  obtain ⟨n, h₁, _, _, h₂⟩ := overlap anchor hm b hb
  exact ⟨hmax b hb, Nat.le_trans h₁ h₂⟩

end ResearchCommons.CappedHostIntervals

#print axioms ResearchCommons.CappedHostIntervals.commonBag
