import ChronologicalEncoding

namespace ChronologyFixture
open BirthOrder PopulationReindex ChronologicalEncoding

def birth (v : Nat) : Nat := v / 2

/- Two same-date vertices in every layer. Edges go to both next-layer
vertices, with the label assigned by the source vertex's parity. -/
def edge (x y l : Nat) : Prop := birth y = birth x + 1 ∧ l = x % 2

def population : RelationalPopulation birth 2 2 where
  E := edge
  unique := by
    intro x y a b ha hb
    exact ha.2.trans hb.2.symm
  valid := by
    intro x y l h
    have hmod := h.2
    omega
  increasing := by
    intro x y l h
    exact h.1 ▸ Nat.lt_succ_self _
  infinite := by
    intro xs
    refine ⟨xs.sum + 1, ?_⟩
    intro hn
    have hsum : ∀ l : List Nat, ∀ n ∈ l, n ≤ l.sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        intro n h
        simp only [List.mem_cons, List.sum_cons] at *
        rcases h with rfl | h
        · omega
        · have := ih n h; omega
    have := hsum xs (xs.sum + 1) hn
    omega
  sublevel := by
    intro r
    refine ⟨List.range (2 * (r + 1)), ?_⟩
    intro x hx
    apply List.mem_range.mpr
    unfold birth at hx
    omega
  roots := by
    refine ⟨[0, 1], ?_⟩
    intro y hy
    by_cases h : birth y = 0
    · unfold birth at h
      simp; omega
    · unfold birth at h
      let x := 2 * (birth y - 1)
      exact False.elim (hy x (x % 2) (by unfold edge; unfold x; unfold birth; omega))
  parent := by
    intro y hy l hl
    have h : 0 < birth y := by
      by_cases hn : 0 < birth y
      · exact hn
      · exfalso
        apply hy
        intro x g hE
        have := hE.1
        omega
    let x := 2 * (birth y - 1) + l
    refine ⟨x, ?_⟩
    unfold edge x birth at *
    omega
  children := by
    intro x
    let q := 2 * (birth x + 1)
    refine ⟨[q, q + 1], by simp, ?_⟩
    rintro y ⟨l, hl⟩
    have hp := hl.1
    unfold q birth at *
    simp; omega

theorem test_source_gender :
    ∀ i j l, (PopulationReindex.toNatPopulation (present population)).edge i j = some l →
      ((enumeration (present population)).toFun i) % 2 = l :=
  (exact_source_gender population (· % 2)).mp (fun _ _ _ h => h.2.symm)

theorem test_adj_forward :
    let e := enumeration (present population)
    let p := PopulationReindex.toNatPopulation (present population)
    (p.edge (e.index 0) (e.index 3)).isSome = true ∨
      (p.edge (e.index 3) (e.index 0)).isSome = true := by
  dsimp
  apply (exact_adjacency population _ _).mpr
  simp only [OrderedEnumeration.toFun_index]
  exact Or.inl ⟨0, by change (3 / 2 : Nat) = 0 / 2 + 1 ∧ 0 = 0 % 2; decide⟩

theorem test_adj_not_created_by_tie :
    let e := enumeration (present population)
    let p := PopulationReindex.toNatPopulation (present population)
    ¬ ((p.edge (e.index 0) (e.index 1)).isSome = true ∨
      (p.edge (e.index 1) (e.index 0)).isSome = true) := by
  dsimp
  intro h
  rcases (exact_adjacency population _ _).mp h with h | h <;>
    simp only [OrderedEnumeration.toFun_index] at h <;>
    obtain ⟨l, hl⟩ := h <;> exact (by decide : ¬ (0 = 1)) hl.1

end ChronologyFixture

#print axioms ChronologyFixture.test_source_gender
#print axioms ChronologyFixture.test_adj_forward
#print axioms ChronologyFixture.test_adj_not_created_by_tie
