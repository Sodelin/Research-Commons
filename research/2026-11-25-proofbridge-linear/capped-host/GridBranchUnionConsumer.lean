import GridMinorControl
import GridMinorCross

namespace ResearchCommons.GridBranchUnionConsumer
open CappedConnectedBags GridMinorControl GridMinorCross

private def branches (i : Nat) : List Nat := [2*i,2*i+1]
private def indexAdj (i j : Nat) : Prop := i+1=j ∨ j+1=i

private theorem twoConnected {A : Nat → Nat → Prop} (x y : Nat)
    (xy : A x y) (yx : A y x) : Connected A [x,y] := by
  intro u hu v hv
  simp at hu hv
  rcases hu with h | h <;> subst u <;>
    rcases hv with e | e <;> subst v
  · exact .stay (by simp)
  · exact .step (by simp) xy (.stay (by simp))
  · exact .step (by simp) yx (.stay (by simp))
  · exact .stay (by simp)

private theorem branchConn (i : Nat) :
    Connected (Adj ray) (branches i) :=
  twoConnected _ _ (ray_step _) (ray_step _).symm

private theorem branchLinks (i j : Nat) (h : indexAdj i j) :
    Linking (Adj ray) (branches i) (branches j) := by
  rcases h with h | h
  · subst j
    refine ⟨2*i+1, by simp [branches], 2*(i+1), by simp [branches], ?_⟩
    have e : 2*(i+1)=2*i+1+1 := by omega
    rw [e]
    exact ray_step _
  · subst i
    refine ⟨2*(j+1), by simp [branches], 2*j+1, by simp [branches], ?_⟩
    have e : 2*(j+1)=2*j+1+1 := by omega
    rw [e]
    exact (ray_step _).symm

/-- Genuine adjacent branch sets [0,1] and [2,3], not singleton surrogates. -/
theorem checked_four_vertex_union : Connected (Adj ray) [0,1,2,3] := by
  have h : Connected (Adj ray) ([0,1].flatMap branches) :=
    connected_union (G := indexAdj) (twoConnected _ _ (Or.inl rfl) (Or.inr rfl))
      (fun x _ => branchConn x) branchLinks
  exact h

/-- The actual bag interface consumes the joined witness without importing
a grid minor or a separate path representation. -/
theorem checked_union_hit_interval :
    ∃ l r, l ≤ r ∧ ∀ t, Hits ray [0,1,2,3] t ↔ l ≤ t ∧ t ≤ r :=
  connected_hit_interval ray _ 0 (by simp) checked_four_vertex_union

#print axioms checked_four_vertex_union
#print axioms checked_union_hit_interval
end ResearchCommons.GridBranchUnionConsumer
