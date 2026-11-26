import CappedConnectedBags

namespace ResearchCommons.GridMinorControl
open PopulationCounting CappedActualBags CappedConnectedBags

def rayEdge (u v : Nat) : Option Nat := if u+1=v then some 0 else none

def ray : InfiniteLabeledPopulation 1 1 where
  edge := rayEdge
  root := fun x => x == 0
  birth_order := by
    intro u v h
    by_cases e : u+1 = v
    · omega
    · simp [rayEdge,e] at h
  root_no_parents := by
    intro v h u
    have hv : v = 0 := by simpa using h
    subst v
    simp [rayEdge]
  parent_of_label := by
    intro v h l hl
    have hv : v ≠ 0 := by simpa using h
    have hl0 : l = 0 := by omega
    subst l
    exact ⟨v-1, by simp [rayEdge, (show v-1+1=v by omega)]⟩
  childSupport := fun u => u+2
  no_children_after := by
    intro u v h
    simp [rayEdge, (show u+1 ≠ v by omega)]
  child_cap := by
    intro u
    change sumBelow (u+2) (fun v => edgeBit (rayEdge u v)) ≤ 1
    have sz : ∀ m, m ≤ u+1 →
        sumBelow m (fun v => edgeBit (rayEdge u v)) = 0 := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        rw [sumBelow, ih (by omega)]
        simp [rayEdge, edgeBit, (show u+1 ≠ m by omega)]
    have z := sz (u+1) (Nat.le_refl _)
    rw [sumBelow,z]
    simp [rayEdge,edgeBit]
  rootSupport := 1
  no_roots_after := by
    intro v h
    simpa using (show v ≠ 0 by omega)

theorem ray_step (u : Nat) : Adj ray u (u+1) :=
  Or.inl (by simp [ray,rayEdge])

theorem ray_width (cut : Nat) : (bagVertices ray cut).length ≤ 2 := by
  have h := bag_width ray cut
  exact h

-- A path from i to j using only vertices in the closed interval.
private theorem up (i j : Nat) (h : i ≤ j) :
    WalkInside (Adj ray) ((List.range (j+1)).filter (fun x => i ≤ x)) i j := by
  have aux (n : Nat) (u : Nat) (eq : u+n=j) (b : i≤u) :
      WalkInside (Adj ray) ((List.range (j+1)).filter (fun x => i ≤ x)) u j := by
    induction n generalizing u with
    | zero =>
      have e : u=j := by omega
      subst u
      exact .stay (by simp [b])
    | succ n ih =>
      refine .step ?_ (ray_step u) (ih (u+1) (by omega) (by omega))
      simp [b, (show u < j+1 by omega)]
  exact aux (j-i) i (by omega) (Nat.le_refl _)

-- Mere routing: all nine cell representatives are distinct, all 12
-- oriented grid edges lift to genuine host walks, but shared transit is allowed.
def weakRoutes3 : Prop :=
  ∃ f : Nat × Nat → Nat,
    (∀ x y : Nat × Nat, x.1<3 → x.2<3 → y.1<3 → y.2<3 → f x=f y → x=y) ∧
    (∀ r c, r<3 → c+1<3 → ∃ V, WalkInside (Adj ray) V (f (r,c)) (f (r,c+1))) ∧
    (∀ r c, r+1<3 → c<3 → ∃ V, WalkInside (Adj ray) V (f (r,c)) (f (r+1,c)))

theorem routing_only_not_width_control :
    weakRoutes3 ∧ ∀ cut, (bagVertices ray cut).length < 3 := by
  refine ⟨?_, fun cut => Nat.lt_succ_of_le (ray_width cut)⟩
  refine ⟨fun (r,c) => 3*r+c, ?_, ?_, ?_⟩
  · intro ⟨r,c⟩ ⟨s,t⟩ hr hc hs ht e
    dsimp at *
    apply Prod.ext <;> dsimp <;> omega
  · intro r c _ _
    exact ⟨_, up (3*r+c) (3*r+(c+1)) (by omega)⟩
  · intro r c _ _
    exact ⟨_, up (3*r+c) (3*(r+1)+c) (by omega)⟩

#print axioms routing_only_not_width_control
end ResearchCommons.GridMinorControl
