import CappedConnectedBags
open PopulationCounting ResearchCommons.CappedConnectedBags
open ResearchCommons.CappedActualBags

example {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (V : List Nat) (u : Nat) (hu : u ∈ V)
    (conn : ∀ a ∈ V, ∀ b ∈ V, WalkInside (Adj p) V a b) :
    ∃ l r, l ≤ r ∧ ∀ t, Hits p V t ↔ l ≤ t ∧ t ≤ r :=
  connected_hit_interval p V u hu conn

private def emptyModel : InfiniteLabeledPopulation 0 0 where
  edge := fun _ _ => none
  root := fun _ => false
  birth_order := by simp
  root_no_parents := by simp
  parent_of_label := by simp
  childSupport := fun _ => 0
  no_children_after := by simp
  child_cap := by simp
  rootSupport := 0
  no_roots_after := by simp

-- Without connectivity, the set {0,2} can leave an actual hole at bag 1.
theorem disconnected_negative :
    Hits emptyModel [0,2] 0 ∧ Hits emptyModel [0,2] 2 ∧ ¬ Hits emptyModel [0,2] 1 := by
  constructor
  · exact ⟨0, by simp, by simp [bagVertices]⟩
  constructor
  · exact ⟨2, by simp, by simp [bagVertices]⟩
  · simp [Hits,bagVertices,outgoingAcross,emptyModel]

#print axioms disconnected_negative
