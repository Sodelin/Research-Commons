import CappedConnectedBags

namespace ResearchCommons.CappedGridWalks
open PopulationCounting ResearchCommons.CappedConnectedBags

private theorem chain {A : Nat → Nat → Prop} {V : List Nat} {u v w : Nat}
    (uv : WalkInside A V u v) (vw : WalkInside A V v w) : WalkInside A V u w := by
  induction uv with
  | stay => exact vw
  | step h e _ ih => exact .step h e (ih vw)

private theorem first_mem {A : Nat → Nat → Prop} {V : List Nat} {u v : Nat}
    (w : WalkInside A V u v) : u ∈ V := by cases w with
  | stay h => exact h
  | step h _ _ => exact h

private theorem reverse {A : Nat → Nat → Prop} {V : List Nat} {u v : Nat}
    (sym : ∀ {a b}, A a b → A b a)
    (w : WalkInside A V u v) : WalkInside A V v u := by
  induction w with
  | stay h => exact .stay h
  | @step x y z hx hxy yz ih => exact chain ih (.step (first_mem yz) (sym hxy) (.stay hx))

private theorem axisForward {A : Nat → Nat → Prop} {V : List Nat}
    (side : Nat) (f : Nat → Nat)
    (mem : ∀ x, x < side → f x ∈ V)
    (step : ∀ x, x + 1 < side → A (f x) (f (x + 1)))
    (i j : Nat) (le : i ≤ j) (bound : j < side) : WalkInside A V (f i) (f j) := by
  induction j with
  | zero =>
    have e : i = 0 := by omega
    subst i
    exact .stay (mem 0 bound)
  | succ j ih =>
    by_cases h : i ≤ j
    · have hj : j < side := by omega
      exact chain (ih h hj) (.step (mem j hj) (step j bound) (.stay (mem (j+1) bound)))
    · have e : i = j + 1 := by omega
      subst i
      exact .stay (mem (j+1) bound)

private theorem axis {A : Nat → Nat → Prop} {V : List Nat}
    (sym : ∀ {a b}, A a b → A b a)
    (side : Nat) (f : Nat → Nat)
    (mem : ∀ x, x < side → f x ∈ V)
    (step : ∀ x, x + 1 < side → A (f x) (f (x + 1)))
    (i j : Nat) (hi : i < side) (hj : j < side) : WalkInside A V (f i) (f j) := by
  rcases Nat.le_total i j with h | h
  · exact axisForward side f mem step i j h hj
  · exact reverse sym (axisForward side f mem step j i h hi)

def imageCross (side : Nat) (f : Nat → Nat → Nat) (i j : Nat) : List Nat :=
  (List.range side).map (f i) ++ (List.range side).map (fun r => f r j)

theorem row_mem (side : Nat) (f : Nat → Nat → Nat) (i j x : Nat) (hx : x < side) :
    f i x ∈ imageCross side f i j := by
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x,List.mem_range.mpr hx,rfl⟩))

theorem col_mem (side : Nat) (f : Nat → Nat → Nat) (i j x : Nat) (hx : x < side) :
    f x j ∈ imageCross side f i j := by
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨x,List.mem_range.mpr hx,rfl⟩))

/-- Unit-edge adjacency is enough to construct the actual walks inside a cross. -/
theorem image_cross_connected {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (side : Nat) (f : Nat → Nat → Nat)
    (hrow : ∀ r c, r < side → c+1 < side → Adj p (f r c) (f r (c+1)))
    (hcol : ∀ r c, r+1 < side → c < side → Adj p (f r c) (f (r+1) c))
    (i j : Nat) (hi : i < side) (hj : j < side) :
    ∀ u ∈ imageCross side f i j, ∀ v ∈ imageCross side f i j,
      WalkInside (Adj p) (imageCross side f i j) u v := by
  have sym {a b : Nat} (h : Adj p a b) : Adj p b a := h.symm
  have hub (u : Nat) (hu : u ∈ imageCross side f i j) :
      WalkInside (Adj p) (imageCross side f i j) u (f i j) := by
    rcases List.mem_append.mp hu with h | h
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp h
      subst u
      exact axis @sym side (f i) (row_mem side f i j) (fun c h => hrow i c hi h)
        x j (List.mem_range.mp hx) hj
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp h
      subst u
      exact axis @sym side (fun r => f r j) (col_mem side f i j)
        (fun r h => hcol r j h hj) x i (List.mem_range.mp hx) hi
  intro u hu v hv
  exact chain (hub u hu) (reverse @sym (hub v hv))

/-- The concrete embedded cross meets an interval of actual host bags. -/
theorem image_cross_hit_interval {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (side : Nat) (f : Nat → Nat → Nat)
    (hrow : ∀ r c, r < side → c+1 < side → Adj p (f r c) (f r (c+1)))
    (hcol : ∀ r c, r+1 < side → c < side → Adj p (f r c) (f (r+1) c))
    (i j : Nat) (hi : i < side) (hj : j < side) :
    ∃ l r, l ≤ r ∧ ∀ t, Hits p (imageCross side f i j) t ↔ l ≤ t ∧ t ≤ r :=
  connected_hit_interval p _ (f i j) (row_mem side f i j j hj)
    (image_cross_connected p side f hrow hcol i j hi hj)

/-- Two crosses meet in an actual host bag, without an injectivity premise. -/
theorem image_crosses_pair_hit {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (side : Nat) (f : Nat → Nat → Nat) (i j u v : Nat)
    (hi : i < side) (hv : v < side) :
    ∃ t, Hits p (imageCross side f i j) t ∧ Hits p (imageCross side f u v) t := by
  have itself : f i v ∈ ResearchCommons.CappedActualBags.bagVertices p (f i v) := by
    simp [ResearchCommons.CappedActualBags.bagVertices]
  exact ⟨f i v, ⟨f i v,row_mem side f i j v hv,itself⟩,
    ⟨f i v,col_mem side f u v i hi,itself⟩⟩

#print axioms image_cross_hit_interval
#print axioms image_crosses_pair_hit
end ResearchCommons.CappedGridWalks
