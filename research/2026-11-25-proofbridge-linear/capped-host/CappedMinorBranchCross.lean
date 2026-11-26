import CappedHostIntervals
import CappedConnectedBags

namespace ResearchCommons.CappedMinorBranchCross
open PopulationCounting CappedConnectedBags

def Connected (A : Nat → Nat → Prop) (V : List Nat) : Prop :=
  ∀ u ∈ V, ∀ v ∈ V, WalkInside A V u v

def Linking (A : Nat → Nat → Prop) (U V : List Nat) : Prop :=
  ∃ u ∈ U, ∃ v ∈ V, A u v

def branchCross (n : Nat) (B : Nat → Nat → List Nat) (i j : Nat) : List Nat :=
  (List.range n).flatMap (B i) ++ (List.range n).flatMap (fun r => B r j)

theorem branchCross_mem_iff {n i j v : Nat} {B : Nat → Nat → List Nat}
    (hi : i < n) (hj : j < n) :
    v ∈ branchCross n B i j ↔
      ∃ r c, r < n ∧ c < n ∧ (r = i ∨ c = j) ∧ v ∈ B r c := by
  simp only [branchCross, List.mem_append, List.mem_flatMap, List.mem_range]
  constructor
  · rintro (⟨c,hc,hv⟩ | ⟨r,hr,hv⟩)
    · exact ⟨i,c,hi,hc,Or.inl rfl,hv⟩
    · exact ⟨r,j,hr,hj,Or.inr rfl,hv⟩
  · rintro ⟨r,c,hr,hc,(rfl | rfl),hv⟩
    · exact Or.inl ⟨c,hc,hv⟩
    · exact Or.inr ⟨r,hr,hv⟩

private theorem appendWalk {A : Nat → Nat → Prop} {V : List Nat} {a b c : Nat}
    (w : WalkInside A V a b) (w' : WalkInside A V b c) : WalkInside A V a c := by
  induction w with
  | stay => exact w'
  | step ha e _ ih => exact .step ha e (ih w')

private theorem widen {A : Nat → Nat → Prop} {U V : List Nat} {a b : Nat}
    (sub : ∀ x ∈ U, x ∈ V) (w : WalkInside A U a b) : WalkInside A V a b := by
  induction w with
  | stay ha => exact .stay (sub _ ha)
  | step ha e _ ih => exact .step (sub _ ha) e ih

private theorem start_mem {A : Nat → Nat → Prop} {V : List Nat} {u v : Nat}
    (w : WalkInside A V u v) : u ∈ V := by
  cases w with
  | stay h => exact h
  | step h _ _ => exact h

private theorem reverseWalk {A : Nat → Nat → Prop} {V : List Nat} {u v : Nat}
    (sym : ∀ x y, A x y → A y x) (w : WalkInside A V u v) : WalkInside A V v u := by
  induction w with
  | stay h => exact .stay h
  | @step x y z hx e tail ih => exact appendWalk ih (.step (start_mem tail) (sym _ _ e) (.stay hx))

private theorem axisForward {A : Nat → Nat → Prop} {V : List Nat}
    (n : Nat) (B : Nat → List Nat)
    (inV : ∀ i, i < n → ∀ u ∈ B i, u ∈ V)
    (conn : ∀ i, i < n → Connected A (B i))
    (links : ∀ i, i+1 < n → Linking A (B i) (B (i+1)))
    (i j : Nat) (hij : i ≤ j) (hj : j < n) (u v : Nat)
    (hu : u ∈ B i) (hv : v ∈ B j) : WalkInside A V u v := by
  induction j generalizing v with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact widen (inV 0 hj) (conn 0 hj u hu v hv)
  | succ j ih =>
    by_cases h : i ≤ j
    · have hj' : j < n := by omega
      obtain ⟨a,ha,b,hb,hab⟩ := links j hj
      exact appendWalk (ih h hj' a ha)
        (.step (inV j hj' a ha) hab (widen (inV (j+1) hj) (conn (j+1) hj b hb v hv)))
    · have he : i = j + 1 := by omega
      subst i
      exact widen (inV (j+1) hj) (conn (j+1) hj u hu v hv)

private theorem axis {A : Nat → Nat → Prop} {V : List Nat}
    (sym : ∀ x y, A x y → A y x)
    (n : Nat) (B : Nat → List Nat)
    (inV : ∀ i, i < n → ∀ u ∈ B i, u ∈ V)
    (conn : ∀ i, i < n → Connected A (B i))
    (links : ∀ i, i+1 < n → Linking A (B i) (B (i+1)))
    (i j : Nat) (hi : i < n) (hj : j < n) (u v : Nat)
    (hu : u ∈ B i) (hv : v ∈ B j) : WalkInside A V u v := by
  rcases Nat.le_total i j with h | h
  · exact axisForward n B inV conn links i j h hj u v hu hv
  · exact reverseWalk sym (axisForward n B inV conn links j i h hi v u hv hu)

/-- Actual host walks entirely inside the union of the cross's branch sets.
Only the junction branch needs explicit nonemptiness here. -/
theorem branch_cross_connected {A : Nat → Nat → Prop}
    (sym : ∀ u v, A u v → A v u) (n : Nat) (B : Nat → Nat → List Nat)
    (conn : ∀ r c, r < n → c < n → Connected A (B r c))
    (row : ∀ r c, r < n → c+1 < n → Linking A (B r c) (B r (c+1)))
    (col : ∀ r c, r+1 < n → c < n → Linking A (B r c) (B (r+1) c))
    (i j : Nat) (hi : i < n) (hj : j < n) (hub : ∃ z, z ∈ B i j) :
    Connected A (branchCross n B i j) := by
  obtain ⟨z,hz⟩ := hub
  have route (u : Nat) (hu : u ∈ branchCross n B i j) :
      WalkInside A (branchCross n B i j) u z := by
    obtain ⟨r,c,hr,hc,(rfl | rfl),hmem⟩ := (branchCross_mem_iff hi hj).mp hu
    · exact axis sym n (B r)
        (fun c hc u hu => (branchCross_mem_iff hi hj).mpr ⟨r,c,hi,hc,Or.inl rfl,hu⟩)
        (fun c hc => conn r c hi hc) (fun c hc => row r c hi hc)
        c j hc hj u z hmem hz
    · exact axis sym n (fun r => B r c)
        (fun r hr u hu => (branchCross_mem_iff hi hj).mpr ⟨r,c,hr,hj,Or.inr rfl,hu⟩)
        (fun r hr => conn r c hr hj) (fun r hr => col r c hr hj)
        r i hr hi u z hmem hz
  intro u hu v hv
  exact appendWalk (route u hu) (reverseWalk sym (route v hv))

theorem branch_cross_hit_interval {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n : Nat) (B : Nat → Nat → List Nat)
    (conn : ∀ r c, r < n → c < n → Connected (Adj p) (B r c))
    (row : ∀ r c, r < n → c+1 < n → Linking (Adj p) (B r c) (B r (c+1)))
    (col : ∀ r c, r+1 < n → c < n → Linking (Adj p) (B r c) (B (r+1) c))
    (i j : Nat) (hi : i < n) (hj : j < n) (hub : ∃ z, z ∈ B i j) :
    ∃ l r, l ≤ r ∧ ∀ t, Hits p (branchCross n B i j) t ↔ l ≤ t ∧ t ≤ r := by
  obtain ⟨z,hz⟩ := hub
  exact connected_hit_interval p _ z
    ((branchCross_mem_iff hi hj).mpr ⟨i,j,hi,hj,Or.inl rfl,hz⟩)
    (branch_cross_connected (fun _ _ h => h.symm) n B conn row col i j hi hj ⟨z,hz⟩)

theorem branch_crosses_pair_hit {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n : Nat) (B : Nat → Nat → List Nat) (i j r c : Nat)
    (hi : i < n) (hj : j < n) (hr : r < n) (hc : c < n)
    (crossing_branch : ∃ z, z ∈ B i c) :
    ∃ t, Hits p (branchCross n B i j) t ∧ Hits p (branchCross n B r c) t := by
  obtain ⟨z,hz⟩ := crossing_branch
  have hbag : z ∈ CappedActualBags.bagVertices p z := by simp [CappedActualBags.bagVertices]
  exact ⟨z,⟨z,(branchCross_mem_iff hi hj).mpr ⟨i,c,hi,hc,Or.inl rfl,hz⟩,hbag⟩,
    ⟨z,(branchCross_mem_iff hr hc).mpr ⟨i,c,hi,hc,Or.inr rfl,hz⟩,hbag⟩⟩

/-- Every cross is met by one actual bag. This is a direct, finite-family
application of the checked host interval Helly lemma. -/
theorem common_branch_cross_cut {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (n : Nat) (pos : 0 < n) (B : Nat → Nat → List Nat)
    (conn : ∀ r c, r < n → c < n → Connected (Adj p) (B r c))
    (row : ∀ r c, r < n → c+1 < n → Linking (Adj p) (B r c) (B r (c+1)))
    (col : ∀ r c, r+1 < n → c < n → Linking (Adj p) (B r c) (B (r+1) c))
    (inhab : ∀ r c, r < n → c < n → ∃ z, z ∈ B r c) :
    ∃ cut, ∀ i j : Nat, i < n → j < n →
      ∃ a b : Nat, a < n ∧ b < n ∧ (a = i ∨ b = j) ∧
        ∃ v ∈ B a b, v ∈ CappedActualBags.bagVertices p cut := by
  classical
  let C := Fin n × Fin n
  let E (x : C) := branch_cross_hit_interval p n B conn row col x.1.val x.2.val
    x.1.isLt x.2.isLt (inhab _ _ x.1.isLt x.2.isLt)
  let I (x : C) : CappedHostIntervals.BagInterval :=
    ⟨Classical.choose (E x),Classical.choose (Classical.choose_spec (E x))⟩
  have spec (x : C) (t : Nat) :
      Hits p (branchCross n B x.1.val x.2.val) t ↔ (I x).lo ≤ t ∧ t ≤ (I x).hi :=
    (Classical.choose_spec (Classical.choose_spec (E x))).2 t
  let cells : List C := (List.finRange n).flatMap fun i => (List.finRange n).map (Prod.mk i)
  let zero : C := (⟨0,pos⟩,⟨0,pos⟩)
  have repr (b : CappedHostIntervals.BagInterval) (h : b ∈ I zero :: cells.map I) :
      ∃ x : C, I x = b := by
    rcases List.mem_cons.mp h with he | hm
    · exact ⟨zero,he.symm⟩
    · obtain ⟨x,_,hx⟩ := List.mem_map.mp hm
      exact ⟨x,hx⟩
  obtain ⟨cut,hcut⟩ := CappedHostIntervals.commonBag (I zero) (cells.map I) (by
    intro b hb c hc
    obtain ⟨x,rfl⟩ := repr b hb
    obtain ⟨y,rfl⟩ := repr c hc
    obtain ⟨t,hx,hy⟩ := branch_crosses_pair_hit p n B x.1.val x.2.val y.1.val y.2.val
      x.1.isLt x.2.isLt y.1.isLt y.2.isLt (inhab _ _ x.1.isLt y.2.isLt)
    exact ⟨t,(spec x t).mp hx |>.1,(spec x t).mp hx |>.2,
      (spec y t).mp hy |>.1,(spec y t).mp hy |>.2⟩)
  refine ⟨cut,?_⟩
  intro i j hi hj
  let x : C := (⟨i,hi⟩,⟨j,hj⟩)
  have hx : x ∈ cells := List.mem_flatMap.mpr
    ⟨x.1,List.mem_finRange _,List.mem_map.mpr ⟨x.2,List.mem_finRange _,rfl⟩⟩
  obtain ⟨v,hmem,hbag⟩ := (spec x cut).mpr
    (hcut (I x) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨x,hx,rfl⟩)))
  obtain ⟨a,b,ha,hb,hcross,hV⟩ := (branchCross_mem_iff hi hj).mp hmem
  exact ⟨a,b,ha,hb,hcross,v,hV,hbag⟩

end ResearchCommons.CappedMinorBranchCross
#print axioms ResearchCommons.CappedMinorBranchCross.branch_cross_connected
#print axioms ResearchCommons.CappedMinorBranchCross.branch_cross_hit_interval
#print axioms ResearchCommons.CappedMinorBranchCross.branch_crosses_pair_hit

#print axioms ResearchCommons.CappedMinorBranchCross.common_branch_cross_cut
