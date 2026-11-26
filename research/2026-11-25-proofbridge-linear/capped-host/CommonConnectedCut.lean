import CappedConnectedBags

namespace ResearchCommons.CommonConnectedCut
open PopulationCounting CappedActualBags CappedConnectedBags

private theorem min_hit (P : Nat → Prop) (h : ∃ t, P t) :
    ∃ m, P m ∧ ∀ t, P t → m ≤ t := by
  classical
  obtain ⟨t, ht⟩ := h
  suffices ∀ b, (∃ u, u ≤ b ∧ P u) → ∃ m, P m ∧ ∀ t, P t → m ≤ t from
    this t ⟨t, Nat.le_refl _, ht⟩
  intro b
  induction b with
  | zero =>
    rintro ⟨u,hu,hpu⟩
    have e : u = 0 := by omega
    subst u
    exact ⟨0,hpu,fun _ _ => Nat.zero_le _⟩
  | succ b ih =>
    intro h'
    by_cases hsmall : ∃ u, u ≤ b ∧ P u
    · exact ih hsmall
    · obtain ⟨u,hu,hpu⟩ := h'
      have hgt : ¬ u ≤ b := fun h => hsmall ⟨u,h,hpu⟩
      refine ⟨u,hpu,fun t ht => ?_⟩
      have hgt' : ¬ t ≤ b := fun h => hsmall ⟨t,h,ht⟩
      omega

private theorem maxList {α : Type} (key : α → Nat) (lead : α) (tail : List α) :
    ∃ y ∈ lead :: tail, ∀ x ∈ lead :: tail, key x ≤ key y := by
  induction tail generalizing lead with
  | nil => exact ⟨lead,by simp,fun x h => by have e := List.mem_singleton.mp h; subst x; exact Nat.le_refl _⟩
  | cons a rest ih =>
    obtain ⟨y,hy,hmax⟩ := ih a
    by_cases h : key lead ≤ key y
    · refine ⟨y,List.mem_cons_of_mem _ hy,?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with e | hm
      · simpa [e] using h
      · exact hmax _ hm
    · refine ⟨lead,by simp,?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with e | hm
      · simp [e]
      · exact Nat.le_trans (hmax _ hm) (by omega)

/-- Among finitely many nonempty convex subsets of natural cuts, pairwise
overlap implies a common cut. No upper bound on individual sets is needed. -/
theorem convex_common {α : Type} (idx : List α) (P : α → Nat → Prop)
    (conv : ∀ a ∈ idx, ∀ l t r, l ≤ t → t ≤ r → P a l → P a r → P a t)
    (over : ∀ a ∈ idx, ∀ b ∈ idx, ∃ t, P a t ∧ P b t) :
    ∃ t, ∀ a ∈ idx, P a t := by
  classical
  cases idx with
  | nil => exact ⟨0, by simp⟩
  | cons x xs =>
    let E (a : α) (h : a ∈ x :: xs) : ∃ m, P a m ∧ ∀ t, P a t → m ≤ t :=
      min_hit (P a) (by obtain ⟨t,ha,_⟩ := over a h a h; exact ⟨t,ha⟩)
    let L (a : α) : Nat := if h : a ∈ x :: xs then Classical.choose (E a h) else 0
    have Lspec (a : α) (h : a ∈ x :: xs) : P a (L a) ∧ ∀ t, P a t → L a ≤ t := by
      simpa only [L, dif_pos h] using Classical.choose_spec (E a h)
    obtain ⟨a,ha,hm⟩ := maxList L x xs
    refine ⟨L a, fun b hb => ?_⟩
    obtain ⟨r,hra,hrb⟩ := over a ha b hb
    exact conv b hb (L b) (L a) r (hm b hb) ((Lspec a ha).2 _ hra) (Lspec b hb).1 hrb

/-- A finite family of connected vertex sets with pairwise shared vertices has
one actual bag hitting all its members. -/
theorem connected_common {k d : Nat} (p : InfiniteLabeledPopulation k d)
    {α : Type} (idx : List α) (V : α → List Nat)
    (conn : ∀ a ∈ idx, ∀ u ∈ V a, ∀ v ∈ V a, WalkInside (Adj p) (V a) u v)
    (inter : ∀ a ∈ idx, ∀ b ∈ idx, ∃ v, v ∈ V a ∧ v ∈ V b) :
    ∃ cut, ∀ a ∈ idx, Hits p (V a) cut := by
  refine convex_common idx (fun a => Hits p (V a))
    (fun a ha l t r hlt htr => connected_hits_convex p (V a) (conn a ha) l t r hlt htr) ?_
  intro a ha b hb
  obtain ⟨v,hv,hw⟩ := inter a ha b hb
  have hbag : v ∈ bagVertices p v := by simp [bagVertices]
  exact ⟨v,⟨v,hv,hbag⟩,⟨v,hw,hbag⟩⟩

#print axioms convex_common
#print axioms connected_common
end ResearchCommons.CommonConnectedCut
