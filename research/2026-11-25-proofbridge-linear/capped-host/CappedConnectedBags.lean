import CappedActualBags

namespace ResearchCommons.CappedConnectedBags
open PopulationCounting ResearchCommons.CappedActualBags

def Adj {k d : Nat} (p : InfiniteLabeledPopulation k d) (u v : Nat) : Prop :=
  (p.edge u v).isSome = true ∨ (p.edge v u).isSome = true

inductive WalkInside (A : Nat → Nat → Prop) (V : List Nat) : Nat → Nat → Prop
  | stay {u : Nat} : u ∈ V → WalkInside A V u u
  | step {u v w : Nat} : u ∈ V → A u v → WalkInside A V v w → WalkInside A V u w

def Hits {k d : Nat} (p : InfiniteLabeledPopulation k d) (V : List Nat) (cut : Nat) : Prop :=
  ∃ u ∈ V, u ∈ bagVertices p cut

private theorem walk_start {A : Nat → Nat → Prop} {V : List Nat} {u v : Nat}
    (w : WalkInside A V u v) : u ∈ V := by
  cases w with
  | stay h => exact h
  | step h _ _ => exact h

private theorem edge_shares_bag {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (u v : Nat) (adj : Adj p u v) :
    ∃ t, u ∈ bagVertices p t ∧ v ∈ bagVertices p t := by
  rcases adj with h | h
  · exact ⟨v, edge_in_target_bag p u v h⟩
  · exact ⟨u, (edge_in_target_bag p v u h).2, (edge_in_target_bag p v u h).1⟩

private theorem walk_stays_left {k d : Nat} (p : InfiniteLabeledPopulation k d)
    {V : List Nat} {u v : Nat} (w : WalkInside (Adj p) V u v)
    (mid : Nat) (miss : ¬ Hits p V mid)
    (left : ∀ t, u ∈ bagVertices p t → t < mid) :
    ∀ t, v ∈ bagVertices p t → t < mid := by
  induction w with
  | stay => exact left
  | @step a b c ha adjacent tail ih =>
    apply ih
    intro far hf
    obtain ⟨s, hs, hb⟩ := edge_shares_bag p a b adjacent
    have sl := left s hs
    by_cases h : far < mid
    · exact h
    · have hm : mid ≤ far := by omega
      have covered := consecutive_bags p b s mid far (by omega) hm hb hf
      exact False.elim (miss ⟨b, walk_start tail, covered⟩)

/-- A connected vertex set cannot leave a hole between two bags it meets. -/
theorem connected_hits_convex {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (V : List Nat)
    (conn : ∀ u ∈ V, ∀ v ∈ V, WalkInside (Adj p) V u v)
    (lo mid hi : Nat) (hl : lo ≤ mid) (hr : mid ≤ hi)
    (hitsLo : Hits p V lo) (hitsHi : Hits p V hi) : Hits p V mid := by
  classical
  by_cases h : Hits p V mid
  · exact h
  · obtain ⟨u, hu, hulo⟩ := hitsLo
    obtain ⟨v, hv, hvhi⟩ := hitsHi
    have left (t : Nat) (ht : u ∈ bagVertices p t) : t < mid := by
      by_cases hlt : t < mid
      · exact hlt
      · have covered := consecutive_bags p u lo mid t hl (by omega) hulo ht
        exact False.elim (h ⟨u, hu, covered⟩)
    have contradiction := walk_stays_left p (conn u hu v hv) mid h left hi hvhi
    omega

private theorem finite_hits {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (V : List Nat) : ∃ b, ∀ t, Hits p V t → t ≤ b := by
  induction V with
  | nil => exact ⟨0, fun _ ⟨_, h, _⟩ => by simp at h⟩
  | cons x xs ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨r, _, hr⟩ := vertex_bag_interval p x
    refine ⟨max b r, ?_⟩
    intro t hit
    obtain ⟨u, hu, ht⟩ := hit
    rcases List.mem_cons.mp hu with e | h
    · subst u
      exact Nat.le_trans ((hr t).mp ht).2 (Nat.le_max_right _ _)
    · exact Nat.le_trans (hb t ⟨u,h,ht⟩) (Nat.le_max_left _ _)

private theorem boundedExtremes (P : Nat → Prop) (M : Nat)
    (w : ∃ t, t ≤ M ∧ P t) :
    ∃ l r, P l ∧ P r ∧ ∀ t, t ≤ M → P t → l ≤ t ∧ t ≤ r := by
  classical
  induction M with
  | zero =>
    obtain ⟨t, ht, hp⟩ := w
    have h : t = 0 := by omega
    subst t
    exact ⟨0,0,hp,hp,fun _ ht _ => ⟨Nat.zero_le _,ht⟩⟩
  | succ m ih =>
    by_cases q : ∃ t, t ≤ m ∧ P t
    · obtain ⟨l,r,hl,hr,bounds⟩ := ih q
      obtain ⟨a,ha,hpa⟩ := q
      by_cases htop : P (m+1)
      · refine ⟨l,m+1,hl,htop,?_⟩
        intro t ht hp
        by_cases hb : t ≤ m
        · exact ⟨(bounds t hb hp).1,ht⟩
        · have hla := (bounds a ha hpa).1
          exact ⟨by omega,ht⟩
      · refine ⟨l,r,hl,hr,?_⟩
        intro t ht hp
        have hne : t ≠ m+1 := fun e => htop (e ▸ hp)
        exact bounds t (by omega) hp
    · obtain ⟨a,ha,hp⟩ := w
      have hlarge : ¬ a ≤ m := fun h => q ⟨a,h,hp⟩
      have htop : P (m+1) := by
        have h : a = m+1 := by omega
        exact h ▸ hp
      refine ⟨m+1,m+1,htop,htop,?_⟩
      intro t ht hp
      have hlarge : ¬ t ≤ m := fun h => q ⟨t,h,hp⟩
      exact ⟨by omega,ht⟩

/-- Each nonempty finite connected set meets bags in a single finite interval. -/
theorem connected_hit_interval {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (V : List Nat) (u : Nat) (hu : u ∈ V)
    (conn : ∀ a ∈ V, ∀ b ∈ V, WalkInside (Adj p) V a b) :
    ∃ l r, l ≤ r ∧ ∀ t, Hits p V t ↔ l ≤ t ∧ t ≤ r := by
  have start : Hits p V u := ⟨u,hu,by simp [bagVertices]⟩
  obtain ⟨M,hM⟩ := finite_hits p V
  obtain ⟨l,r,hl,hr,bounds⟩ := boundedExtremes (Hits p V) M ⟨u,hM u start,start⟩
  exact ⟨l,r,(bounds l (hM l hl) hl).2,fun t =>
    ⟨fun h => bounds t (hM t h) h,
     fun h => connected_hits_convex p V conn l t r h.1 h.2 hl hr⟩⟩

#print axioms connected_hits_convex
#print axioms connected_hit_interval
end ResearchCommons.CappedConnectedBags
