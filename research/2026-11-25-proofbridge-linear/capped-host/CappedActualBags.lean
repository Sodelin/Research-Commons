import Lean
import SamuelAlexanderResearch.InfiniteConservation

namespace ResearchCommons.CappedActualBags
open PopulationCounting InfiniteConservation

def outgoingAcross {k d : Nat} (p : InfiniteLabeledPopulation k d) (cut u : Nat) : Nat :=
  sumBelow (p.childSupport u) (fun v => if cut ≤ v then edgeBit (p.edge u v) else 0)

/-- The current vertex plus earlier vertices with a child on or beyond the cut. -/
def bagVertices {k d : Nat} (p : InfiniteLabeledPopulation k d) (cut : Nat) : List Nat :=
  cut :: ((List.range cut).filter (fun u => decide (0 < outgoingAcross p cut u)))

private theorem prefix_filter_count (count : Nat → Nat) (n : Nat) :
    ((List.range n).filter (fun u => decide (0 < count u))).length ≤ sumBelow n count := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, sumBelow_succ]
    by_cases h : 0 < count n
    · simp [h]
      omega
    · simp [h]
      omega

/-- Actual crossing width implies the advertised bag-width bound. -/
theorem bag_width {k : Nat} (p : InfiniteLabeledPopulation k k) (cut : Nat) :
    (bagVertices p cut).length ≤ k * fullRootCount p + 1 := by
  have h := prefix_filter_count (outgoingAcross p cut) cut
  change ((List.range cut).filter (fun u => decide (0 < outgoingAcross p cut u))).length ≤
    InfiniteConservation.crossingCount p cut at h
  have hc := crossing_upper p cut
  simp only [bagVertices, List.length_cons]
  omega

/-- The actual endpoints of each edge appear together in its target bag. -/
theorem edge_in_target_bag {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (u v : Nat) (he : (p.edge u v).isSome = true) :
    u ∈ bagVertices p v ∧ v ∈ bagVertices p v := by
  have huv : u < v := p.birth_order u v he
  have hv : v < p.childSupport u := by
    by_cases hh : v < p.childSupport u
    · exact hh
    · have hn := p.no_children_after u v (by omega)
      simp [hn] at he
  have term := term_le_sumBelow (fun j => if v ≤ j then edgeBit (p.edge u j) else 0) hv
  have positive : 0 < outgoingAcross p v u := by
    have hp : edgeBit (p.edge u v) = 1 := by simp [edgeBit, he]
    have hle : 1 ≤ outgoingAcross p v u := by
      simpa only [Nat.le_refl, if_true, hp, outgoingAcross] using term
    exact Nat.lt_of_lt_of_le (by decide : 0 < 1) hle
  have hu : u ∈ (List.range v).filter (fun a => decide (0 < outgoingAcross p v a)) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr huv, by simp [positive]⟩
  exact ⟨List.mem_cons_of_mem _ hu, by simp [bagVertices]⟩

private theorem across_mono {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (u i j : Nat) (h : i ≤ j) : outgoingAcross p j u ≤ outgoingAcross p i u := by
  apply sumBelow_mono
  intro v _
  by_cases hj : j ≤ v
  · have hi := Nat.le_trans h hj
    simp [hj, hi]
  · simp [hj]

private theorem mem_bag_iff {k d : Nat} (p : InfiniteLabeledPopulation k d) (u t : Nat) :
    u ∈ bagVertices p t ↔ u = t ∨ (u < t ∧ 0 < outgoingAcross p t u) := by
  simp [bagVertices]

/-- Membership is consecutive between any two cuts containing the vertex. -/
theorem consecutive_bags {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (u i j t : Nat) (hij : i ≤ j) (hjt : j ≤ t)
    (hi : u ∈ bagVertices p i) (ht : u ∈ bagVertices p t) : u ∈ bagVertices p j := by
  have hu : u ≤ i := by
    rcases (mem_bag_iff p u i).mp hi with h | h <;> omega
  apply (mem_bag_iff p u j).mpr
  by_cases h : u = j
  · exact Or.inl h
  · right
    have huj : u < j := by omega
    refine ⟨huj, ?_⟩
    rcases (mem_bag_iff p u t).mp ht with he | hc
    · omega
    · exact Nat.lt_of_lt_of_le hc.2 (across_mono p u j t hjt)

private theorem latest_of_bounded (P : Nat → Prop) (M : Nat)
    (existsMem : ∃ x, x ≤ M ∧ P x) :
    ∃ last, last ≤ M ∧ P last ∧ ∀ y, y ≤ M → P y → y ≤ last := by
  classical
  induction M with
  | zero =>
    obtain ⟨x, hx, hp⟩ := existsMem
    have he : x = 0 := by omega
    subst x
    exact ⟨0, Nat.le_refl _, hp, fun y hy _ => hy⟩
  | succ M ih =>
    by_cases top : P (M + 1)
    · exact ⟨M+1, Nat.le_refl _, top, fun y hy _ => hy⟩
    · have step (y : Nat) (hy : y ≤ M+1) (hp : P y) : y ≤ M := by
        by_cases hy' : y = M+1
        · subst y
          exact False.elim (top hp)
        · omega
      obtain ⟨x, hx, hp⟩ := existsMem
      obtain ⟨last, hn, hlast, all⟩ := ih ⟨x, step x hx hp, hp⟩
      exact ⟨last, by omega, hlast, fun y hy hP => all y (step y hy hP) hP⟩

/-- Each vertex occurs on exactly one nonempty, finite interval of actual bags. -/
theorem vertex_bag_interval {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (u : Nat) : ∃ last, u ≤ last ∧
      ∀ t, u ∈ bagVertices p t ↔ u ≤ t ∧ t ≤ last := by
  let cap := max u (p.childSupport u)
  have atSelf : u ∈ bagVertices p u := (mem_bag_iff p u u).mpr (Or.inl rfl)
  have bounded (t : Nat) (ht : u ∈ bagVertices p t) : t ≤ cap := by
    rcases (mem_bag_iff p u t).mp ht with he | h
    · rw [← he]
      exact Nat.le_max_left _ _
    · by_cases hb : t ≤ cap
      · exact hb
      · have zero : outgoingAcross p t u = 0 := by
          unfold outgoingAcross
          calc
            _ = sumBelow (p.childSupport u) (fun _ => 0) := by
              apply sumBelow_congr
              intro v hv
              have hs : p.childSupport u ≤ cap := Nat.le_max_right _ _
              have hn : ¬ t ≤ v := by omega
              simp [hn]
            _ = 0 := by simp
        have hp := h.2
        omega
  obtain ⟨last, _, hlast, maximal⟩ :=
    latest_of_bounded (fun t => u ∈ bagVertices p t) cap ⟨u, Nat.le_max_left _ _, atSelf⟩
  have hstart := maximal u (bounded u atSelf) atSelf
  refine ⟨last, hstart, fun t => ⟨?_, ?_⟩⟩
  · intro ht
    have hmin : u ≤ t := by
      rcases (mem_bag_iff p u t).mp ht with h | h <;> omega
    exact ⟨hmin, maximal t (bounded t ht) ht⟩
  · intro ht
    exact consecutive_bags p u u t last ht.1 ht.2 atSelf hlast

/-- Dropping the current-vertex contribution would already fail at the first bag. -/
theorem first_bag_nonempty {k d : Nat} (p : InfiniteLabeledPopulation k d) :
    (bagVertices p 0).length = 1 := by simp [bagVertices]

#print axioms bag_width
#print axioms edge_in_target_bag
#print axioms consecutive_bags
#print axioms vertex_bag_interval
#print axioms first_bag_nonempty

end ResearchCommons.CappedActualBags
