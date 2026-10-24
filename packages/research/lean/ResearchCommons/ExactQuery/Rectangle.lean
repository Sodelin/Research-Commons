import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! Geometric primitive of the OLD complete-support supplied-circle search.
Positions are natural numbers in the supplied circle. This is NOT original
network admission, unknown-order learning or the complete query bound.
The OLD source theorem supplies displayed-tree edge witnesses separately.
-/
namespace ResearchCommons.ExactQuery.Rectangle
set_option autoImplicit false

def Inside (i j x : ℕ) : Prop := i < x ∧ x ≤ j

/-- Bit4 for a<b<c<d: ad|bc, with either side of the bipartition. -/
def DisplaysADBC (i j a b c d : ℕ) : Prop :=
  (Inside i j a ∧ Inside i j d ∧ ¬ Inside i j b ∧ ¬ Inside i j c) ∨
  (¬ Inside i j a ∧ ¬ Inside i j d ∧ Inside i j b ∧ Inside i j c)

/-- Bit1: ab|cd, again independent of which shore is stored. -/
def DisplaysABCD (i j a b c d : ℕ) : Prop :=
  (Inside i j a ∧ Inside i j b ∧ ¬ Inside i j c ∧ ¬ Inside i j d) ∨
  (¬ Inside i j a ∧ ¬ Inside i j b ∧ Inside i j c ∧ Inside i j d)

def InRectangle (a b c d i j : ℕ) : Prop := a ≤ i ∧ i < b ∧ c ≤ j ∧ j < d

/-- Literal two-gap/complete-quartet rectangle equivalence for ALL sizes.
This does not suppose the desired recovery output or a fitted probability. -/
theorem interval_displays_iff_rectangle (a b c d i j : ℕ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    DisplaysADBC i j a b c d ↔ InRectangle a b c d i j := by
  unfold DisplaysADBC Inside InRectangle
  omega

/-- Taking the UNION of complete split witnesses preserves the existential
rectangle predicate. Different answers need not be realized in one tree. -/
theorem split_union_rectangle_oracle (S : Finset (ℕ × ℕ)) (a b c d : ℕ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (∃ g ∈ S, DisplaysADBC g.1 g.2 a b c d) ↔
      ∃ g ∈ S, InRectangle a b c d g.1 g.2 := by
  constructor
  · rintro ⟨g,hg,h⟩
    exact ⟨g,hg,(interval_displays_iff_rectangle a b c d g.1 g.2 hab hbc hcd).mp h⟩
  · rintro ⟨g,hg,h⟩
    exact ⟨g,hg,(interval_displays_iff_rectangle a b c d g.1 g.2 hab hbc hcd).mpr h⟩

theorem rectangle_left_partition (a m b c d i j : ℕ) (ham : a ≤ m) (hmb : m ≤ b) :
    InRectangle a b c d i j ↔
      InRectangle a m c d i j ∨ InRectangle m b c d i j := by
  unfold InRectangle
  omega

theorem rectangle_right_partition (a b c m d i j : ℕ) (hcm : c ≤ m) (hmd : m ≤ d) :
    InRectangle a b c d i j ↔
      InRectangle a b c m i j ∨ InRectangle a b m d i j := by
  unfold InRectangle
  omega

theorem rectangle_singleton (a c i j : ℕ) :
    InRectangle a (a+1) c (c+1) i j ↔ i = a ∧ j = c := by
  unfold InRectangle
  omega

/-- The OLD special wrap query is a ONE-cell test for (k,n-1).
All requested quartet positions are distinct under these literal bounds. -/
theorem wrap_query_singleton (n k i j : ℕ)
    (hk : 1 ≤ k) (hkn : k+2 < n) (hij : i < j) (hjn : j < n) :
    DisplaysABCD i j 0 k (k+1) (n-1) ↔ i = k ∧ j = n-1 := by
  unfold DisplaysABCD Inside
  omega


/-- Non-wrap nonadjacent gap pairs in the literal half-open interval. -/
def Triangle (l r i j : ℕ) : Prop := l ≤ i ∧ i+2 ≤ j ∧ j < r

/-- The OLD two cross-half roots plus recursive triangles cover exactly the
parent triangle. Empty cross-half rectangles are allowed and contain no cell. -/
theorem triangle_mid_partition (l m r i j : ℕ) (hlm : l < m) (hmr : m < r) :
    Triangle l r i j ↔
      InRectangle l (m-1) m r i j ∨
      InRectangle (m-1) m (m+1) r i j ∨
      Triangle l m i j ∨ Triangle m r i j := by
  unfold Triangle InRectangle
  omega

theorem triangle_mid_disjoint (l m r i j : ℕ) :
    (InRectangle l (m-1) m r i j →
      ¬ InRectangle (m-1) m (m+1) r i j ∧
      ¬ Triangle l m i j ∧ ¬ Triangle m r i j) ∧
    (InRectangle (m-1) m (m+1) r i j →
      ¬ Triangle l m i j ∧ ¬ Triangle m r i j) ∧
    (Triangle l m i j → ¬ Triangle m r i j) := by
  unfold InRectangle Triangle
  omega

/-- Literal coverage of the OLD recursively emitted root rectangles.
This is geometry, not an oracle that inspects unknown source splits. -/
def SeedCovered (l r i j : ℕ) : Prop :=
  if small : r-l ≤ 2 then False
  else
    let m := l+(r-l)/2
    InRectangle l (m-1) m r i j ∨
      InRectangle (m-1) m (m+1) r i j ∨
      SeedCovered l m i j ∨ SeedCovered m r i j
termination_by r-l
decreasing_by all_goals omega

/-- ALL finite recursion depths, rather than a bounded root enumeration. -/
theorem seed_covered_iff_triangle (l r i j : ℕ) :
    SeedCovered l r i j ↔ Triangle l r i j := by
  have aux : ∀ n l r : ℕ, r-l=n →
      (SeedCovered l r i j ↔ Triangle l r i j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro l r hn
        rw [SeedCovered]
        by_cases small : r-l ≤ 2
        · rw [dif_pos small]
          unfold Triangle
          omega
        · rw [dif_neg small]
          let m := l+(r-l)/2
          have hlm : l < m := by dsimp [m]; omega
          have hmr : m < r := by dsimp [m]; omega
          have leftSmall : m-l < n := by dsimp [m]; omega
          have rightSmall : r-m < n := by dsimp [m]; omega
          change (InRectangle l (m-1) m r i j ∨
            InRectangle (m-1) m (m+1) r i j ∨
            SeedCovered l m i j ∨ SeedCovered m r i j) ↔ Triangle l r i j
          rw [ih (m-l) leftSmall l m rfl, ih (r-m) rightSmall m r rfl]
          exact (triangle_mid_partition l m r i j hlm hmr).symm
  exact aux (r-l) l r rfl

def CandidateSplit (n i j : ℕ) : Prop :=
  i+2 ≤ j ∧ j < n ∧ ¬ (i=0 ∧ j=n-1)

def WrapCandidate (n i j : ℕ) : Prop :=
  1 ≤ i ∧ i+2 < n ∧ j=n-1

/-- Every original nontrivial two-gap candidate is covered by the actual
non-wrap root recursion or exactly one of the OLD special wrap queries. -/
theorem all_candidates_covered (n i j : ℕ) (hn : 4 ≤ n) :
    CandidateSplit n i j ↔
      SeedCovered 0 (n-1) i j ∨ WrapCandidate n i j := by
  rw [seed_covered_iff_triangle]
  unfold CandidateSplit Triangle WrapCandidate
  omega

theorem wrap_and_nonwrap_disjoint (n i j : ℕ) :
    ¬ (SeedCovered 0 (n-1) i j ∧ WrapCandidate n i j) := by
  rw [seed_covered_iff_triangle]
  unfold Triangle WrapCandidate
  omega

theorem emitted_roots_have_distinct_query_positions (l m r : ℕ)
    (hlm : l < m) (hmr : m < r) :
    (l < m-1 → l < m-1 ∧ m-1 < m ∧ m < r) ∧
    (m+1 < r → m-1 < m ∧ m < m+1 ∧ m+1 < r) := by
  omega

end ResearchCommons.ExactQuery.Rectangle
