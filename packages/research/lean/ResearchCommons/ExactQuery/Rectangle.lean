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

end ResearchCommons.ExactQuery.Rectangle
