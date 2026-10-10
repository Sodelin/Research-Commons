import G3BernoulliDerivatives

/-!
Regression draft for the corrected G3 rare-node partition. Contributor: dot,
10 October 2026. UNCOMPILED. Intended for the existing connectedResearch package,
not a separate Lake project. The existing COMMON Bernoulli factor is reused.
These propositions supply only the exhaustive partition; analytic tail estimates,
certificate production and the p -> 1 limiting diagnostic remain separate.
Here p is the COMMON mixture probability, not the G4 parameter g * (1-g).
-/
namespace GProgram.G3.AllResidue.WeakClassPartition

/-- Predicate on the existing real Bernoulli parameters, not a new source type. -/
def strictPair (p q : ℝ) : Prop := 0 < p ∧ p < 1 ∧ 0 < q ∧ q < 1

noncomputable def odds (p : ℝ) : ℝ := p / (1 - p)

/-- A rare-node class requires BOTH node membership and the small-odds bound. -/
def rare (I : Set ℝ) (z0 p q : ℝ) : Prop :=
  strictPair p q ∧ q ∈ I ∧ odds p ≤ z0

/-- Every other strict pair belongs to the outside class, including large odds. -/
def outside (I J : Set ℝ) (z0 p q : ℝ) : Prop :=
  strictPair p q ∧ ¬ rare I z0 p q ∧ ¬ rare J z0 p q

theorem rare_iff (I : Set ℝ) (z0 p q : ℝ) :
    rare I z0 p q ↔ strictPair p q ∧ q ∈ I ∧ odds p ≤ z0 := Iff.rfl

theorem coverage (I J : Set ℝ) (z0 p q : ℝ) (hs : strictPair p q) :
    rare I z0 p q ∨ rare J z0 p q ∨ outside I J z0 p q := by
  classical
  by_cases hi : rare I z0 p q
  · exact Or.inl hi
  · by_cases hj : rare J z0 p q
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr ⟨hs, hi, hj⟩)

theorem rare_disjoint {I J : Set ℝ} (hIJ : Disjoint I J)
    {z0 p q : ℝ} (hi : rare I z0 p q) : ¬ rare J z0 p q := by
  intro hj
  exact Set.disjoint_left.mp hIJ hi.2.1 hj.2.1

theorem rare_left_not_outside {I J : Set ℝ} {z0 p q : ℝ}
    (hi : rare I z0 p q) : ¬ outside I J z0 p q := by
  intro ho
  exact ho.2.1 hi

theorem rare_right_not_outside {I J : Set ℝ} {z0 p q : ℝ}
    (hj : rare J z0 p q) : ¬ outside I J z0 p q := by
  intro ho
  exact ho.2.2 hj

theorem outside_of_large_odds (I J : Set ℝ) {z0 p q : ℝ}
    (hs : strictPair p q) (hz : z0 < odds p) : outside I J z0 p q := by
  refine ⟨hs, ?_, ?_⟩
  · intro hi
    exact (not_le_of_gt hz) hi.2.2
  · intro hj
    exact (not_le_of_gt hz) hj.2.2

/-- Interval membership alone cannot move a large-odds pair into a rare class. -/
theorem outside_even_at_node (I J : Set ℝ) {z0 p q : ℝ}
    (hs : strictPair p q) (_hq : q ∈ I) (hz : z0 < odds p) :
    outside I J z0 p q := outside_of_large_odds I J hs hz

/-- The partition's real parameters feed the already accepted source factor. -/
theorem factor_positive (n : ℕ) {p q : ℝ} (hs : strictPair p q) :
    0 < bernoulliFactor n p q :=
  bernoulli_factor_pos hs.1 hs.2.1 hs.2.2.1

#print axioms coverage
#print axioms rare_disjoint
#print axioms rare_left_not_outside
#print axioms rare_right_not_outside
#print axioms outside_of_large_odds
#print axioms outside_even_at_node
#print axioms factor_positive

end GProgram.G3.AllResidue.WeakClassPartition
