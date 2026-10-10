import FiniteSimplexAttainment
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
CLOUD-G6-SOL-ULTRA-20261007. UNCHECKED, outside179.
Finite-TV neighborhoods and the ordinary real-coordinate image closure are
the SAME class. Quantitative norm bounds handle an empty index type without
division by its cardinality. No effective/source-net conclusion is assumed.
-/
namespace UnifiedLean.G6.CoordinateTVClosure

open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open UnifiedLean.G6.CorruptionClasses UnifiedLean.G6.FiniteSimplexAttainment
open scoped BigOperators Classical
variable {A : Type*} [Fintype A]

theorem coordinate_dist_le_twice_tv (p q : PMF A) :
    dist (realLaw p) (realLaw q) ≤ 2 * pmfTV p q := by
  apply (dist_pi_le_iff (mul_nonneg (by norm_num) (pmfTV_nonneg p q))).mpr
  intro a
  have hs := Finset.single_le_sum (fun b (_ : b ∈ Finset.univ) =>
    abs_nonneg (realLaw p b - realLaw q b)) (Finset.mem_univ a)
  rw [Real.dist_eq]
  change |realLaw p a - realLaw q a| ≤
    2 * ((∑ b, |realLaw p b - realLaw q b|) / 2)
  linarith

theorem tv_le_card_add_one_dist (p q : PMF A) :
    pmfTV p q ≤ ((Fintype.card A : ℝ) + 1) * dist (realLaw p) (realLaw q) := by
  have hs : (∑ a, |realLaw p a - realLaw q a|) ≤
      (Fintype.card A : ℝ) * dist (realLaw p) (realLaw q) := by
    calc
      _ ≤ ∑ a : A, dist (realLaw p) (realLaw q) := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [Real.dist_eq] using dist_le_pi_dist (realLaw p) (realLaw q) a
      _ = _ := by simp
  have hn : 0 ≤ (Fintype.card A : ℝ) := by positivity
  have hd : 0 ≤ dist (realLaw p) (realLaw q) := dist_nonneg
  change (∑ a, |realLaw p a - realLaw q a|) / 2 ≤ _
  nlinarith [mul_nonneg hn hd]

/-- The two earlier explicitly distinguished closure definitions coincide
by finite-dimensional norm bounds; no compactness premise is supplied. -/
theorem tvClosure_eq_coordinateClosedClass (laws : Set (PMF A)) :
    tvClosure laws = coordinateClosedClass laws := by
  ext p
  constructor
  · intro hp
    change realLaw p ∈ closure (realLaw '' laws)
    apply Metric.mem_closure_iff.mpr
    intro epsilon hepsilon
    obtain ⟨q, hq, hpq⟩ := hp (epsilon / 2) (by linarith)
    refine ⟨realLaw q, ⟨q, hq, rfl⟩, ?_⟩
    have hbound := coordinate_dist_le_twice_tv p q
    linarith
  · intro hp epsilon hepsilon
    change realLaw p ∈ closure (realLaw '' laws) at hp
    have hc : 0 < (Fintype.card A : ℝ) + 1 := by positivity
    obtain ⟨v, ⟨q, hq, rfl⟩, hpq⟩ := Metric.mem_closure_iff.mp hp
      (epsilon / ((Fintype.card A : ℝ) + 1)) (div_pos hepsilon hc)
    refine ⟨q, hq, ?_⟩
    have hbound := tv_le_card_add_one_dist p q
    have hsmall := (lt_div_iff₀ hc).mp hpq
    nlinarith

/-- Compact coordinate attainment now supplies an actual closest PMF in
the finite-TV closure. Nonemptiness is explicit; empty images are separate. -/
theorem exists_closest_tv_closure (p : PMF A)
    (laws : Set (PMF A)) (hne : laws.Nonempty) :
    ∃ closest ∈ tvClosure laws,
      ∀ q ∈ tvClosure laws, pmfTV p closest ≤ pmfTV p q := by
  simpa only [tvClosure_eq_coordinateClosedClass] using
    exists_closest_coordinate_law p laws hne

theorem sharp_tv_closure_corruption_boundary (p : PMF A)
    (laws : Set (PMF A)) (hne : laws.Nonempty) (beta : ℝ) :
    ∃ closest ∈ tvClosure laws,
      (∀ q ∈ tvClosure laws, pmfTV p closest ≤ pmfTV p q) ∧
      (allCorruptionsSeparated p (tvClosure laws) beta ↔
        2 * beta < pmfTV p closest) := by
  simpa only [tvClosure_eq_coordinateClosedClass] using
    coordinate_class_corruption_boundary p laws hne beta

#print axioms coordinate_dist_le_twice_tv
#print axioms tv_le_card_add_one_dist
#print axioms tvClosure_eq_coordinateClosedClass
#print axioms exists_closest_tv_closure
#print axioms sharp_tv_closure_corruption_boundary

end UnifiedLean.G6.CoordinateTVClosure
