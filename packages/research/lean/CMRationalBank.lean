import CMFoundations
import RationalBankMoments
import Mathlib.Logic.Function.Basic

/-! A typed receiver for an ALREADY grouped distinct rational bank.
This does not compute the positive image or refine a native grouping program.
The imported CM structure is the exact existing accepted component source. -/

namespace Astra.CommonMoment.RationalBank

open scoped BigOperators

noncomputable def castWeight (w : ℚ → ℚ) : ℝ → ℝ :=
  Function.extend (fun q : ℚ => (q : ℝ)) (fun q => (w q : ℝ)) (fun _ => 0)

theorem castWeight_at (w : ℚ → ℚ) (q : ℚ) :
    castWeight w (q : ℝ) = (w q : ℝ) :=
  Rat.cast_injective.extend_apply _ _ q

theorem cast_nodes_sum (S : Finset ℚ) (f : ℝ → ℝ) :
    (∑ x ∈ S.image (fun q : ℚ => (q : ℝ)), f x) = ∑ q ∈ S, f (q : ℝ) := by
  classical
  exact Finset.sum_image (fun a _ b _ h => Rat.cast_injective h)

/-- No normalization or removal is performed here: the caller supplies exactly
the distinct positive-mass rational scalar image and its grouped weights. -/
noncomputable def fromGroupedRationals (S : Finset ℚ) (w : ℚ → ℚ)
    (hx : ∀ q ∈ S, 0 < q) (hw : ∀ q ∈ S, 0 < w q)
    (hmass : ∑ q ∈ S, w q = 1) : FinitePositiveLaw := by
  classical
  refine { nodes := S.image (fun q : ℚ => (q : ℝ))
           weight := castWeight w
           node_pos := ?_
           weight_pos := ?_
           mass_one := ?_ }
  · intro x hxmem
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hxmem
    exact_mod_cast hx q hq
  · intro x hxmem
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hxmem
    rw [castWeight_at]
    exact_mod_cast hw q hq
  · rw [cast_nodes_sum]
    simp only [castWeight_at]
    calc
      _ = ((∑ q ∈ S, w q : ℚ) : ℝ) := (map_sum (Rat.castHom ℝ) w S).symm
      _ = 1 := by rw [hmass]; norm_num

theorem fromGroupedRationals_moment (S : Finset ℚ) (w : ℚ → ℚ)
    (hx : ∀ q ∈ S, 0 < q) (hw : ∀ q ∈ S, 0 < w q)
    (hmass : ∑ q ∈ S, w q = 1) (n : ℕ) :
    moment (fromGroupedRationals S w hx hw hmass) n =
      ((∑ q ∈ S, w q * q^n : ℚ) : ℝ) := by
  classical
  change (∑ x ∈ S.image (fun q : ℚ => (q : ℝ)), castWeight w x*x^n) = _
  rw [cast_nodes_sum]
  simp only [castWeight_at]
  have h := map_sum (Rat.castHom ℝ) (fun q => w q*q^n) S
  simpa only [Rat.coe_castHom,Rat.cast_mul,Rat.cast_pow] using h.symm

/-- The CM positive-axis constructor does not itself impose an upper bound.
This separate survival fact retains the old weighted-square receiver domain. -/
theorem fromGroupedRationals_survival_and_sparse_moments
    (S : Finset ℚ) (w : ℚ → ℚ)
    (hx : ∀ q ∈ S, 0 < q) (hx1 : ∀ q ∈ S, q ≤ 1)
    (hw : ∀ q ∈ S, 0 < w q) (hmass : ∑ q ∈ S, w q = 1) :
    let mu := fromGroupedRationals S w hx hw hmass
    (∀ x ∈ mu.nodes, x ≤ 1) ∧
      ∀ k : ℕ, moment mu (k.choose 2) =
        ((∑ q ∈ S, w q*q^(k.choose 2) : ℚ) : ℝ) := by
  classical
  dsimp only
  refine ⟨?_,fun k => fromGroupedRationals_moment S w hx hw hmass (k.choose 2)⟩
  intro x hxmem
  change x ∈ S.image (fun q : ℚ => (q : ℝ)) at hxmem
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hxmem
  exact_mod_cast hx1 q hq

end Astra.CommonMoment.RationalBank
