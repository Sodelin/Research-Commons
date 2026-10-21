import G4WholeProfileDetermination
import CMFoundations

/-! Semantic packaging of an existing finite PMF, without a new grouping
algorithm. The physical import context uses the original sparse supplier
instead of importing the duplicate extracted CMSparseSupplier. -/

namespace Astra.CommonMoment.FinitePMF

open scoped BigOperators Classical
open DotG4.ActualPositiveGridUniqueness DotG4.WholeProfileDetermination

variable {ι : Type*} [Fintype ι]

noncomputable def positiveImage (p : PMF ι) (x : ι → ℝ) : Finset ℝ :=
  Finset.univ.image (fun a : {i : ι // p i ≠ 0} => x a.val)

noncomputable def groupedWeight (p : PMF ι) (x : ι → ℝ) : ℝ → ℝ :=
  gridWeight (fun a => (positiveSupportPMF p a).toReal)
    (fun a => x a.val)

theorem grouped_moment (p : PMF ι) (x : ι → ℝ) (n : ℕ) :
    (∑ a ∈ positiveImage p x, groupedWeight p x a * a ^ n) =
      ∑ i, (p i).toReal * x i ^ n := by
  classical
  have h := gridWeight_moment (positiveImage p x)
    (fun a => (positiveSupportPMF p a).toReal) (fun a => x a.val)
    (fun a => Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩) n
  rw [positiveSupportPMF_sum p (fun i => x i ^ n)] at h
  calc
    _ = ∑ a : positiveImage p x,
        groupedWeight p x a * (a : ℝ) ^ n :=
      (Finset.sum_coe_sort (positiveImage p x)
        (fun a => groupedWeight p x a * a ^ n)).symm
    _ = _ := h

theorem grouped_weight_positive (p : PMF ι) (x : ι → ℝ)
    (a : ℝ) (ha : a ∈ positiveImage p x) :
    0 < groupedWeight p x a := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset {j : ι // p j ≠ 0}))
    (f := fun j => if x j.val = x i.val then
      (positiveSupportPMF p j).toReal else 0)
    (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
  exact lt_of_lt_of_le (positiveSupportPMF_positive p i)
    (by simpa [groupedWeight, gridWeight] using h)

theorem grouped_mass_one (p : PMF ι) (x : ι → ℝ) :
    (∑ a ∈ positiveImage p x, groupedWeight p x a) = 1 := by
  classical
  have hsum : (∑ i, (p i).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun i _ => p.apply_ne_top i)]
    simpa only [tsum_fintype, ENNReal.toReal_one] using
      congrArg ENNReal.toReal p.tsum_coe
  calc
    _ = ∑ i, (p i).toReal := by
      simpa only [pow_zero, mul_one] using grouped_moment p x 0
    _ = 1 := hsum

noncomputable def fromFinitePMF (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) : FinitePositiveLaw where
  nodes := positiveImage p x
  weight := groupedWeight p x
  node_pos := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hx i.val i.property
  weight_pos := grouped_weight_positive p x
  mass_one := grouped_mass_one p x

theorem fromFinitePMF_moment (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) (n : ℕ) :
    moment (fromFinitePMF p x hx) n = ∑ i, (p i).toReal * x i ^ n :=
  grouped_moment p x n

theorem fromFinitePMF_sparse_moment (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) (k : ℕ) :
    moment (fromFinitePMF p x hx) (k.choose 2) = finiteBankMoment p x k :=
  fromFinitePMF_moment p x hx (k.choose 2)

theorem fromFinitePMF_nodes_Ioc (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i)
    (hx1 : ∀ i, p i ≠ 0 → x i ≤ 1) :
    ∀ a ∈ (fromFinitePMF p x hx).nodes, a ∈ Set.Ioc (0 : ℝ) 1 := by
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨hx i.val i.property, hx1 i.val i.property⟩

theorem fromFinitePMF_weight_mapped_mass (p : PMF ι) (x : ι → ℝ)
    (hx : ∀ i, p i ≠ 0 → 0 < x i) (a : ℝ) :
    (fromFinitePMF p x hx).weight a = ((p.map x) a).toReal := by
  change gridWeight (fun i => (positiveSupportPMF p i).toReal)
    (fun i => x i.val) a = _
  rw [gridWeight_eq_mapped_mass, positiveSupportPMF_map]

end Astra.CommonMoment.FinitePMF
