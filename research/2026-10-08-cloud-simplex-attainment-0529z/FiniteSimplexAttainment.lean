import UnifiedLean.G6.CorruptionClasses
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
CLOUD-G6-SOL-ULTRA-20261007. UNCHECKED, outside179.
Construct a closest law in the COORDINATE closure of any nonempty finite-law
image. Compactness/minimizers are DERIVED, not source fields. Equivalence to
the finite-TV neighborhood closure and effective source nets remain separate.
-/
namespace UnifiedLean.G6.FiniteSimplexAttainment

open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.CorruptionClasses
open scoped BigOperators Classical
variable {A : Type*} [Fintype A]

def realLaw (p : PMF A) : A → ℝ := fun a => (p a).toReal

def simplex (A : Type*) [Fintype A] : Set (A → ℝ) :=
  {v | (∀ a, 0 ≤ v a) ∧ ∑ a, v a = 1}

theorem realLaw_mem_simplex (p : PMF A) : realLaw p ∈ simplex A := by
  exact ⟨fun _ => ENNReal.toReal_nonneg, pmf_sum_real p⟩

theorem continuous_sum_coordinates : Continuous (fun v : A → ℝ => ∑ a, v a) :=
  continuous_finsetSum Finset.univ (fun a _ => continuous_apply a)

theorem isClosed_simplex : IsClosed (simplex A) := by
  have hnonneg : IsClosed (⋂ a : A, {v : A → ℝ | 0 ≤ v a}) :=
    isClosed_iInter (fun a => isClosed_le continuous_const (continuous_apply a))
  have hsum : IsClosed {v : A → ℝ | ∑ a, v a = 1} :=
    isClosed_eq continuous_sum_coordinates continuous_const
  have heq : simplex A =
      (⋂ a : A, {v : A → ℝ | 0 ≤ v a}) ∩ {v : A → ℝ | ∑ a, v a = 1} := by
    ext v
    simp [simplex]
  rw [heq]
  exact hnonneg.inter hsum

theorem simplex_subset_unit_cube : simplex A ⊆ Set.Icc (0 : A → ℝ) 1 := by
  intro v hv
  refine ⟨hv.1, ?_⟩
  intro a
  have h := Finset.single_le_sum (fun b (_ : b ∈ Finset.univ) => hv.1 b)
    (Finset.mem_univ a)
  simpa only [hv.2] using h

theorem isCompact_simplex : IsCompact (simplex A) :=
  (isCompact_Icc : IsCompact (Set.Icc (0 : A → ℝ) 1)).of_isClosed_subset
    isClosed_simplex simplex_subset_unit_cube

theorem continuous_tv_coordinates (p : A → ℝ) : Continuous (tv p) := by
  have hsum : Continuous (fun q : A → ℝ => ∑ a, |p a - q a|) :=
    continuous_finsetSum Finset.univ
      (fun a _ => (continuous_const.sub (continuous_apply a)).abs)
  exact hsum.div_const 2

/-- Reconstruct an actual PMF from a closed-simplex coordinate witness. -/
noncomputable def coordinatePMF (v : A → ℝ) (hv : v ∈ simplex A) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (v a)) (by
    have hs : ENNReal.ofReal (∑ a, v a) = ∑ a, ENNReal.ofReal (v a) :=
      ENNReal.ofReal_sum_of_nonneg (fun a _ => hv.1 a)
    rw [← hs, hv.2]
    norm_num)

theorem coordinatePMF_real (v : A → ℝ) (hv : v ∈ simplex A) (a : A) :
    (coordinatePMF v hv a).toReal = v a := by
  change (ENNReal.ofReal (v a)).toReal = v a
  exact ENNReal.toReal_ofReal (hv.1 a)

theorem coordinatePMF_coordinates (v : A → ℝ) (hv : v ∈ simplex A) :
    realLaw (coordinatePMF v hv) = v := by
  funext a
  exact coordinatePMF_real v hv a

def coordinateClosedClass (laws : Set (PMF A)) : Set (PMF A) :=
  {q | realLaw q ∈ closure (realLaw '' laws)}

theorem coordinate_closure_subset_simplex (laws : Set (PMF A)) :
    closure (realLaw '' laws) ⊆ simplex A := by
  apply closure_minimal _ isClosed_simplex
  rintro v ⟨q, _, rfl⟩
  exact realLaw_mem_simplex q

theorem isCompact_coordinate_closure (laws : Set (PMF A)) :
    IsCompact (closure (realLaw '' laws)) :=
  isCompact_simplex.of_isClosed_subset isClosed_closure
    (coordinate_closure_subset_simplex laws)

/-- A closest PMF in the compact coordinate closure is constructed by the
library extreme-value theorem plus exact simplex-to-PMF conversion. -/
theorem exists_closest_coordinate_law (p : PMF A)
    (laws : Set (PMF A)) (hne : laws.Nonempty) :
    ∃ closest ∈ coordinateClosedClass laws,
      ∀ q ∈ coordinateClosedClass laws, pmfTV p closest ≤ pmfTV p q := by
  have hnonempty : (closure (realLaw '' laws)).Nonempty := by
    obtain ⟨q, hq⟩ := hne
    exact ⟨realLaw q, subset_closure ⟨q, hq, rfl⟩⟩
  obtain ⟨v, hv, hmin⟩ := (isCompact_coordinate_closure laws).exists_isMinOn
    hnonempty (continuous_tv_coordinates (realLaw p)).continuousOn
  have hsimplex := coordinate_closure_subset_simplex laws hv
  let closest := coordinatePMF v hsimplex
  have hcoords : realLaw closest = v := coordinatePMF_coordinates v hsimplex
  refine ⟨closest, ?_, ?_⟩
  · change realLaw closest ∈ closure (realLaw '' laws)
    rw [hcoords]
    exact hv
  · intro q hq
    change tv (realLaw p) (realLaw closest) ≤ tv (realLaw p) (realLaw q)
    rw [hcoords]
    exact hmin hq

/-- Sharp class boundary with a DERIVED closest law, for a nonempty image.
This is not the statistical finite-read theorem or an effective distance. -/
theorem coordinate_class_corruption_boundary (p : PMF A)
    (laws : Set (PMF A)) (hne : laws.Nonempty) (beta : ℝ) :
    ∃ closest ∈ coordinateClosedClass laws,
      (∀ q ∈ coordinateClosedClass laws, pmfTV p closest ≤ pmfTV p q) ∧
      (allCorruptionsSeparated p (coordinateClosedClass laws) beta ↔
        2 * beta < pmfTV p closest) := by
  obtain ⟨closest, hc, hmin⟩ := exists_closest_coordinate_law p laws hne
  exact ⟨closest, hc, hmin, closest_wrong_class_boundary p closest _ beta hc hmin⟩

theorem coordinate_closed_class_empty :
    coordinateClosedClass (∅ : Set (PMF A)) = ∅ := by
  ext q
  simp [coordinateClosedClass]

#print axioms realLaw_mem_simplex
#print axioms continuous_sum_coordinates
#print axioms isClosed_simplex
#print axioms simplex_subset_unit_cube
#print axioms isCompact_simplex
#print axioms continuous_tv_coordinates
#print axioms coordinatePMF_real
#print axioms coordinatePMF_coordinates
#print axioms coordinate_closure_subset_simplex
#print axioms isCompact_coordinate_closure
#print axioms exists_closest_coordinate_law
#print axioms coordinate_class_corruption_boundary
#print axioms coordinate_closed_class_empty

end UnifiedLean.G6.FiniteSimplexAttainment
