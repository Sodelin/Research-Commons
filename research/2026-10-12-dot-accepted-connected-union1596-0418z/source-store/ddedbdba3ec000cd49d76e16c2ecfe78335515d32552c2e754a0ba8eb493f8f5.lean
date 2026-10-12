import G3CriticalSliceCoefficientData
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Real.Basic

/-! Characteristic-zero lifting of the concrete polynomial coprimality
certificate. This module does not yet bind these coefficient lists to the
actual Bernoulli source slice polynomials. -/
noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

instance : Fact (Nat.Prime 101) := ⟨by decide⟩

abbrev reduce101 : ℤ →+* ZMod 101 := Int.castRingHom (ZMod 101)

def H3 : Polynomial ℤ := ofCoeffs h3Coeffs
def H5 : Polynomial ℤ := ofCoeffs h5Coeffs

theorem H3_natDegree : H3.natDegree = 147 :=
  natDegree_ofCoeffs_eq h3Coeffs 147 h3_length h3_last_ne_zero

theorem H5_natDegree : H5.natDegree = 147 :=
  natDegree_ofCoeffs_eq h5Coeffs 147 h5_length h5_last_ne_zero

theorem H3_map : H3.map reduce101 = ofCoeffs h3ModCoeffs := by
  rw [H3, map_ofCoeffs, modular_map_3]

theorem H5_map : H5.map reduce101 = ofCoeffs h5ModCoeffs := by
  rw [H5, map_ofCoeffs, modular_map_5]

theorem H3_map_natDegree : (H3.map reduce101).natDegree = 147 := by
  rw [H3_map]
  apply natDegree_ofCoeffs_eq _ _ h3_mod_length
  rw [h3_mod_last]
  decide

theorem H5_map_natDegree : (H5.map reduce101).natDegree = 147 := by
  rw [H5_map]
  apply natDegree_ofCoeffs_eq _ _ h5_mod_length
  rw [h5_mod_last]
  decide

theorem reduced_coprime : IsCoprime (H3.map reduce101) (H5.map reduce101) := by
  rw [H3_map, H5_map]
  exact ⟨ofCoeffs sModCoeffs, ofCoeffs tModCoeffs,
    polynomial_identity_of_coefficient_identity _ _ _ _ 293 modular_bezout⟩

theorem integer_resultant_ne_zero : Polynomial.resultant H3 H5 147 147 ≠ 0 := by
  have hn := Polynomial.resultant_ne_zero (H3.map reduce101) (H5.map reduce101) reduced_coprime
  rw [H3_map_natDegree, H5_map_natDegree, Polynomial.resultant_map_map] at hn
  intro hz
  apply hn
  rw [hz, map_zero]

theorem quotients_no_common_real_root (r : ℝ) :
    ¬ ((H3.map (Int.castRingHom ℝ)).eval r = 0 ∧
       (H5.map (Int.castRingHom ℝ)).eval r = 0) := by
  intro hr
  have hd3 : (H3.map (Int.castRingHom ℝ)).natDegree ≤ 147 := by
    exact (Polynomial.natDegree_map_le).trans (by rw [H3_natDegree])
  have hd5 : (H5.map (Int.castRingHom ℝ)).natDegree ≤ 147 := by
    exact (Polynomial.natDegree_map_le).trans (by rw [H5_natDegree])
  obtain ⟨u,v,_,_,he⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    (H3.map (Int.castRingHom ℝ)) (H5.map (Int.castRingHom ℝ)) hd3 hd5 (by decide)
  have heval := congrArg (fun f : Polynomial ℝ => f.eval r) he
  simp only [Polynomial.eval_add, Polynomial.eval_mul, hr.1, hr.2,
    zero_mul, zero_add, Polynomial.eval_C, Polynomial.resultant_map_map] at heval
  have hz : Polynomial.resultant H3 H5 147 147 = 0 := by
    have hc : ((Polynomial.resultant H3 H5 147 147 : ℤ) : ℝ) = 0 := heval.symm
    exact_mod_cast hc
  exact integer_resultant_ne_zero hz

#print axioms integer_resultant_ne_zero
#print axioms quotients_no_common_real_root
end GProgram.G3.CriticalCertificates
