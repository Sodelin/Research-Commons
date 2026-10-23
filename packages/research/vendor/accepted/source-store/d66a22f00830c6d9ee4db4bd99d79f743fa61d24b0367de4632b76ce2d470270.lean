import G3CriticalSourceArrayBinding

noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
open scoped BigOperators

theorem fin6_sum_expansion (f : Fin 6 → Polynomial ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ, add_assoc]

theorem fin6_prod_erase_0 (f : Fin 6 → Polynomial ℝ) :
    ∏ j ∈ Finset.univ.erase (0:Fin 6), f j = f 1 * f 2 * f 3 * f 4 * f 5 := by
  rw [fin6_erase_0]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_assoc]

theorem fin6_prod_erase_1 (f : Fin 6 → Polynomial ℝ) :
    ∏ j ∈ Finset.univ.erase (1:Fin 6), f j = f 0 * f 2 * f 3 * f 4 * f 5 := by
  rw [fin6_erase_1]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_assoc]

theorem fin6_prod_erase_2 (f : Fin 6 → Polynomial ℝ) :
    ∏ j ∈ Finset.univ.erase (2:Fin 6), f j = f 0 * f 1 * f 3 * f 4 * f 5 := by
  rw [fin6_erase_2]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_assoc]

theorem fin6_prod_erase_3 (f : Fin 6 → Polynomial ℝ) :
    ∏ j ∈ Finset.univ.erase (3:Fin 6), f j = f 0 * f 1 * f 2 * f 4 * f 5 := by
  rw [fin6_erase_3]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_assoc]

theorem fin6_prod_erase_4 (f : Fin 6 → Polynomial ℝ) :
    ∏ j ∈ Finset.univ.erase (4:Fin 6), f j = f 0 * f 1 * f 2 * f 3 * f 5 := by
  rw [fin6_erase_4]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_assoc]

theorem fin6_prod_erase_5 (f : Fin 6 → Polynomial ℝ) :
    ∏ j ∈ Finset.univ.erase (5:Fin 6), f j = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [fin6_erase_5]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [mul_assoc]

end GProgram.G3.CriticalCertificates
