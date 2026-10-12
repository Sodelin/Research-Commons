import G3CriticalBivariateLists
import G3FixedDegreeResultants

/-! Binding exact coefficient arrays to the imported Bernoulli source. -/
noncomputable section
namespace GProgram.G3.CriticalCertificates
open Polynomial
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def evalRows (r : ℝ) (as : List (List ℤ)) : Polynomial ℝ :=
  (ofRows as).map (Polynomial.eval₂RingHom (Int.castRingHom ℝ) r)

theorem evalRows_add (r : ℝ) (as bs : List (List ℤ)) :
    evalRows r (addRows as bs) = evalRows r as + evalRows r bs := by
  simp only [evalRows, ofRows_add, Polynomial.map_add]

theorem evalRows_mul (r : ℝ) (as bs : List (List ℤ)) :
    evalRows r (mulRows as bs) = evalRows r as * evalRows r bs := by
  simp only [evalRows, ofRows_mul, Polynomial.map_mul]

theorem evalRows_const (r : ℝ) (as : List ℤ) :
    evalRows r [as] = C ((ofCoeffs as).eval₂ (Int.castRingHom ℝ) r) := by
  simp [evalRows, ofRows, ofCoeffs]

theorem evalRows_factor (r : ℝ) (z : ℤ) (n : ℕ) :
    evalRows r [[1], [z^n-1]] = AllResidue.probabilityPolynomial n (z : ℝ) := by
  simp [evalRows, ofRows, ofCoeffs, AllResidue.probabilityPolynomial]
  <;> ring

def normalRow0 : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24, 72, 240, 540, 1212, 2229, 4035, 6510, 10230, 14880, 21045, 28005, 36300, 44655, 53655, 61536, 68958, 74205, 77946, 78921, 77946, 74205, 68958, 61536, 53655, 44655, 36300, 28005, 21045, 14880, 10230, 6510, 4035, 2229, 1212, 540, 240, 72, 24]

theorem normalRow0_eval (r : ℝ) :
    (ofCoeffs normalRow0).eval₂ (Int.castRingHom ℝ) r = AllResidue.normalB0 r := by
  norm_num [normalRow0, ofCoeffs, AllResidue.normalB0]
  <;> ring

def normalRow1 : List ℤ := [0, 0, 0, 0, 0, 0, 0, -8, -24, -80, -208, -488, -915, -1829, -3018, -4950, -7620, -11215, -15455, -21340, -27205, -34325, -41652, -48886, -55230, -61787, -65542, -68667, -69737, -68667, -65542, -61787, -55230, -48886, -41652, -34325, -27205, -21340, -15455, -11215, -7620, -4950, -3018, -1829, -915, -488, -208, -80, -24, -8]

theorem normalRow1_eval (r : ℝ) :
    (ofCoeffs normalRow1).eval₂ (Int.castRingHom ℝ) r = AllResidue.normalB1 r := by
  norm_num [normalRow1, ofCoeffs, AllResidue.normalB1]
  <;> ring

def normalRow2 : List ℤ := [0, 0, 0, 0, 14, 42, 86, 242, 434, 800, 1380, 2250, 3290, 5080, 6910, 9470, 12470, 15850, 19230, 23550, 26720, 30450, 33386, 35638, 36780, 37806, 36780, 35638, 33386, 30450, 26720, 23550, 19230, 15850, 12470, 9470, 6910, 5080, 3290, 2250, 1380, 800, 434, 242, 86, 42, 14]

theorem normalRow2_eval (r : ℝ) :
    (ofCoeffs normalRow2).eval₂ (Int.castRingHom ℝ) r = AllResidue.normalB2 r := by
  norm_num [normalRow2, ofCoeffs, AllResidue.normalB2]
  <;> ring

def normalRow3 : List ℤ := [-6, -18, -30, -90, -138, -276, -450, -750, -1140, -1740, -2406, -3438, -4344, -5712, -6858, -8280, -9474, -10704, -11580, -12492, -12714, -13170, -12714, -12492, -11580, -10704, -9474, -8280, -6858, -5712, -4344, -3438, -2406, -1740, -1140, -750, -450, -276, -138, -90, -30, -18, -6]

theorem normalRow3_eval (r : ℝ) :
    (ofCoeffs normalRow3).eval₂ (Int.castRingHom ℝ) r = AllResidue.normalB3 r := by
  norm_num [normalRow3, ofCoeffs, AllResidue.normalB3]
  <;> ring

def normalRow4 : List ℤ := [11, 33, 55, 165, 218, 401, 610, 794, 1077, 1430, 1585, 2062, 2244, 2515, 2720, 2875, 2835, 2875, 2720, 2515, 2244, 2062, 1585, 1430, 1077, 794, 610, 401, 218, 165, 55, 33, 11]

theorem normalRow4_eval (r : ℝ) :
    (ofCoeffs normalRow4).eval₂ (Int.castRingHom ℝ) r = AllResidue.normalB4 r := by
  norm_num [normalRow4, ofCoeffs, AllResidue.normalB4]
  <;> ring

def normalRow5 : List ℤ := [-5, -15, -25, -75, -94, -167, -246, -278, -347, -410, -351, -410, -347, -278, -246, -167, -94, -75, -25, -15, -5]

theorem normalRow5_eval (r : ℝ) :
    (ofCoeffs normalRow5).eval₂ (Int.castRingHom ℝ) r = AllResidue.normalB5 r := by
  norm_num [normalRow5, ofCoeffs, AllResidue.normalB5]
  <;> ring

theorem fin6_erase_0 : (Finset.univ : Finset (Fin 6)).erase 0 = {1, 2, 3, 4, 5} := by decide
theorem fin6_erase_1 : (Finset.univ : Finset (Fin 6)).erase 1 = {0, 2, 3, 4, 5} := by decide
theorem fin6_erase_2 : (Finset.univ : Finset (Fin 6)).erase 2 = {0, 1, 3, 4, 5} := by decide
theorem fin6_erase_3 : (Finset.univ : Finset (Fin 6)).erase 3 = {0, 1, 2, 4, 5} := by decide
theorem fin6_erase_4 : (Finset.univ : Finset (Fin 6)).erase 4 = {0, 1, 2, 3, 5} := by decide
theorem fin6_erase_5 : (Finset.univ : Finset (Fin 6)).erase 5 = {0, 1, 2, 3, 4} := by decide

end GProgram.G3.CriticalCertificates
