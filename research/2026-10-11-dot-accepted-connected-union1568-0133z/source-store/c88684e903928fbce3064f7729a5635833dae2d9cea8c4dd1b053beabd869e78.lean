import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Finite cap-six Poisson-interior Jacobian certificate

Dedicated Lean lane's formal finite algebra contribution. Source interface is
the G3 worker's CAP6-POISSON-INTERIOR, section 3. Its analytic IFT, positive
normal-form regularization and actual finite-source attainment are separate
hand/source obligations; this module certifies only the explicit determinant.
The last column differentiates D(q) in q and then sets q=r^2. It has no extra 2r.
A factored unit-lower/upper certificate avoids the memory-intensive direct
Leibniz expansion. Every certificate entry is checked by ring/field_simp.
Public research checkpoint; product-specific software is outside this packet.
-/

namespace GProgram.G3.CapSix

open scoped BigOperators

def exponent (i : Fin 5) : Nat := match i.val with
  | 0 => 1 | 1 => 3 | 2 => 6 | 3 => 10 | _ => 15

noncomputable def R (n : Nat) (r : ℝ) : ℝ := ∑ k ∈ Finset.range n, r^k
noncomputable def Rprime (n : Nat) (r : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (k : ℝ)*r^(k-1)

noncomputable def J0 (r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  match j.val with
  | 0 => exponent i
  | 1 => R (exponent i) r
  | 2 => Rprime (exponent i) r
  | 3 => 1-r^(2*exponent i)
  | _ => -(exponent i : ℝ)*r^(2*exponent i-2)

noncomputable def P (r : ℝ) : ℝ :=
  5*r^20+15*r^19+25*r^18+75*r^17+94*r^16+167*r^15+
  246*r^14+278*r^13+347*r^12+410*r^11+351*r^10+
  410*r^9+347*r^8+278*r^7+246*r^6+167*r^5+94*r^4+
  75*r^3+25*r^2+15*r+5

noncomputable def determinantFactor (r : ℝ) : ℝ :=
  3*r^8*(1-r)^10*(r+1)^4*(r^2+r+1)^4*(r^4+r^3+r^2+r+1)*P r

noncomputable def Q (r : ℝ) : ℝ := 3*r^11 + 12*r^10 + 21*r^9 + 42*r^8 + 59*r^7 + 74*r^6 + 87*r^5 + 86*r^4 + 65*r^3 + 48*r^2 + 20*r + 8

noncomputable def L (r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 1, 0 => 3
  | 1, 1 => 1
  | 2, 0 => 6
  | 2, 1 => (r^4 + 2*r^3 + 3*r^2 + 4*r + 5)/(r + 2)
  | 2, 2 => 1
  | 3, 0 => 10
  | 3, 1 => (r^8 + 2*r^7 + 3*r^6 + 4*r^5 + 5*r^4 + 6*r^3 + 7*r^2 + 8*r + 9)/(r + 2)
  | 3, 2 => (7*r^8 + 28*r^7 + 43*r^6 + 52*r^5 + 55*r^4 + 52*r^3 + 43*r^2 + 28*r + 7)/(3*(r^2 + r + 1)*(r^2 + 3*r + 1))
  | 3, 3 => 1
  | 4, 0 => 15
  | 4, 1 => (r^13 + 2*r^12 + 3*r^11 + 4*r^10 + 5*r^9 + 6*r^8 + 7*r^7 + 8*r^6 + 9*r^5 + 10*r^4 + 11*r^3 + 12*r^2 + 13*r + 14)/(r + 2)
  | 4, 2 => 2*(r + 1)*(2*r^10 + 4*r^9 + r^8 + 5*r^7 + 4*r^6 + 3*r^5 + 4*r^4 + 5*r^3 + r^2 + 4*r + 2)/(r^2 + 3*r + 1)
  | 4, 3 => 3*(r^2 + r + 1)^2*(r^17 + 2*r^16 + 6*r^14 + 5*r^13 + 4*r^12 + 13*r^11 + 14*r^10 + 9*r^9 + 24*r^8 + 17*r^7 + 16*r^6 + 19*r^5 + 14*r^4 + 10*r^3 + 12*r^2 + 3*r + 6)/(Q r)
  | 4, 4 => 1
  | _, _ => 0

noncomputable def U (r : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 0, 1 => 1
  | 0, 3 => 1 - r^2
  | 0, 4 => -1
  | 1, 1 => (r - 1)*(r + 2)
  | 1, 2 => 2*r + 1
  | 1, 3 => -(r - 1)^2*(r + 1)^2*(r^2 + 2)
  | 1, 4 => -3*(r - 1)*(r + 1)*(r^2 + 1)
  | 2, 2 => 3*(r - 1)*(r^2 + r + 1)*(r^2 + 3*r + 1)/(r + 2)
  | 2, 3 => -r*(r - 1)^3*(r + 1)^2*(r^2 + r + 1)^2*(r^3 + r^2 + 3)/(r + 2)
  | 2, 4 => -3*(r - 1)^2*(r + 1)*(r^2 + r + 1)*(2*r^6 + 4*r^5 + 2*r^4 + 5*r^3 + 4*r^2 + 2*r + 1)/(r + 2)
  | 3, 3 => -r^3*(r - 1)^4*(r + 1)^2*(r^2 + r + 1)*(Q r)/(3*(r^2 + 3*r + 1))
  | 3, 4 => -2*r^2*(r - 1)^3*(r + 1)*(5*r^14 + 25*r^13 + 55*r^12 + 100*r^11 + 148*r^10 + 190*r^9 + 220*r^8 + 230*r^7 + 210*r^6 + 170*r^5 + 115*r^4 + 65*r^3 + 30*r^2 + 10*r + 2)/(r^2 + 3*r + 1)
  | 4, 4 => -3*r^5*(r - 1)^4*(r + 1)^2*(r^2 + r + 1)^2*(r^4 + r^3 + r^2 + r + 1)*(P r)/(Q r)
  | _, _ => 0

theorem Q_positive {r : ℝ} (hr : 0 < r) : 0 < Q r := by
  unfold Q
  positivity

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem LU_eq_J0 {r : ℝ} (hr : 0 < r) : L r * U r = J0 r := by
  have h2 : r+2 ≠ 0 := ne_of_gt (by linarith)
  have hc : r^2+r+1 ≠ 0 := ne_of_gt (by positivity)
  have hb : r^2+3*r+1 ≠ 0 := ne_of_gt (by positivity)
  have hQ : Q r ≠ 0 := ne_of_gt (Q_positive hr)
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [Matrix.mul_apply,Fin.sum_univ_succ,L,U,J0,exponent,
    R,Rprime,Finset.sum_range_succ]
  all_goals field_simp [h2,hc,hb,hQ]
  all_goals try simp only [Q,P]
  all_goals ring

theorem det_L (r : ℝ) : (L r).det = 1 := by
  simp [Matrix.det_succ_row_zero, Matrix.det_fin_zero,
    Fin.sum_univ_succ, Matrix.submatrix_apply, L]

theorem det_U (r : ℝ) : (U r).det = ∏ i, U r i i := by
  simp [Matrix.det_succ_column_zero, Matrix.det_fin_zero,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Matrix.submatrix_apply, U]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem exact_determinant {r : ℝ} (hr : 0 < r) : (J0 r).det = determinantFactor r := by
  rw [← LU_eq_J0 hr,Matrix.det_mul,det_L,one_mul,
    det_U r]
  have h2 : r+2 ≠ 0 := ne_of_gt (by linarith)
  have hb : r^2+3*r+1 ≠ 0 := ne_of_gt (by positivity)
  have hQ : Q r ≠ 0 := ne_of_gt (Q_positive hr)
  norm_num [Fin.prod_univ_succ,U]
  unfold determinantFactor
  field_simp [h2,hb,hQ]
  ring

theorem P_positive {r : ℝ} (hr : 0 < r) : 0 < P r := by
  unfold P
  positivity

theorem determinantFactor_positive {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < determinantFactor r := by
  have h1 : 0 < 1-r := by linarith
  have hp := P_positive hr
  unfold determinantFactor
  positivity

theorem J0_nonsingular {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : (J0 r).det ≠ 0 := by
  rw [exact_determinant hr]
  exact ne_of_gt (determinantFactor_positive hr hr1)

noncomputable def columnScale (w : ℝ) (j : Fin 5) : ℝ :=
  match j.val with
  | 2 => w | 4 => 1/2 | _ => 1

noncomputable def J (r w : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  J0 r * Matrix.diagonal (columnScale w)

theorem scaled_determinant (r w : ℝ) (hr : 0 < r) : (J r w).det = (w/2)*determinantFactor r := by
  rw [J,Matrix.det_mul,Matrix.det_diagonal,exact_determinant hr]
  norm_num [columnScale,Fin.prod_univ_five]
  ring

theorem scaled_J_nonsingular {r w : ℝ} (hr : 0 < r) (hr1 : r < 1) (hw : 0 < w) :
    (J r w).det ≠ 0 := by
  rw [scaled_determinant r w hr]
  have hp := determinantFactor_positive hr hr1
  exact ne_of_gt (mul_pos (by positivity) hp)

#print axioms LU_eq_J0
#print axioms det_L
#print axioms det_U
#print axioms exact_determinant
#print axioms J0_nonsingular
#print axioms scaled_J_nonsingular

end GProgram.G3.CapSix
