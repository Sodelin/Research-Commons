import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Algebra underlying the curvature-corrected G4 residual

Codex, 2026-10-14. SOURCE AUTHORED; COMPILATION UNVERIFIED.
This file contains abstract algebra only. It does not construct the physical
forest algebra, differentiate its body map, or prove a Taylor/BCH expansion.
The Jacobian inverse identities and complete leading equality are explicit
hypotheses. No theorem about signs, source attainability or G4 closure follows.
-/

namespace G4CurvatureAlgebra

section Projection

variable {R V : Type*} [Ring R] [AddCommGroup V]

/-- Endpoint projection, with the coordinate inverse supplied explicitly. -/
def endpointProjection (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V) (x : R) : R :=
  x - D (Jinv (pi x))

def normalizedTangent (D : V →+ R) (Tinv : R) (v : V) : R := D v * Tinv

def normalizedCoordinates (pi : R →+ V) (T : R) (L : R) : V := pi (L * T)

def logProjection (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (T Tinv L : R) : R :=
  L - normalizedTangent D Tinv (Jinv (normalizedCoordinates pi T L))

/-- Transport uses the right normalization and only `T * Tinv = 1`. -/
theorem projection_transport (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (T Tinv L : R) (hTTinv : T * Tinv = 1) :
    logProjection D pi Jinv T Tinv L =
      endpointProjection D pi Jinv (L * T) * Tinv := by
  unfold logProjection endpointProjection normalizedTangent normalizedCoordinates
  rw [sub_mul, mul_assoc, hTTinv, mul_one]

theorem endpointProjection_tangent (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (hLeft : ∀ v, Jinv (pi (D v)) = v) (v : V) :
    endpointProjection D pi Jinv (D v) = 0 := by
  unfold endpointProjection
  rw [hLeft, sub_self]

theorem endpointProjection_coordinates (D : V →+ R) (pi : R →+ V)
    (Jinv : V →+ V) (hRight : ∀ c, pi (D (Jinv c)) = c) (x : R) :
    pi (endpointProjection D pi Jinv x) = 0 := by
  simp only [endpointProjection, map_sub, hRight, sub_self]

theorem endpointProjection_idempotent (D : V →+ R) (pi : R →+ V)
    (Jinv : V →+ V) (hRight : ∀ c, pi (D (Jinv c)) = c) (x : R) :
    endpointProjection D pi Jinv (endpointProjection D pi Jinv x) =
      endpointProjection D pi Jinv x := by
  change endpointProjection D pi Jinv x -
    D (Jinv (pi (endpointProjection D pi Jinv x))) = _
  rw [endpointProjection_coordinates D pi Jinv hRight x]
  simp only [map_zero, sub_zero]

theorem normalizedCoordinates_tangent (D : V →+ R) (pi : R →+ V)
    (T Tinv : R) (hTinvT : Tinv * T = 1) (v : V) :
    normalizedCoordinates pi T (normalizedTangent D Tinv v) = pi (D v) := by
  unfold normalizedCoordinates normalizedTangent
  rw [mul_assoc, hTinvT, mul_one]

theorem logProjection_tangent (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (T Tinv : R) (hTinvT : Tinv * T = 1)
    (hLeft : ∀ v, Jinv (pi (D v)) = v) (v : V) :
    logProjection D pi Jinv T Tinv (normalizedTangent D Tinv v) = 0 := by
  unfold logProjection
  rw [normalizedCoordinates_tangent D pi T Tinv hTinvT v, hLeft, sub_self]

theorem logProjection_coordinates (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (T Tinv : R) (hTTinv : T * Tinv = 1) (hTinvT : Tinv * T = 1)
    (hRight : ∀ c, pi (D (Jinv c)) = c) (L : R) :
    normalizedCoordinates pi T (logProjection D pi Jinv T Tinv L) = 0 := by
  unfold normalizedCoordinates
  rw [projection_transport D pi Jinv T Tinv L hTTinv,
    mul_assoc, hTinvT, mul_one]
  exact endpointProjection_coordinates D pi Jinv hRight (L * T)

theorem logProjection_idempotent (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (T Tinv : R) (hTTinv : T * Tinv = 1) (hTinvT : Tinv * T = 1)
    (hRight : ∀ c, pi (D (Jinv c)) = c) (L : R) :
    logProjection D pi Jinv T Tinv (logProjection D pi Jinv T Tinv L) =
      logProjection D pi Jinv T Tinv L := by
  change logProjection D pi Jinv T Tinv L -
    normalizedTangent D Tinv
      (Jinv (normalizedCoordinates pi T (logProjection D pi Jinv T Tinv L))) = _
  rw [logProjection_coordinates D pi Jinv T Tinv hTTinv hTinvT hRight L]
  simp only [map_zero, normalizedTangent, zero_mul, sub_zero]

theorem logProjection_add (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (T Tinv x y : R) :
    logProjection D pi Jinv T Tinv (x + y) =
      logProjection D pi Jinv T Tinv x + logProjection D pi Jinv T Tinv y := by
  simp only [logProjection, normalizedTangent, normalizedCoordinates, add_mul, map_add]
  abel

theorem logProjection_zero (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (T Tinv : R) : logProjection D pi Jinv T Tinv 0 = 0 := by
  simp only [logProjection, normalizedTangent, normalizedCoordinates,
    zero_mul, map_zero, sub_self]

/-- A complete leading equation forces the calibrated body coefficient. -/
theorem leading_body_coefficient (D : V →+ R) (pi : R →+ V) (Jinv : V →+ V)
    (T Tinv : R) (hTinvT : Tinv * T = 1)
    (hLeft : ∀ v, Jinv (pi (D v)) = v) (v : V) (S : R)
    (hLead : normalizedTangent D Tinv v + S = 0) :
    v = -Jinv (normalizedCoordinates pi T S) := by
  have hCoord : pi (D v) + normalizedCoordinates pi T S = 0 := by
    have h := congrArg (fun x : R => pi (x * T)) hLead
    simpa only [normalizedTangent, normalizedCoordinates, add_mul, map_add,
      mul_assoc, hTinvT, mul_one, zero_mul, map_zero] using h
  have hRecover : v + Jinv (normalizedCoordinates pi T S) = 0 := by
    have h := congrArg (fun c : V => Jinv c) hCoord
    simpa only [map_add, hLeft, map_zero] using h
  calc
    v = v + -(v + Jinv (normalizedCoordinates pi T S)) := by
      rw [hRecover, neg_zero, add_zero]
    _ = -Jinv (normalizedCoordinates pi T S) := by abel

/-- This uses a full equality, not merely equality of selected coordinates. -/
theorem complete_leading_projected_zero (D : V →+ R) (pi : R →+ V)
    (Jinv : V →+ V) (T Tinv : R) (hTinvT : Tinv * T = 1)
    (hLeft : ∀ v, Jinv (pi (D v)) = v) (v : V) (S : R)
    (hLead : normalizedTangent D Tinv v + S = 0) :
    logProjection D pi Jinv T Tinv S = 0 := by
  have h := congrArg (logProjection D pi Jinv T Tinv) hLead
  rw [logProjection_add, logProjection_tangent D pi Jinv T Tinv hTinvT hLeft v,
    logProjection_zero, zero_add] at h
  exact h

end Projection

section Brackets

variable {R : Type*} [Ring R]

def commutator (x y : R) : R := x * y - y * x

theorem bracket_sum_substitution (x y : R) :
    commutator x (-(x + y)) + commutator x y + commutator (-(x + y)) y =
      -commutator x y := by
  unfold commutator
  noncomm_ring

theorem bracket_sum_of_complete_leading (x z y : R) (hLead : x + z + y = 0) :
    commutator x z + commutator x y + commutator z y = -commutator x y := by
  have hz : z = -(x + y) := by
    calc
      z = z + -(x + z + y) := by rw [hLead, neg_zero, add_zero]
      _ = -(x + y) := by abel
  rw [hz]
  exact bracket_sum_substitution x y

end Brackets

section Quadratic

variable {R V W : Type*} [Ring R] [Module ℚ R]
variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- `B` is a supplied symmetric normalized endpoint Hessian, not a derivative
computed here. The expression subtracts the polarized noncommutative square. -/
def logHessian (B : V →ₗ[ℚ] V →ₗ[ℚ] R) (A : V →ₗ[ℚ] R) (v w : V) : R :=
  B v w - (1 / 2 : ℚ) • (A v * A w + A w * A v)

def logQuadratic (B : V →ₗ[ℚ] V →ₗ[ℚ] R) (A : V →ₗ[ℚ] R) (v : V) : R :=
  (1 / 2 : ℚ) • B v v - (1 / 2 : ℚ) • (A v * A v)

theorem half_smul_pair (x : R) : (1 / 2 : ℚ) • x + (1 / 2 : ℚ) • x = x := by
  rw [← add_smul]
  norm_num

theorem logHessian_diagonal (B : V →ₗ[ℚ] V →ₗ[ℚ] R) (A : V →ₗ[ℚ] R) (v : V) :
    logHessian B A v v = B v v - A v * A v := by
  unfold logHessian
  rw [smul_add, half_smul_pair]

theorem logQuadratic_eq_half_hessian (B : V →ₗ[ℚ] V →ₗ[ℚ] R)
    (A : V →ₗ[ℚ] R) (v : V) :
    logQuadratic B A v = (1 / 2 : ℚ) • logHessian B A v v := by
  rw [logHessian_diagonal, smul_sub]
  rfl

theorem logHessian_symmetric (B : V →ₗ[ℚ] V →ₗ[ℚ] R) (A : V →ₗ[ℚ] R)
    (hSym : ∀ v w, B v w = B w v) (v w : V) :
    logHessian B A v w = logHessian B A w v := by
  unfold logHessian
  rw [hSym v w, add_comm (A v * A w)]

/-- Polarization of the quadratic log-body coefficient. Multiplication in `R`
need not commute; the cross term contains both multiplication orders. -/
theorem logQuadratic_polarization (B : V →ₗ[ℚ] V →ₗ[ℚ] R)
    (A : V →ₗ[ℚ] R) (hSym : ∀ v w, B v w = B w v) (v w : V) :
    logQuadratic B A (v + w) - logQuadratic B A v - logQuadratic B A w =
      logHessian B A v w := by
  have hExpand : B (v + w) (v + w) = B v v + B v w + B w v + B w w := by
    simp only [map_add, LinearMap.add_apply]
    abel
  calc
    logQuadratic B A (v + w) - logQuadratic B A v - logQuadratic B A w =
        ((1 / 2 : ℚ) • B v w + (1 / 2 : ℚ) • B w v) -
          (1 / 2 : ℚ) • (A v * A w + A w * A v) := by
      simp only [logQuadratic, hExpand, map_add, add_mul, mul_add, smul_add]
      abel
    _ = logHessian B A v w := by
      rw [hSym w v, half_smul_pair]
      rfl

theorem half_bracket_of_complete_leading (x z y : R) (hLead : x + z + y = 0) :
    (1 / 2 : ℚ) • (commutator x z + commutator x y + commutator z y) =
      -((1 / 2 : ℚ) • commutator x y) := by
  rw [bracket_sum_of_complete_leading x z y hLead, smul_neg]

/-- Removes the new linear body coefficient from the supplied second-order
expression. The coefficient formulas and full leading equality are hypotheses;
this does not establish that they are actual physical Taylor/BCH coefficients. -/
theorem projected_second_residual (P : R →ₗ[ℚ] W) (A : V →ₗ[ℚ] R)
    (hKill : ∀ v, P (A v) = 0) (x z y xNext zNext yNext H : R) (vNext : V)
    (hLead : x + z + y = 0) (hBody : zNext = A vNext + (1 / 2 : ℚ) • H) :
    P (xNext + zNext + yNext +
      (1 / 2 : ℚ) • (commutator x z + commutator x y + commutator z y)) =
      P (xNext + yNext - (1 / 2 : ℚ) • commutator x y + (1 / 2 : ℚ) • H) := by
  rw [hBody, half_bracket_of_complete_leading x z y hLead]
  have hRearrange :
      xNext + (A vNext + (1 / 2 : ℚ) • H) + yNext +
          -((1 / 2 : ℚ) • commutator x y) =
        A vNext + (xNext + yNext - (1 / 2 : ℚ) • commutator x y +
          (1 / 2 : ℚ) • H) := by abel
  rw [hRearrange, map_add, hKill, zero_add]

/-- The `k = 3` names expose the sixth residual with the supplied quadratic
body coefficient expanded. No grading or coefficient extraction is assumed
implicitly: the sixth body formula is the explicit `hBody` premise. -/
theorem projected_sixth_curvature_residual (P : R →ₗ[ℚ] W)
    (B : V →ₗ[ℚ] V →ₗ[ℚ] R) (A : V →ₗ[ℚ] R)
    (hKill : ∀ v, P (A v) = 0) (x3 z3 y3 x6 z6 y6 : R) (v3 v6 : V)
    (hLead : x3 + z3 + y3 = 0)
    (hBody : z6 = A v6 + logQuadratic B A v3) :
    P (x6 + z6 + y6 +
      (1 / 2 : ℚ) • (commutator x3 z3 + commutator x3 y3 + commutator z3 y3)) =
      P (x6 + y6 - (1 / 2 : ℚ) • commutator x3 y3 +
        (1 / 2 : ℚ) • logHessian B A v3 v3) := by
  have hBody' : z6 = A v6 + (1 / 2 : ℚ) • logHessian B A v3 v3 := by
    rw [hBody, logQuadratic_eq_half_hessian]
  exact projected_second_residual P A hKill x3 z3 y3 x6 z6 y6
    (logHessian B A v3 v3) v6 hLead hBody'

end Quadratic

end G4CurvatureAlgebra

-- Audit commands are supplied for the integration owner's compiler execution.
-- No output from these commands has been observed by this source author.
#print axioms G4CurvatureAlgebra.projection_transport
#print axioms G4CurvatureAlgebra.endpointProjection_tangent
#print axioms G4CurvatureAlgebra.endpointProjection_coordinates
#print axioms G4CurvatureAlgebra.endpointProjection_idempotent
#print axioms G4CurvatureAlgebra.normalizedCoordinates_tangent
#print axioms G4CurvatureAlgebra.logProjection_tangent
#print axioms G4CurvatureAlgebra.logProjection_coordinates
#print axioms G4CurvatureAlgebra.logProjection_idempotent
#print axioms G4CurvatureAlgebra.logProjection_add
#print axioms G4CurvatureAlgebra.logProjection_zero
#print axioms G4CurvatureAlgebra.leading_body_coefficient
#print axioms G4CurvatureAlgebra.complete_leading_projected_zero
#print axioms G4CurvatureAlgebra.bracket_sum_substitution
#print axioms G4CurvatureAlgebra.bracket_sum_of_complete_leading
#print axioms G4CurvatureAlgebra.half_smul_pair
#print axioms G4CurvatureAlgebra.logHessian_diagonal
#print axioms G4CurvatureAlgebra.logQuadratic_eq_half_hessian
#print axioms G4CurvatureAlgebra.logHessian_symmetric
#print axioms G4CurvatureAlgebra.logQuadratic_polarization
#print axioms G4CurvatureAlgebra.half_bracket_of_complete_leading
#print axioms G4CurvatureAlgebra.projected_second_residual
#print axioms G4CurvatureAlgebra.projected_sixth_curvature_residual
