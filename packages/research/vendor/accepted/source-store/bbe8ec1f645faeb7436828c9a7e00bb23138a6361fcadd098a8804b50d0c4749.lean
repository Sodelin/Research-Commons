import G3AllResiduePositivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Exact real-polynomial normal identities. These named coefficient arrays
are the executed packet's B-normal. This module does not assume or prove
Descartes uniqueness, Sylvester resultant identities, critical finiteness,
Baker independence or the analytic actual-source realization bridge. -/
namespace GProgram.G3.AllResidue

def normalB0 (r : ℝ) : ℝ :=
  (24 : ℝ)*r^49 + (72 : ℝ)*r^48 + (240 : ℝ)*r^47 + (540 : ℝ)*r^46 + (1212 : ℝ)*r^45 + (2229 : ℝ)*r^44 + (4035 : ℝ)*r^43 + (6510 : ℝ)*r^42 + (10230 : ℝ)*r^41 + (14880 : ℝ)*r^40 + (21045 : ℝ)*r^39 + (28005 : ℝ)*r^38 + (36300 : ℝ)*r^37 + (44655 : ℝ)*r^36 + (53655 : ℝ)*r^35 + (61536 : ℝ)*r^34 + (68958 : ℝ)*r^33 + (74205 : ℝ)*r^32 + (77946 : ℝ)*r^31 + (78921 : ℝ)*r^30 + (77946 : ℝ)*r^29 + (74205 : ℝ)*r^28 + (68958 : ℝ)*r^27 + (61536 : ℝ)*r^26 + (53655 : ℝ)*r^25 + (44655 : ℝ)*r^24 + (36300 : ℝ)*r^23 + (28005 : ℝ)*r^22 + (21045 : ℝ)*r^21 + (14880 : ℝ)*r^20 + (10230 : ℝ)*r^19 + (6510 : ℝ)*r^18 + (4035 : ℝ)*r^17 + (2229 : ℝ)*r^16 + (1212 : ℝ)*r^15 + (540 : ℝ)*r^14 + (240 : ℝ)*r^13 + (72 : ℝ)*r^12 + (24 : ℝ)*r^11

def normalB1 (r : ℝ) : ℝ :=
  (-8 : ℝ)*r^49 + (-24 : ℝ)*r^48 + (-80 : ℝ)*r^47 + (-208 : ℝ)*r^46 + (-488 : ℝ)*r^45 + (-915 : ℝ)*r^44 + (-1829 : ℝ)*r^43 + (-3018 : ℝ)*r^42 + (-4950 : ℝ)*r^41 + (-7620 : ℝ)*r^40 + (-11215 : ℝ)*r^39 + (-15455 : ℝ)*r^38 + (-21340 : ℝ)*r^37 + (-27205 : ℝ)*r^36 + (-34325 : ℝ)*r^35 + (-41652 : ℝ)*r^34 + (-48886 : ℝ)*r^33 + (-55230 : ℝ)*r^32 + (-61787 : ℝ)*r^31 + (-65542 : ℝ)*r^30 + (-68667 : ℝ)*r^29 + (-69737 : ℝ)*r^28 + (-68667 : ℝ)*r^27 + (-65542 : ℝ)*r^26 + (-61787 : ℝ)*r^25 + (-55230 : ℝ)*r^24 + (-48886 : ℝ)*r^23 + (-41652 : ℝ)*r^22 + (-34325 : ℝ)*r^21 + (-27205 : ℝ)*r^20 + (-21340 : ℝ)*r^19 + (-15455 : ℝ)*r^18 + (-11215 : ℝ)*r^17 + (-7620 : ℝ)*r^16 + (-4950 : ℝ)*r^15 + (-3018 : ℝ)*r^14 + (-1829 : ℝ)*r^13 + (-915 : ℝ)*r^12 + (-488 : ℝ)*r^11 + (-208 : ℝ)*r^10 + (-80 : ℝ)*r^9 + (-24 : ℝ)*r^8 + (-8 : ℝ)*r^7

def normalB2 (r : ℝ) : ℝ :=
  (14 : ℝ)*r^46 + (42 : ℝ)*r^45 + (86 : ℝ)*r^44 + (242 : ℝ)*r^43 + (434 : ℝ)*r^42 + (800 : ℝ)*r^41 + (1380 : ℝ)*r^40 + (2250 : ℝ)*r^39 + (3290 : ℝ)*r^38 + (5080 : ℝ)*r^37 + (6910 : ℝ)*r^36 + (9470 : ℝ)*r^35 + (12470 : ℝ)*r^34 + (15850 : ℝ)*r^33 + (19230 : ℝ)*r^32 + (23550 : ℝ)*r^31 + (26720 : ℝ)*r^30 + (30450 : ℝ)*r^29 + (33386 : ℝ)*r^28 + (35638 : ℝ)*r^27 + (36780 : ℝ)*r^26 + (37806 : ℝ)*r^25 + (36780 : ℝ)*r^24 + (35638 : ℝ)*r^23 + (33386 : ℝ)*r^22 + (30450 : ℝ)*r^21 + (26720 : ℝ)*r^20 + (23550 : ℝ)*r^19 + (19230 : ℝ)*r^18 + (15850 : ℝ)*r^17 + (12470 : ℝ)*r^16 + (9470 : ℝ)*r^15 + (6910 : ℝ)*r^14 + (5080 : ℝ)*r^13 + (3290 : ℝ)*r^12 + (2250 : ℝ)*r^11 + (1380 : ℝ)*r^10 + (800 : ℝ)*r^9 + (434 : ℝ)*r^8 + (242 : ℝ)*r^7 + (86 : ℝ)*r^6 + (42 : ℝ)*r^5 + (14 : ℝ)*r^4

def normalB3 (r : ℝ) : ℝ :=
  (-6 : ℝ)*r^42 + (-18 : ℝ)*r^41 + (-30 : ℝ)*r^40 + (-90 : ℝ)*r^39 + (-138 : ℝ)*r^38 + (-276 : ℝ)*r^37 + (-450 : ℝ)*r^36 + (-750 : ℝ)*r^35 + (-1140 : ℝ)*r^34 + (-1740 : ℝ)*r^33 + (-2406 : ℝ)*r^32 + (-3438 : ℝ)*r^31 + (-4344 : ℝ)*r^30 + (-5712 : ℝ)*r^29 + (-6858 : ℝ)*r^28 + (-8280 : ℝ)*r^27 + (-9474 : ℝ)*r^26 + (-10704 : ℝ)*r^25 + (-11580 : ℝ)*r^24 + (-12492 : ℝ)*r^23 + (-12714 : ℝ)*r^22 + (-13170 : ℝ)*r^21 + (-12714 : ℝ)*r^20 + (-12492 : ℝ)*r^19 + (-11580 : ℝ)*r^18 + (-10704 : ℝ)*r^17 + (-9474 : ℝ)*r^16 + (-8280 : ℝ)*r^15 + (-6858 : ℝ)*r^14 + (-5712 : ℝ)*r^13 + (-4344 : ℝ)*r^12 + (-3438 : ℝ)*r^11 + (-2406 : ℝ)*r^10 + (-1740 : ℝ)*r^9 + (-1140 : ℝ)*r^8 + (-750 : ℝ)*r^7 + (-450 : ℝ)*r^6 + (-276 : ℝ)*r^5 + (-138 : ℝ)*r^4 + (-90 : ℝ)*r^3 + (-30 : ℝ)*r^2 + (-18 : ℝ)*r + (-6 : ℝ)

def normalB4 (r : ℝ) : ℝ :=
  (11 : ℝ)*r^32 + (33 : ℝ)*r^31 + (55 : ℝ)*r^30 + (165 : ℝ)*r^29 + (218 : ℝ)*r^28 + (401 : ℝ)*r^27 + (610 : ℝ)*r^26 + (794 : ℝ)*r^25 + (1077 : ℝ)*r^24 + (1430 : ℝ)*r^23 + (1585 : ℝ)*r^22 + (2062 : ℝ)*r^21 + (2244 : ℝ)*r^20 + (2515 : ℝ)*r^19 + (2720 : ℝ)*r^18 + (2875 : ℝ)*r^17 + (2835 : ℝ)*r^16 + (2875 : ℝ)*r^15 + (2720 : ℝ)*r^14 + (2515 : ℝ)*r^13 + (2244 : ℝ)*r^12 + (2062 : ℝ)*r^11 + (1585 : ℝ)*r^10 + (1430 : ℝ)*r^9 + (1077 : ℝ)*r^8 + (794 : ℝ)*r^7 + (610 : ℝ)*r^6 + (401 : ℝ)*r^5 + (218 : ℝ)*r^4 + (165 : ℝ)*r^3 + (55 : ℝ)*r^2 + (33 : ℝ)*r + (11 : ℝ)

def normalB5 (r : ℝ) : ℝ :=
  (-5 : ℝ)*r^20 + (-15 : ℝ)*r^19 + (-25 : ℝ)*r^18 + (-75 : ℝ)*r^17 + (-94 : ℝ)*r^16 + (-167 : ℝ)*r^15 + (-246 : ℝ)*r^14 + (-278 : ℝ)*r^13 + (-347 : ℝ)*r^12 + (-410 : ℝ)*r^11 + (-351 : ℝ)*r^10 + (-410 : ℝ)*r^9 + (-347 : ℝ)*r^8 + (-278 : ℝ)*r^7 + (-246 : ℝ)*r^6 + (-167 : ℝ)*r^5 + (-94 : ℝ)*r^4 + (-75 : ℝ)*r^3 + (-25 : ℝ)*r^2 + (-15 : ℝ)*r + (-5 : ℝ)

def normalMassPositiveFactor (r : ℝ) : ℝ :=
  (8 : ℝ)*r^34 + (32 : ℝ)*r^33 + (104 : ℝ)*r^32 + (245 : ℝ)*r^31 + (524 : ℝ)*r^30 + (979 : ℝ)*r^29 + (1679 : ℝ)*r^28 + (2660 : ℝ)*r^27 + (4012 : ℝ)*r^26 + (5657 : ℝ)*r^25 + (7640 : ℝ)*r^24 + (9834 : ℝ)*r^23 + (12076 : ℝ)*r^22 + (14197 : ℝ)*r^21 + (16146 : ℝ)*r^20 + (17556 : ℝ)*r^19 + (18501 : ℝ)*r^18 + (18850 : ℝ)*r^17 + (18501 : ℝ)*r^16 + (17556 : ℝ)*r^15 + (16146 : ℝ)*r^14 + (14197 : ℝ)*r^13 + (12076 : ℝ)*r^12 + (9834 : ℝ)*r^11 + (7640 : ℝ)*r^10 + (5657 : ℝ)*r^9 + (4012 : ℝ)*r^8 + (2660 : ℝ)*r^7 + (1679 : ℝ)*r^6 + (979 : ℝ)*r^5 + (524 : ℝ)*r^4 + (245 : ℝ)*r^3 + (104 : ℝ)*r^2 + (32 : ℝ)*r + (8 : ℝ)

def normalMass (r : ℝ) : ℝ :=
  2*r^13*(r^2-r+1)*normalMassPositiveFactor r

theorem normal_sum (r : ℝ) :
    normalB0 r + normalB1 r + normalB2 r + normalB3 r + normalB4 r + normalB5 r = normalMass r := by
  unfold normalB0 normalB1 normalB2 normalB3 normalB4 normalB5 normalMass normalMassPositiveFactor
  ring

theorem normal_drift (r : ℝ) :
    (1 : ℝ)*normalB0 r + (3 : ℝ)*normalB1 r + (6 : ℝ)*normalB2 r + (10 : ℝ)*normalB3 r + (15 : ℝ)*normalB4 r + (21 : ℝ)*normalB5 r = 0 := by
  unfold normalB0 normalB1 normalB2 normalB3 normalB4 normalB5
  ring

theorem normal_residue_value (r : ℝ) :
    normalB0 r*(1-r^1) + normalB1 r*(1-r^3) + normalB2 r*(1-r^6) + normalB3 r*(1-r^10) + normalB4 r*(1-r^15) + normalB5 r*(1-r^21) = 0 := by
  unfold normalB0 normalB1 normalB2 normalB3 normalB4 normalB5
  ring

theorem normal_residue_derivative (r : ℝ) :
    normalB0 r*(1 : ℝ)*r^0 + normalB1 r*(3 : ℝ)*r^2 + normalB2 r*(6 : ℝ)*r^5 + normalB3 r*(10 : ℝ)*r^9 + normalB4 r*(15 : ℝ)*r^14 + normalB5 r*(21 : ℝ)*r^20 = 0 := by
  unfold normalB0 normalB1 normalB2 normalB3 normalB4 normalB5
  ring

theorem normal_square_value (r : ℝ) :
    normalB0 r*(1-r^2) + normalB1 r*(1-r^6) + normalB2 r*(1-r^12) + normalB3 r*(1-r^20) + normalB4 r*(1-r^30) + normalB5 r*(1-r^42) = 0 := by
  unfold normalB0 normalB1 normalB2 normalB3 normalB4 normalB5
  ring

theorem normal_square_derivative (r : ℝ) :
    normalB0 r*(1 : ℝ)*r^0 + normalB1 r*(3 : ℝ)*r^4 + normalB2 r*(6 : ℝ)*r^10 + normalB3 r*(10 : ℝ)*r^18 + normalB4 r*(15 : ℝ)*r^28 + normalB5 r*(21 : ℝ)*r^40 = 0 := by
  unfold normalB0 normalB1 normalB2 normalB3 normalB4 normalB5
  ring

theorem normal_mass_pos {r : ℝ} (hr : 0 < r) : 0 < normalMass r := by
  have hquad := quadratic_factor_pos r
  have hpositive : 0 < normalMassPositiveFactor r := by
    unfold normalMassPositiveFactor
    positivity
  unfold normalMass
  positivity

theorem normal_mass_ne_zero {r : ℝ} (hr : 0 < r) : normalMass r ≠ 0 :=
  ne_of_gt (normal_mass_pos hr)

#print axioms normal_sum
#print axioms normal_drift
#print axioms normal_residue_value
#print axioms normal_residue_derivative
#print axioms normal_square_value
#print axioms normal_square_derivative
#print axioms normal_mass_pos
#print axioms normal_mass_ne_zero

end GProgram.G3.AllResidue
