import Reuse
set_option warningAsError true

namespace ThueMorseReuse
open ThueMorseBits

def asInt : Bool → Int
  | false => 0
  | true => 1

def flipAt (n : Nat) : Int := asInt (Bool.xor (t n) (t (n+1)))

def descentAt (n : Nat) : Int := asInt (t n && !(t (n+1)))

def flipCount : Nat → Int
  | 0 => 0
  | n+1 => flipCount n + flipAt n

def zeroCount : Nat → Int
  | 0 => 0
  | n+1 => zeroCount n + descentAt (n+1)

theorem descentAt_counts_actual_zero (n : Nat) :
    descentAt (n+1) = (if FullHeight.height n = 0 then 1 else 0) := by
  simp only [height_zero_iff_descent]
  cases a : t (n+1) <;> cases b : t (n+2) <;> simp [descentAt, asInt, a, b]

theorem flipAt_even (n : Nat) : flipAt (2*n) = 1 := by
  unfold flipAt
  rw [t_double, t_double_add_one]
  cases t n <;> rfl

theorem flipAt_odd (n : Nat) : flipAt (2*n+1) = 1 - flipAt n := by
  unfold flipAt
  rw [show 2*n+1+1 = 2*(n+1) by omega, t_double_add_one, t_double]
  cases t n <;> cases t (n+1) <;> decide

theorem flipCount_even (n : Nat) : flipCount (2*n) = 2*(n : Int) - flipCount n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega]
    simp only [flipCount, flipAt_even, flipAt_odd] at *
    omega

theorem flipCount_recurrence (n : Nat) :
    flipCount n = (n : Int) - flipCount (n/2) := by
  have hd : n = 2*(n/2)+(n%2) := by omega
  have step : n%2=0 ∨ n%2=1 := by omega
  rcases step with h | h
  · have he : n = 2*(n/2) := by omega
    have hx := congrArg flipCount he
    rw [flipCount_even] at hx
    omega
  · have ho : n = 2*(n/2)+1 := by omega
    have hx := congrArg flipCount ho
    simp only [flipCount, flipCount_even, flipAt_even] at hx
    omega

private theorem descent_balance (n : Nat) :
    2*descentAt n = flipAt n + asInt (t n) - asInt (t (n+1)) := by
  unfold descentAt flipAt
  cases t n <;> cases t (n+1) <;> decide

theorem zeroCount_formula (n : Nat) : 2*zeroCount n =
    flipCount (n+1) - asInt (t (n+1)) := by
  induction n with
  | zero => simp [zeroCount, flipCount, flipAt, asInt]
  | succ n ih =>
    have hb := descent_balance (n+1)
    change 2*(zeroCount n + descentAt (n+1)) =
      flipCount (n+1) + flipAt (n+1) - asInt (t (n+1+1))
    omega

def alternatingDigitValue (n : Nat) : Int := 3*flipCount n - 2*(n : Int)

theorem alternatingDigitValue_recurrence (n : Nat) :
    alternatingDigitValue n = ((n%2 : Nat) : Int) - alternatingDigitValue (n/2) := by
  unfold alternatingDigitValue
  rw [flipCount_recurrence]
  omega

theorem zeroCount_exact (n : Nat) :
    6*zeroCount n =
      2*((n+1 : Nat) : Int) + alternatingDigitValue (n+1) - 3*asInt (t (n+1)) := by
  unfold alternatingDigitValue
  have h := zeroCount_formula n
  omega

#print axioms descentAt_counts_actual_zero
#print axioms flipCount_recurrence
#print axioms alternatingDigitValue_recurrence
#print axioms zeroCount_exact
end ThueMorseReuse
