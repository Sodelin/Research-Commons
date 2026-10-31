import SamuelAlexanderResearch.QuantitativeModulus
import SamuelAlexanderResearch.SlowAvoidance

/-! Existing CB-SEQ-006 owner/type correspondence, pending full-card review.
Original Samuel definitions and proof authorship are retained. A supplied bit
modulus yields an explicit clock; existence by choice is not a native algorithm.
Arbitrarily slow finite matches in an f-dependent target do not give an infinite match. -/
namespace ResearchCommons.Claims.AperiodicModulus
open BinaryAvoidance QuantitativeAvoidance FiniteEditStability

theorem even_break (s : Nat → Bool) (e i : Nat) :
    QuantitativeModulus.BreaksAt s (2*e) i ↔ s (i+e+1) = s i :=
  QuantitativeModulus.even_break_iff s e i

theorem odd_break (s : Nat → Bool) (e i : Nat) :
    QuantitativeModulus.BreaksAt s (2*e+1) i ↔ s (i+e+1) ≠ s i :=
  QuantitativeModulus.odd_break_iff s e i

theorem prefix_clock {s : Nat → Bool} {M : Nat → Nat → Nat}
    (hm : QuantitativeModulus.IsModulus s M) {path : Nat → Nat} {ell : Nat}
    (hp : MatchesPrefix s path ell) :
    ell < QuantitativeModulus.clock M (path 0) (path 0+1) :=
  QuantitativeModulus.prefix_length_lt_clock hm hp

theorem uniform_window_bound {s : Nat → Bool} {M : Nat → Nat → Nat}
    (hm : QuantitativeModulus.IsModulus s M) {path : Nat → Nat} {ell R : Nat}
    (hp : MatchesPrefix s path ell)
    (hR : ∀ b, M (path 0) b ≤ b+R) : ell < (path 0+1)*R :=
  QuantitativeModulus.prefix_length_lt_uniform_windows hm hp hR

theorem aperiodic_modulus_and_bounds (s : Nat → Bool) (ha : ¬EventuallyPeriodic s) :
    ∃ M, QuantitativeModulus.IsModulus s M ∧
      ∀ path ell, MatchesPrefix s path ell →
        ell < QuantitativeModulus.clock M (path 0) (path 0+1) :=
  QuantitativeModulus.aperiodic_explicit_bounds s ha

theorem arbitrarily_slow (f : Nat → Nat) :
    ∃ s : Nat → Bool, ¬EventuallyPeriodic s ∧
      (¬∃ path, Matches s path) ∧
      ∃ starts : Nat → Nat,
        (∀ i j, i < j → starts i < starts j) ∧
        ∀ j, ∃ len, f (starts j) < len ∧
          ∃ path : Nat → Nat, path 0 = starts j ∧ MatchesPrefix s path len :=
  SlowAvoidance.arbitrarily_slow_avoidance f
end ResearchCommons.Claims.AperiodicModulus
