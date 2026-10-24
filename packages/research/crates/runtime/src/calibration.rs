//! Exact implementation of OLD CB-MEMORY-004 / CALIBRATION-BOUND.md.
//! Known strict Bernoulli rate, independent fully observed trials. No sampling
//! engine, unknown-rate admission, or biological calibration is provided.
use parity_solver::{q, Rational};

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub trials: u32,
    pub rational_chars: usize,
    pub render_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self { trials: 1_000_000, rational_chars: 4096, render_bytes: 262144 }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    Limit { kind: &'static str, cap: usize },
}
fn bounded(value: &Rational, limits: Limits) -> Result<(), Error> {
    if value.to_string().len() > limits.rational_chars {
        Err(Error::Limit { kind: "rational_chars", cap: limits.rational_chars })
    } else { Ok(()) }
}
/// Owns ONE unchanged rate and its exact finite-sample optima. Private fields
/// prevent an emitted certificate from being paired with replaced coordinates.
#[derive(Clone, Debug)]
pub struct Calibration {
    rate: Rational,
    trials: u32,
    miss: Rational,
    sum: Rational,
    worst: Rational,
    equal_prior: Rational,
}
impl Calibration {
    /// Binary powering uses the existing BigRational engine. Limits are checked
    /// after each operation, not claimed as a global allocator bound.
    pub fn new(rate: Rational, trials: u32, limits: Limits) -> Result<Self, Error> {
        if rate <= q(0, 1) || rate >= q(1, 1) {
            return Err(Error::Invalid("event rate must be strictly between zero and one"));
        }
        if trials > limits.trials {
            return Err(Error::Limit { kind: "trials", cap: limits.trials as usize });
        }
        bounded(&rate, limits)?;
        let mut power = q(1, 1) - &rate;
        bounded(&power, limits)?;
        let mut exponent = trials;
        let mut miss = q(1, 1);
        while exponent != 0 {
            if exponent & 1 != 0 {
                miss *= &power;
                bounded(&miss, limits)?;
            }
            exponent >>= 1;
            if exponent != 0 {
                power = &power * &power;
                bounded(&power, limits)?;
            }
        }
        let denominator = q(1, 1) + &miss;
        bounded(&denominator, limits)?;
        let worst = &miss / denominator;
        let equal_prior = &miss / q(2, 1);
        bounded(&worst, limits)?;
        bounded(&equal_prior, limits)?;
        Ok(Self { rate, trials, sum: miss.clone(), miss, worst, equal_prior })
    }
    pub fn rate(&self) -> &Rational { &self.rate }
    pub fn trials(&self) -> u32 { self.trials }
    pub fn miss(&self) -> &Rational { &self.miss }
    pub fn minimum_sum_error(&self) -> &Rational { &self.sum }
    pub fn minimum_worst_error(&self) -> &Rational { &self.worst }
    pub fn minimum_equal_prior_error(&self) -> &Rational { &self.equal_prior }
    /// On any nonzero sample choose the alternative. On the all-zero sample,
    /// choose it with probability a. The SAME rule is used under both models.
    pub fn threshold_errors(&self, a: &Rational, limits: Limits)
        -> Result<(Rational, Rational), Error> {
        if a < &q(0, 1) || a > &q(1, 1) {
            return Err(Error::Invalid("randomized decision probability is outside [0,1]"));
        }
        bounded(a, limits)?;
        let beta = &self.miss * (q(1, 1) - a);
        bounded(&beta, limits)?;
        Ok((a.clone(), beta))
    }
    /// Real literal arithmetic is rechecked in Lean against the actual product
    /// sample law and sharp theorem over ALL randomized rules. This output is a
    /// proof document, not acceptance; the existing caller must kernel-check it.
    pub fn lean_certificate(&self, limits: Limits) -> Result<String, Error> {
        if self.trials > limits.trials {
            return Err(Error::Limit { kind: "trials", cap: limits.trials as usize });
        }
        for value in [&self.rate, &self.miss, &self.sum, &self.worst, &self.equal_prior] {
            bounded(value, limits)?;
        }
        let literal = |r: &Rational| format!("({} / {} : ℝ)", r.numer(), r.denom());
        let rate = literal(&self.rate);
        let miss = literal(&self.miss);
        let sum = literal(&self.sum);
        let worst = literal(&self.worst);
        let equal_prior = literal(&self.equal_prior);
        let n = self.trials;
        let source = format!(r#"import ResearchCommons.Calibration.RareEvent
import Mathlib.Tactic.NormNum

namespace ResearchCommons.Generated.RareEvent
open ResearchCommons.Calibration
noncomputable def rate : EventRate := ⟨{rate}, by constructor <;> norm_num⟩
theorem actual_miss : miss rate {n} = {miss} := by
  norm_num [miss, rate]
theorem minimum_sum :
    IsLeast (Set.range (fun d : Decision {n} => nullError d + alternativeError rate d))
      {sum} := by
  simpa only [actual_miss] using sharp_sum_error rate {n}
theorem minimum_worst :
    IsLeast (Set.range (fun d : Decision {n} => max (nullError d) (alternativeError rate d)))
      {worst} := by
  have h := sharp_worst_error rate {n}
  rw [actual_miss] at h
  norm_num at h ⊢
  exact h
theorem minimum_equal_prior :
    IsLeast (Set.range (fun d : Decision {n} => (nullError d + alternativeError rate d) / 2))
      {equal_prior} := by
  have h := sharp_equal_prior_error rate {n}
  rw [actual_miss] at h
  norm_num at h ⊢
  exact h
theorem balanced_rule :
    nullError (thresholdRule {n} (balancedProbability rate {n})) = {worst} ∧
    alternativeError rate (thresholdRule {n} (balancedProbability rate {n})) = {worst} := by
  have h := balanced_rule_errors rate {n}
  rw [actual_miss] at h
  norm_num at h ⊢
  exact h
theorem finite_error_positive (d : Decision {n}) :
    0 < max (nullError d) (alternativeError rate d) :=
  no_finite_certain_decision rate d
end ResearchCommons.Generated.RareEvent
"#);
        if source.len() > limits.render_bytes {
            return Err(Error::Limit { kind: "render_bytes", cap: limits.render_bytes });
        }
        Ok(source)
    }
}
pub fn example_certificate(empty_sample: bool) -> Result<String, Error> {
    let limits = Limits::default();
    Calibration::new(q(1, 4), if empty_sample { 0 } else { 3 }, limits)?
        .lean_certificate(limits)
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn empty_sample_keeps_the_two_criteria_distinct() {
        let l = Limits::default();
        let c = Calibration::new(q(1, 7), 0, l).unwrap();
        assert_eq!(c.miss(), &q(1, 1));
        assert_eq!(c.minimum_sum_error(), &q(1, 1));
        assert_eq!(c.minimum_worst_error(), &q(1, 2));
        assert_eq!(c.minimum_equal_prior_error(), &q(1, 2));
        assert_eq!(c.threshold_errors(&q(0, 1), l).unwrap(), (q(0, 1), q(1, 1)));
        assert_eq!(c.threshold_errors(c.minimum_worst_error(), l).unwrap(), (q(1, 2), q(1, 2)));
    }
    #[test]
    fn exact_rate_and_both_attaining_rules() {
        let l = Limits::default();
        let c = Calibration::new(q(1, 4), 3, l).unwrap();
        assert_eq!(c.miss(), &q(27, 64));
        assert_eq!(c.minimum_worst_error(), &q(27, 91));
        assert_eq!(c.minimum_equal_prior_error(), &q(27, 128));
        let sum_rule = c.threshold_errors(&q(0, 1), l).unwrap();
        let worst_rule = c.threshold_errors(c.minimum_worst_error(), l).unwrap();
        assert_eq!(sum_rule, (q(0, 1), q(27, 64)));
        assert_eq!(worst_rule, (q(27, 91), q(27, 91)));
        assert!(sum_rule.1 > worst_rule.1);
        assert!(worst_rule.0 + worst_rule.1 > *c.minimum_sum_error());
    }
    #[test]
    fn invalid_models_and_resource_refusals_are_explicit() {
        let l = Limits::default();
        for rate in [q(-1, 2), q(0, 1), q(1, 1), q(3, 2)] {
            assert!(matches!(Calibration::new(rate, 3, l), Err(Error::Invalid(_))));
        }
        let tiny = Limits { trials: 2, ..l };
        assert!(matches!(Calibration::new(q(1, 2), 3, tiny), Err(Error::Limit { kind: "trials", .. })));
        let c = Calibration::new(q(1, 4), 3, l).unwrap();
        assert!(matches!(c.threshold_errors(&q(4, 3), l), Err(Error::Invalid(_))));
        assert!(matches!(c.lean_certificate(Limits { render_bytes: 1, ..l }), Err(Error::Limit { kind: "render_bytes", .. })));
        assert!(matches!(Calibration::new(q(1, 4), 100, Limits { rational_chars: 12, ..l }), Err(Error::Limit { kind: "rational_chars", .. })));
    }
}
