//! Exact normalized Poisson-prefix certificate, compatibility algorithm v1.
//!
//! `RESOURCE_LIMIT` has no negative source/target implication. This is a
//! numerical input-layer component, not a biological-source construction,
//! scientific admission, or Lean-verified result. See README for CLI limits.
#![forbid(unsafe_code)]

pub use num_bigint::{BigInt, BigUint};
pub use num_rational::BigRational as Rational;
use num_traits::{One, Zero};
use std::error::Error;
use std::fmt;

pub mod parse;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InvalidInput;

impl fmt::Display for InvalidInput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Require a >= 0 and 0 < epsilon < 1.")
    }
}
impl Error for InvalidInput {}

/// The success fields cannot be constructed or changed by external callers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Certified {
    a: Rational,
    epsilon: Rational,
    k: BigUint,
    s: Rational,
    t: Rational,
    u: Rational,
    delta: Rational,
    inspected: BigUint,
}

impl Certified {
    pub fn a(&self) -> &Rational { &self.a }
    pub fn epsilon(&self) -> &Rational { &self.epsilon }
    pub fn k(&self) -> &BigUint { &self.k }
    pub fn s(&self) -> &Rational { &self.s }
    pub fn t(&self) -> &Rational { &self.t }
    pub fn u(&self) -> &Rational { &self.u }
    pub fn delta(&self) -> &Rational { &self.delta }
    pub fn inspected(&self) -> &BigUint { &self.inspected }
    pub fn weights(&self) -> Vec<Rational> {
        // certify guarantees nonnegative a.
        weights_nonnegative(&self.a, &self.k)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceLimit {
    a: Rational,
    epsilon: Rational,
    inspected: BigUint,
    next_k: BigUint,
}
impl ResourceLimit {
    pub fn a(&self) -> &Rational { &self.a }
    pub fn epsilon(&self) -> &Rational { &self.epsilon }
    pub fn inspected(&self) -> &BigUint { &self.inspected }
    pub fn next_k(&self) -> &BigUint { &self.next_k }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome {
    Certified(Certified),
    ResourceLimit(ResourceLimit),
}

/// Return the first qualifying cutoff, or the exact inspected-cutoff limit.
///
/// Counters and arithmetic are arbitrary precision. `None` is an unbounded
/// mathematical search, not a wall-time, memory, or allocator guarantee.
/// `Some(0)` inspects no candidates. No hidden cap changes the count law.
pub fn certify(
    a: &Rational,
    epsilon: &Rational,
    max_steps: Option<&BigUint>,
) -> Result<Outcome, InvalidInput> {
    let canonical_a = canonical(a)?;
    let canonical_epsilon = canonical(epsilon)?;
    let a = &canonical_a;
    let epsilon = &canonical_epsilon;
    if a < &Rational::zero() || epsilon <= &Rational::zero() || epsilon >= &Rational::one() {
        return Err(InvalidInput);
    }
    let mut k = BigUint::zero();
    let mut term = Rational::one();
    let mut prefix = Rational::one();
    let mut inspected = BigUint::zero();
    let two_a = a * Rational::from_integer(BigInt::from(2u8));
    while max_steps.map_or(true, |limit| &inspected < limit) {
        let divisor = Rational::from_integer(BigInt::from(&k + BigUint::one()));
        let next_term = &term * a / divisor;
        let twice_next = &next_term * Rational::from_integer(BigInt::from(2u8));
        let upper = &prefix + &twice_next;
        let delta = &twice_next / &upper;
        inspected += BigUint::one();
        let cutoff_guard = Rational::from_integer(BigInt::from(&k + BigUint::from(2u8)));
        if cutoff_guard >= two_a && &delta <= epsilon {
            return Ok(Outcome::Certified(Certified {
                a: a.clone(), epsilon: epsilon.clone(), k,
                s: prefix, t: next_term, u: upper, delta, inspected,
            }));
        }
        k += BigUint::one();
        term = next_term;
        prefix += &term;
    }
    Ok(Outcome::ResourceLimit(ResourceLimit {
        a: a.clone(), epsilon: epsilon.clone(), inspected, next_k: k,
    }))
}

/// Exact normalized-prefix weights. No residual mass is assigned to zero.
/// A natural cutoff is encoded by BigUint, so negative/bool cutoffs cannot occur.
pub fn weights(a: &Rational, k: &BigUint) -> Result<Vec<Rational>, InvalidInput> {
    let canonical_a = canonical(a)?;
    let a = &canonical_a;
    if a < &Rational::zero() {
        return Err(InvalidInput);
    }
    Ok(weights_nonnegative(a, k))
}

fn canonical(value: &Rational) -> Result<Rational, InvalidInput> {
    if value.denom().is_zero() { return Err(InvalidInput); }
    Ok(Rational::new(value.numer().clone(), value.denom().clone()))
}

fn weights_nonnegative(a: &Rational, k: &BigUint) -> Vec<Rational> {
    let mut terms = vec![Rational::one()];
    let mut term = Rational::one();
    let mut total = Rational::one();
    let mut i = BigUint::zero();
    while &i < k {
        i += BigUint::one();
        term = term * a / Rational::from_integer(BigInt::from(i.clone()));
        total += &term;
        terms.push(term.clone());
    }
    terms.into_iter().map(|term| term / &total).collect()
}

impl Outcome {
    /// Python-compatible legacy JSON object (stable sorted-key rendering).
    /// Exact rational fields are strings; legacy cutoff counters are JSON integers.
    /// Weight construction has the same optional, post-certification timing.
    pub fn to_legacy_json(&self, include_weights: bool) -> String {
        match self {
            Self::Certified(c) => {
                let mut fields = vec![
                    format!("\"K\": {}", c.k),
                    format!("\"S\": \"{}\"", c.s),
                    format!("\"T\": \"{}\"", c.t),
                    format!("\"U\": \"{}\"", c.u),
                    format!("\"a\": \"{}\"", c.a),
                    format!("\"delta\": \"{}\"", c.delta),
                    format!("\"epsilon\": \"{}\"", c.epsilon),
                    format!("\"inspected\": {}", c.inspected),
                    "\"law\": \"normalized_prefix\"".to_owned(),
                    "\"status\": \"CERTIFIED\"".to_owned(),
                ];
                if include_weights {
                    let values: Vec<String> = c.weights().iter().map(|v| format!("\"{v}\"")).collect();
                    fields.push(format!("\"weights\": [{}]", values.join(", ")));
                }
                format!("{{{}}}", fields.join(", "))
            }
            Self::ResourceLimit(r) => format!(
                "{{\"a\": \"{}\", \"epsilon\": \"{}\", \"inspected\": {}, \"law\": \"normalized_prefix\", \"next_K\": {}, \"status\": \"RESOURCE_LIMIT\"}}",
                r.a, r.epsilon, r.inspected, r.next_k,
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn q(s: &str) -> Rational { parse::rational(s).unwrap() }
    fn run(a: &str, e: &str, n: Option<u32>) -> Outcome {
        certify(&q(a), &q(e), n.map(BigUint::from).as_ref()).unwrap()
    }
    #[test]
    fn zero_and_zero_budget() {
        assert!(matches!(run("0", "1/100", Some(0)), Outcome::ResourceLimit(_)));
        let Outcome::Certified(c) = run("0", "1/100", Some(1)) else { panic!() };
        assert_eq!(c.k(), &BigUint::zero());
        assert_eq!(c.s(), &q("1")); assert_eq!(c.t(), &q("0"));
        assert_eq!(c.u(), &q("1")); assert_eq!(c.delta(), &q("0"));
        assert_eq!(c.inspected(), &BigUint::one());
        assert_eq!(c.weights(), vec![q("1")]);
    }
    #[test]
    fn both_inequalities_include_equality() {
        let Outcome::Certified(c) = run("1", "2/3", None) else { panic!() };
        assert_eq!(c.k(), &BigUint::zero());
        assert_eq!(c.delta(), &q("2/3"));
        assert!(matches!(run("1", "665/1000", Some(1)), Outcome::ResourceLimit(_)));
    }
    #[test]
    fn geometric_guard_is_not_optional() {
        // At K=0 delta=4/5 fits epsilon, but K+2 < 2a.
        assert!(matches!(run("2", "9/10", Some(2)), Outcome::ResourceLimit(_)));
        let Outcome::Certified(c) = run("2", "9/10", Some(3)) else { panic!() };
        assert_eq!(c.k(), &BigUint::from(2u8));
    }
    #[test]
    fn first_cutoff_and_budget_boundary() {
        let Outcome::ResourceLimit(r) = run("1", "1/2", Some(1)) else { panic!() };
        assert_eq!(r.next_k(), &BigUint::one()); assert_eq!(r.inspected(), &BigUint::one());
        assert_eq!(run("1", "1/2", Some(2)), run("1", "1/2", None));
        let Outcome::Certified(c) = run("1", "1/2", None) else { panic!() };
        assert_eq!(c.k(), &BigUint::one());
        assert_eq!(c.s(), &q("2")); assert_eq!(c.t(), &q("1/2"));
        assert_eq!(c.u(), &q("3")); assert_eq!(c.delta(), &q("1/3"));
        assert_eq!(c.weights(), vec![q("1/2"), q("1/2")]);
    }
    #[test]
    fn domain_rejections_are_not_resource_limits() {
        for (a,e) in [("-1","1/2"),("0","0"),("0","1"),("0","2"),("0","-1")] {
            assert!(certify(&q(a), &q(e), Some(&BigUint::zero())).is_err());
        }
        assert!(weights(&q("-1"), &BigUint::zero()).is_err());
    }
    #[test]
    fn arbitrary_precision_and_exact_weights() {
        let n = "340282366920938463463374607431768211457";
        assert_eq!(q(&format!("{n}/{n}")), q("1"));
        let w = weights(&q("5/3"), &BigUint::from(12u8)).unwrap();
        assert_eq!(w.iter().cloned().sum::<Rational>(), q("1"));
        for i in 1..w.len() { assert_eq!(&w[i] / &w[i-1], q("5/3") / Rational::from_integer(BigInt::from(i))); }
    }
    #[test]
    fn raw_ratio_inputs_cannot_skip_canonicalization() {
        let raw = Rational::new_raw(BigInt::from(2), BigInt::from(2));
        assert_eq!(certify(&raw, &q("2/3"), None).unwrap(), run("1", "2/3", None));
        let negative_denominator = Rational::new_raw(BigInt::from(-2), BigInt::from(-2));
        let unreduced_epsilon = Rational::new_raw(BigInt::from(4), BigInt::from(6));
        assert_eq!(certify(&negative_denominator, &unreduced_epsilon, None).unwrap(), run("1", "2/3", None));
        let zero_denominator = Rational::new_raw(BigInt::one(), BigInt::zero());
        assert!(certify(&zero_denominator, &q("1/2"), None).is_err());
    }
    #[test]
    fn legacy_serialization_and_limit_omit_weights() {
        assert_eq!(run("1", "2/3", None).to_legacy_json(true),
            "{\"K\": 0, \"S\": \"1\", \"T\": \"1\", \"U\": \"3\", \"a\": \"1\", \"delta\": \"2/3\", \"epsilon\": \"2/3\", \"inspected\": 1, \"law\": \"normalized_prefix\", \"status\": \"CERTIFIED\", \"weights\": [\"1\"]}");
        assert!(!run("0", "1/2", Some(0)).to_legacy_json(true).contains("weights"));
    }
}
