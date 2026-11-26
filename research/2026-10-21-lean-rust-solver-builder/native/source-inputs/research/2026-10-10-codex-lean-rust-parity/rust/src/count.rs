//! Arithmetic gate of the inherited conditional zero-score bound.
//! Provider/source completeness is deliberately not inferred by arithmetic.
use crate::{q, Rational};
use num_bigint::BigInt;
use num_integer::Integer;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConditionalCount { pub delta: Rational, pub bound: Rational, pub ceiling: BigInt }

pub fn conditional_count(b: &Rational, epsilon: &Rational, sigma: &Rational,
    modulus: &Rational) -> Result<ConditionalCount, &'static str> {
    if b <= &q(0, 1) || epsilon <= &q(0, 1) || sigma <= &q(0, 1) || modulus < &q(0, 1) {
        return Err("COUNT_DOMAIN");
    }
    let delta = epsilon.clone().min(sigma / (q(2, 1) * (modulus + q(1, 1))));
    let bound = q(2, 1) * (q(1, 1) + &delta) / (b * &delta);
    let ceiling = bound.numer().div_ceil(bound.denom());
    Ok(ConditionalCount { delta, bound, ceiling })
}
