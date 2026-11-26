//! Canonical sparse multivariate rational polynomials.
//! Variables retain their original edge/hybrid positions. Multiplication and
//! addition remove exact zero coefficients; no floating point is used.
use crate::{q, Rational};
use std::collections::BTreeMap;
use num_traits::Zero;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Polynomial {
    pub dimension: usize,
    pub terms: BTreeMap<Vec<usize>, Rational>,
}

impl Polynomial {
    pub fn zero(dimension: usize) -> Self { Self { dimension, terms: BTreeMap::new() } }
    pub fn constant(dimension: usize, coefficient: Rational) -> Self {
        let mut value = Self::zero(dimension);
        if !coefficient.is_zero() { value.terms.insert(vec![0; dimension], coefficient); }
        value
    }
    pub fn one(dimension: usize) -> Self { Self::constant(dimension, q(1, 1)) }
    pub fn monomial(dimension: usize, variable: usize, power: usize, coefficient: Rational)
        -> Result<Self, &'static str> {
        if variable >= dimension { return Err("POLYNOMIAL_VARIABLE"); }
        let mut value = Self::zero(dimension);
        if !coefficient.is_zero() {
            let mut powers = vec![0; dimension];
            powers[variable] = power;
            value.terms.insert(powers, coefficient);
        }
        Ok(value)
    }
    pub fn variable(dimension: usize, variable: usize) -> Result<Self, &'static str> {
        Self::monomial(dimension, variable, 1, q(1, 1))
    }
    pub fn is_zero(&self) -> bool { self.terms.is_empty() }
    fn accumulate(&mut self, powers: Vec<usize>, coefficient: Rational) {
        if coefficient.is_zero() { return; }
        let sum = self.terms.get(&powers).cloned().unwrap_or_else(|| q(0, 1)) + coefficient;
        if sum.is_zero() { self.terms.remove(&powers); }
        else { self.terms.insert(powers, sum); }
    }
    pub fn add(&self, other: &Self) -> Result<Self, &'static str> {
        if self.dimension != other.dimension { return Err("POLYNOMIAL_DIMENSION"); }
        let mut sum = self.clone();
        for (powers, coefficient) in &other.terms { sum.accumulate(powers.clone(), coefficient.clone()); }
        Ok(sum)
    }
    pub fn scale(&self, factor: &Rational) -> Self {
        if factor.is_zero() { return Self::zero(self.dimension); }
        Self { dimension: self.dimension,
            terms: self.terms.iter().map(|(powers, coefficient)| (powers.clone(), coefficient * factor)).collect() }
    }
    pub fn subtract(&self, other: &Self) -> Result<Self, &'static str> {
        self.add(&other.scale(&q(-1, 1)))
    }
    pub fn multiply(&self, other: &Self) -> Result<Self, &'static str> {
        if self.dimension != other.dimension { return Err("POLYNOMIAL_DIMENSION"); }
        let mut product = Self::zero(self.dimension);
        for (a, ca) in &self.terms {
            for (b, cb) in &other.terms {
                let powers = a.iter().zip(b).map(|(x, y)| x.checked_add(*y).ok_or("POLYNOMIAL_EXPONENT"))
                    .collect::<Result<Vec<_>, _>>()?;
                product.accumulate(powers, ca * cb);
            }
        }
        Ok(product)
    }
    pub fn power(&self, exponent: usize) -> Result<Self, &'static str> {
        let mut result = Self::one(self.dimension);
        for _ in 0..exponent { result = result.multiply(self)?; }
        Ok(result)
    }
    pub fn evaluate(&self, values: &[Rational]) -> Result<Rational, &'static str> {
        if values.len() != self.dimension { return Err("POLYNOMIAL_ASSIGNMENT"); }
        self.terms.iter().try_fold(q(0, 1), |sum, (powers, coefficient)| {
            let mut term = coefficient.clone();
            for (value, power) in values.iter().zip(powers) {
                let exponent = i32::try_from(*power).map_err(|_| "POLYNOMIAL_EXPONENT")?;
                term *= value.pow(exponent);
            }
            Ok(sum + term)
        })
    }
}
