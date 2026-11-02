//! Strict Fourier–Motzkin projection and deterministic rational reconstruction.
//! Row/projection semantics reuse dot's StrictAffineElimination.lean. The
//! executable ordering is RC1: zero rows, then positive outer / negative inner.
use crate::{q, Rational};
use num_traits::Zero;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    pub coefficients: Vec<Rational>,
    pub bound: Rational,
    pub strict: bool,
}

impl Row {
    pub fn evaluate(&self, assignment: &[Rational]) -> Option<Rational> {
        if assignment.len() != self.coefficients.len() { return None; }
        Some(self.coefficients.iter().zip(assignment)
            .fold(Rational::zero(), |sum, (a, x)| sum + a * x))
    }
    pub fn holds(&self, assignment: &[Rational]) -> bool {
        self.evaluate(assignment).is_some_and(|value|
            if self.strict { value < self.bound } else { value <= self.bound })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Witness(Vec<Rational>),
    /// Nonnegative combination of original rows yielding a contradiction.
    Exclusion(Vec<Rational>),
    /// A resource limit never implies infeasibility.
    Unknown { dimension: usize, required_rows: usize, cap: usize },
}

#[derive(Clone, Debug)]
struct TrackedRow { row: Row, weights: Vec<Rational> }

/// All rows must have the same declared dimension. A cap limits the number of
/// rows at each *projected* stage, not the input row count or elapsed time.
pub fn solve(n: usize, rows: &[Row], cap: usize) -> Result<Decision, &'static str> {
    if rows.iter().any(|r| r.coefficients.len() != n) { return Err("ROW_DIMENSION"); }
    let originals = rows.len();
    let initial: Vec<_> = rows.iter().enumerate().map(|(i, row)| TrackedRow {
        row: row.clone(),
        weights: (0..originals).map(|j| q(i64::from(i == j), 1)).collect(),
    }).collect();
    let mut stages = vec![initial];
    for dimension in (1..=n).rev() {
        let current = stages.last().unwrap();
        let mut zeros = Vec::new();
        let mut positive = Vec::new();
        let mut negative = Vec::new();
        for r in current {
            let a = &r.row.coefficients[dimension - 1];
            if a.is_zero() { zeros.push(r); }
            else if a > &q(0, 1) { positive.push(r); }
            else { negative.push(r); }
        }
        let needed = positive.len().checked_mul(negative.len())
            .and_then(|pairs| zeros.len().checked_add(pairs));
        if needed.is_none_or(|size| size > cap) {
            return Ok(Decision::Unknown { dimension, required_rows: needed.unwrap_or(usize::MAX), cap });
        }
        let mut next = Vec::with_capacity(needed.unwrap());
        for r in zeros {
            let mut copy = r.clone();
            copy.row.coefficients.pop();
            next.push(copy);
        }
        for p in &positive {
            for m in &negative {
                let ap = &p.row.coefficients[dimension - 1];
                let am = -&m.row.coefficients[dimension - 1];
                let coefficients = (0..dimension - 1)
                    .map(|i| &am * &p.row.coefficients[i] + ap * &m.row.coefficients[i])
                    .collect();
                let bound = &am * &p.row.bound + ap * &m.row.bound;
                let weights = p.weights.iter().zip(&m.weights)
                    .map(|(wp, wm)| &am * wp + ap * wm).collect();
                next.push(TrackedRow {
                    row: Row { coefficients, bound, strict: m.row.strict || p.row.strict },
                    weights,
                });
            }
        }
        stages.push(next);
    }
    // Pick the first contradiction in the declared projection order.
    if let Some(r) = stages.last().unwrap().iter().find(|r| !r.row.holds(&[])) {
        if !check_exclusion(n, rows, &r.weights) { return Err("INTERNAL_EXCLUSION"); }
        return Ok(Decision::Exclusion(r.weights.clone()));
    }
    let mut assignment = Vec::with_capacity(n);
    for dimension in 1..=n {
        let current = &stages[n - dimension];
        let mut lower: Option<Rational> = None;
        let mut upper: Option<Rational> = None;
        for r in current {
            let a = &r.row.coefficients[dimension - 1];
            if a.is_zero() { continue; }
            let rest = r.row.coefficients[..dimension - 1].iter().zip(&assignment)
                .fold(q(0, 1), |sum, (coefficient, x)| sum + coefficient * x);
            let endpoint = (&r.row.bound - rest) / a;
            if a < &q(0, 1) {
                lower = Some(lower.map_or(endpoint.clone(), |old| old.max(endpoint)));
            } else {
                upper = Some(upper.map_or(endpoint.clone(), |old| old.min(endpoint)));
            }
        }
        let next = match (lower, upper) {
            (Some(a), Some(b)) if a < b => (a + b) / q(2, 1),
            (Some(a), Some(b)) if a == b => a,
            (Some(_), Some(_)) => return Err("INTERNAL_RECONSTRUCTION"),
            (Some(a), None) => a + q(1, 1),
            (None, Some(b)) => b - q(1, 1),
            (None, None) => q(0, 1),
        };
        assignment.push(next);
        if current.iter().any(|r| !r.row.holds(&assignment)) {
            return Err("INTERNAL_RECONSTRUCTION");
        }
    }
    if !check_witness(n, rows, &assignment) { return Err("INTERNAL_WITNESS"); }
    Ok(Decision::Witness(assignment))
}

/// Independent verification performs only original-row dot products. It does
/// not call solve or reconstruct a search trajectory.
pub fn check_witness(n: usize, rows: &[Row], assignment: &[Rational]) -> bool {
    assignment.len() == n && rows.iter().all(|r|
        r.coefficients.len() == n && r.holds(assignment))
}

/// A strict contradiction requires a *positive* coefficient on at least one
/// strict original row; a zero multiplier cannot turn a weak row into strict.
pub fn check_exclusion(n: usize, rows: &[Row], weights: &[Rational]) -> bool {
    if rows.len() != weights.len() || rows.iter().any(|r| r.coefficients.len() != n)
        || weights.iter().any(|w| w < &q(0, 1)) { return false; }
    let coefficients: Vec<_> = (0..n).map(|i| rows.iter().zip(weights)
        .fold(q(0, 1), |sum, (r, w)| sum + &r.coefficients[i] * w)).collect();
    if coefficients.iter().any(|a| !a.is_zero()) { return false; }
    let bound = rows.iter().zip(weights)
        .fold(q(0, 1), |sum, (r, w)| sum + &r.bound * w);
    let strict = rows.iter().zip(weights).any(|(r, w)| r.strict && w > &q(0, 1));
    bound < q(0, 1) || (strict && bound == q(0, 1))
}
