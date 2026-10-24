//! Exact native receiver for OLD strict-half RAW NANUQ recovery.
//! Prior theorem/review/finite JS implementation are recorded in the reuse
//! preflight. This is not an estimator, circle finder or source admission.
use parity_solver::{q, Rational};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub taxa: usize,
    pub cells: usize,
    pub rational_chars: usize,
    pub render_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self { taxa: 64, cells: 4096, rational_chars: 4096, render_bytes: 262144 }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    Unknown(&'static str),
    HalfTie { row: usize, column: usize },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CutCoefficient {
    /// Literal supplied circular positions, as in the retained exact-query engine.
    pub gaps: [usize; 2],
    /// Original unhalved alpha; the split weight is alpha/2.
    pub alpha: Rational,
}
#[derive(Clone, Debug)]
pub struct Recovery {
    labels: Vec<u64>,
    observed: Vec<Vec<Rational>>,
    integer: Vec<Vec<Rational>>,
}
fn abs(x: Rational) -> Rational {
    if x < q(0, 1) { -x } else { x }
}
fn bounded(x: &Rational, limits: Limits) -> bool {
    x.numer().to_string().len() <= limits.rational_chars &&
        x.denom().to_string().len() <= limits.rational_chars
}
/// FLOOR(x+1/2), with exact signed arithmetic. Ties are explicitly refused:
/// a selected integer at a tie would not certify the strict source promise.
fn snap(x: &Rational) -> Option<Rational> {
    let shifted = x + q(1, 2);
    let trunc = shifted.to_integer();
    let value = Rational::from_integer(trunc.clone());
    let floor = if shifted < q(0, 1) && shifted != value { trunc - 1 } else { trunc };
    let result = Rational::from_integer(floor);
    if abs(x - &result) == q(1, 2) { None } else { Some(result) }
}
impl Recovery {
    /// Consume ONE complete matrix and its literal supplied taxon/circle order.
    /// Noise may be asymmetric or negative, including diagonal observations.
    /// No source or order correctness follows from successful arithmetic.
    pub fn new(labels: Vec<u64>, observed: Vec<Vec<Rational>>, limits: Limits)
        -> Result<Self, Error>
    {
        let n = labels.len();
        let cells = n.checked_mul(n).ok_or(Error::Unknown("matrix dimension overflow"))?;
        if n > limits.taxa || cells > limits.cells {
            return Err(Error::Unknown("matrix profile limit"));
        }
        if observed.len() != n || observed.iter().any(|r| r.len() != n) {
            return Err(Error::Invalid("complete square matrix required"));
        }
        if labels.iter().copied().collect::<BTreeSet<_>>().len() != n {
            return Err(Error::Invalid("distinct original taxon labels required"));
        }
        let mut integer = Vec::with_capacity(n);
        for (i, row) in observed.iter().enumerate() {
            let mut out = Vec::with_capacity(n);
            for (j, x) in row.iter().enumerate() {
                if !bounded(x, limits) { return Err(Error::Unknown("input rational limit")); }
                let k = snap(x).ok_or(Error::HalfTie { row: i, column: j })?;
                if !bounded(&k, limits) { return Err(Error::Unknown("integer magnitude limit")); }
                // Defense at the actual returned value, not a float/residual proxy.
                if abs(x - &k) >= q(1, 2) {
                    return Err(Error::Invalid("internal exact rounding invariant"));
                }
                out.push(k);
            }
            integer.push(out);
        }
        Ok(Self { labels, observed, integer })
    }
    pub fn labels(&self) -> &[u64] { &self.labels }
    pub fn observed(&self) -> &[Vec<Rational>] { &self.observed }
    pub fn integers(&self) -> &[Vec<Rational>] { &self.integer }

    /// Reuse the literal OLD WeightedCoefficients.circularAlpha formula.
    /// Returns ALL upper gap pairs in original position order, with signed
    /// coefficients. Negative values are not a source-class NO conclusion.
    pub fn cut_coefficients(&self) -> Vec<CutCoefficient> {
        let n = self.labels.len();
        let mut result = Vec::new();
        for i in 0..n {
            let ni = if i + 1 == n { 0 } else { i + 1 };
            for j in i + 1..n {
                let nj = if j + 1 == n { 0 } else { j + 1 };
                result.push(CutCoefficient { gaps: [i, j],
                    alpha: &self.integer[i][j] + &self.integer[ni][nj]
                        - &self.integer[i][nj] - &self.integer[ni][j] });
            }
        }
        result
    }
    pub fn positive_gap_pairs(&self) -> Vec<[usize; 2]> {
        self.cut_coefficients().into_iter().filter(|x| x.alpha > q(0, 1))
            .map(|x| x.gaps).collect()
    }

    /// Complete input/output proof. Generic uniqueness covers ANY integer
    /// source matrix satisfying the SAME strict entrywise error promise.
    /// Source admission and supplied correct circle remain explicit downstream.
    pub fn lean_certificate(&self, namespace: &str, limits: Limits)
        -> Result<String, Error>
    {
        if namespace.is_empty() || namespace.len() > 120 ||
            !namespace.bytes().enumerate().all(|(i, c)|
                c == b'_' || c.is_ascii_alphabetic() || (i > 0 && c.is_ascii_digit())) {
            return Err(Error::Invalid("simple Lean namespace required"));
        }
        let n = self.labels.len();
        if n > limits.taxa || n.checked_mul(n).is_none_or(|x| x > limits.cells) {
            return Err(Error::Unknown("certificate matrix profile limit"));
        }
        if self.observed.iter().chain(self.integer.iter()).flatten()
            .any(|x| !bounded(x, limits)) {
            return Err(Error::Unknown("certificate rational limit"));
        }
        let rat = |x: &Rational| format!("({} / {} : ℚ)", x.numer(), x.denom());
        let int = |x: &Rational| format!("({} : ℤ)", x.numer());
        let grid = |matrix: &[Vec<Rational>], is_int: bool| {
            if n == 0 { return "fun i => Fin.elim0 i".to_string(); }
            let rows = matrix.iter().map(|row| {
                let cells = row.iter().map(|x| if is_int { int(x) } else { rat(x) })
                    .collect::<Vec<_>>().join(", ");
                format!("![{cells}]")
            }).collect::<Vec<_>>().join(", ");
            format!("![{rows}]")
        };
        let labels = if n == 0 { "fun i => Fin.elim0 i".to_string() }
            else { format!("![{}]", self.labels.iter().map(u64::to_string)
                .collect::<Vec<_>>().join(", ")) };
        let cases = if n == 0 { "intro i; exact Fin.elim0 i" }
            else { "intro i j; fin_cases i <;> fin_cases j <;> norm_num [observed, recovered]" };
        let positives = self.positive_gap_pairs().iter()
            .map(|[i, j]| format!("({i}, {j})")).collect::<Vec<_>>().join(", ");
        let support_proof = if n == 0 { "intro i; exact Fin.elim0 i" }
            else { "intro i j; fin_cases i <;> fin_cases j <;> norm_num [returnedPositive, recovered, Nanuq.Weighted.circularAlpha, Nanuq.Weighted.cyclicNext]" };
        let observed = grid(&self.observed, false);
        let recovered = grid(&self.integer, true);
        let source = format!(r#"import ResearchCommons.NANUQ.RawNoise
namespace ResearchCommons.Generated.{namespace}
open ResearchCommons.NANUQ.RawNoise
def labels : Fin {n} → ℕ := {labels}
def observed : Fin {n} → Fin {n} → ℚ := {observed}
def recovered : Fin {n} → Fin {n} → ℤ := {recovered}
theorem input_labels_injective : Function.Injective labels := by decide +kernel
theorem returned_strict_errors :
    ∀ i j, |observed i j - (recovered i j : ℚ)| < 1 / 2 := by
  {cases}
theorem actual_native_rounding :
    (fun i j => round (observed i j)) = recovered :=
  integer_matrix_rounding observed recovered returned_strict_errors
theorem any_promised_integer_source (truth : Fin {n} → Fin {n} → ℤ)
    (noise : ∀ i j, |observed i j - (truth i j : ℚ)| < 1 / 2) :
    truth = recovered :=
  (integer_matrix_rounding observed truth noise).symm.trans actual_native_rounding
def returnedPositive : Finset (Fin {n} × Fin {n}) := {{{positives}}}
theorem entire_returned_support :
    ∀ i j, (i,j) ∈ returnedPositive ↔
      i < j ∧ 0 < Nanuq.Weighted.circularAlpha (fun a b => (recovered a b : ℚ)) i j := by
  {support_proof}
end ResearchCommons.Generated.{namespace}
"#);
        if source.len() > limits.render_bytes {
            return Err(Error::Unknown("complete proof document limit"));
        }
        Ok(source)
    }
}
/// Two fixed public readouts from the OLD four-taxon sharpness witness.
/// This reuses their literal matrices; no graph/source producer is run.
pub fn example(cycle: bool, limits: Limits) -> Result<Recovery, Error> {
    let raw = if cycle {
        [[0,5,6,5], [5,0,5,6], [6,5,0,5], [5,6,5,0]]
    } else {
        [[0,4,6,6], [4,0,6,6], [6,6,0,4], [6,6,4,0]]
    };
    let observed = raw.iter().enumerate().map(|(i, row)|
        row.iter().enumerate().map(|(j, &v)| q(v,1) +
            if i <= j { q(-1,4) } else { q(1,3) })
            .collect()).collect();
    Recovery::new(vec![900,7,42,123], observed, limits)
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn same_old_tree_cycle_matrices_and_complete_support() {
        let t = example(false, Limits::default()).unwrap();
        let c = example(true, Limits::default()).unwrap();
        assert_eq!(t.labels(), &[900,7,42,123]);
        assert_eq!(t.integers()[0][1], q(4,1));
        assert_eq!(c.integers()[0][1], q(5,1));
        assert!(t.observed()[0][0] < q(0,1));
        assert_ne!(t.observed()[0][1], t.observed()[1][0]);
        let alpha = |r: &Recovery| r.cut_coefficients().into_iter()
            .find(|x| x.gaps == [0,2]).unwrap().alpha;
        assert_eq!(alpha(&t), q(0,1));
        assert_eq!(alpha(&c), q(2,1));
        assert_eq!(t.cut_coefficients().len(), 6);
        assert_ne!(t.positive_gap_pairs(), c.positive_gap_pairs());
        for r in [&t, &c] {
            for i in 0..4 { for j in 0..4 {
                assert!(abs(&r.observed()[i][j] - &r.integers()[i][j]) < q(1,2));
            }}
        }
    }
    #[test]
    fn signed_exact_rounding_and_closed_half_refusal() {
        for k in -40..=40 {
            for e in [q(-499,1000), q(-1,4), q(0,1), q(1,3), q(499,1000)] {
                assert_eq!(snap(&(q(k,1) + e)), Some(q(k,1)));
            }
            assert_eq!(snap(&(q(k,1) + q(1,2))), None);
            assert_eq!(snap(&(q(k,1) - q(1,2))), None);
        }
        assert!(matches!(Recovery::new(vec![0], vec![vec![q(9,2)]], Limits::default()),
            Err(Error::HalfTie { row: 0, column: 0 })));
    }
    #[test]
    fn shape_labels_empty_and_resource_refusals() {
        let l = Limits::default();
        assert!(matches!(Recovery::new(vec![1], vec![], l), Err(Error::Invalid(_))));
        assert!(matches!(Recovery::new(vec![1,1], vec![vec![q(0,1);2];2], l), Err(Error::Invalid(_))));
        assert!(matches!(Recovery::new(vec![1], vec![vec![q(0,1)]],
            Limits { cells: 0, ..l }), Err(Error::Unknown(_))));
        let empty = Recovery::new(vec![], vec![], l).unwrap();
        assert!(empty.cut_coefficients().is_empty());
        let r = example(false,l).unwrap();
        assert!(matches!(r.lean_certificate("bad.namespace",l), Err(Error::Invalid(_))));
        assert!(matches!(r.lean_certificate("X",Limits { render_bytes: 1, ..l }), Err(Error::Unknown(_))));
        let proof = r.lean_certificate("RawNoiseTree",l).unwrap();
        assert!(proof.contains("any_promised_integer_source"));
        assert!(proof.contains("entire_returned_support"));
        assert!(proof.contains("![900, 7, 42, 123]"));
        assert!(!proof.contains("sorry"));
    }
}
