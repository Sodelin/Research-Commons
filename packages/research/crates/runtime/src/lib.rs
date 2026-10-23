//! Portable facade over retained exact engines. It adds no source/QE oracle.
#![forbid(unsafe_code)]
pub use g7_exact_law_formula as exact_law;
pub use parity_solver as exact_arithmetic;
pub mod moments;
pub mod affine_certificate;
pub mod source_certificate;
pub mod population_certificate;
pub mod residual_certificate;
pub mod epoch_certificate;

#[cfg(test)]
mod tests {
    use super::{exact_law::*, exact_arithmetic::{polynomial::Polynomial, q}};
    fn finite_problem() -> Problem {
        let k = |n| Polynomial::constant(0, q(n, 1));
        let channels = vec![vec![
            vec![k(1), k(0)],
            vec![k(0), k(1)],
        ]];
        Problem {
            original_hybrid_count: 0,
            rows: vec![vec![]],
            base_observations: 2,
            target_count: 2,
            constants: vec![],
            models: vec![
                SourceModel { parameter_count: 0, target: 0, domain: Predicate::Truth(true), base: vec![k(1), k(0)] },
                SourceModel { parameter_count: 0, target: 1, domain: Predicate::Truth(true), base: vec![k(0), k(1)] },
            ],
            actions: vec![ActionCase {
                parameter_count: 0,
                output_count: 2,
                allowed: Predicate::Truth(true),
                support: vec![0],
                weights: vec![k(1)],
                measurement: Measurement::StochasticChannels(channels),
            }],
        }
    }
    #[test]
    fn actual_existing_engine_builds_guarded_query() {
        let p = finite_problem();
        let b = PathBudget::rectangular(1, 1, 0);
        let c = compile(&p, &b, &[], true, Limits::default()).unwrap();
        assert_eq!(c.retained_horizon(), 1);
        let query = c.wolfram_assertion(AssertionKind::WinningContinuation, AssertionHistory::Reachable).unwrap();
        assert!(query.document().starts_with("Resolve["));
        assert!(!query.has_free_context());
    }
    #[test]
    fn exact_free_history_is_retained() {
        let p = finite_problem();
        let b = PathBudget::rectangular(1, 1, 0);
        let c = compile(&p, &b, &[0], false, Limits::default()).unwrap();
        assert_eq!(c.history_symbols().len(), 1);
        let query = c.wolfram_assertion(AssertionKind::IdentifiedTarget(0), AssertionHistory::Reachable).unwrap();
        assert!(query.has_free_context());
        assert!(c.wolfram_assertion(AssertionKind::IdentifiedTarget(2), AssertionHistory::Reachable).is_err());
    }
    #[test]
    fn original_forcing_width_is_not_relabelled() {
        let mut p = finite_problem();
        p.rows[0] = vec![Some(false)];
        let b = PathBudget::rectangular(1, 1, 0);
        assert!(compile(&p, &b, &[], false, Limits::default()).is_err());
    }
    #[test]
    fn missing_path_regions_are_not_budget_no() {
        let p = finite_problem();
        let b = PathBudget { regions: vec![] };
        assert!(matches!(compile(&p, &b, &[], false, Limits::default()), Err(Error::Invalid(_))));
    }
}

pub mod word_certificate;

pub mod completion_certificate;

pub mod word_cache_certificate;
