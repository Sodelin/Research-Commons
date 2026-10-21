//! Typed, in-memory access to the ORIGINAL native CHART row compiler.
//!
//! SOURCE ONLY: not compiled or executed. Link to a freshly authenticated
//! parity_solver from the existing 51-file restoration/build contract.
//! No solver, canonical task, source admission, parser refinement, process,
//! file, log, network, new word grammar or certificate is introduced here.
#![forbid(unsafe_code)]

use parity_solver::affine::Row;
use parity_solver::natural_cell::{self, Chart, Compiled, Population};
use parity_solver::protocol::{self, Request};

pub const MAX_DIMENSION: usize = 32;
pub const MAX_ORIGINAL_ROWS: usize = 128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExportError {
    InvalidRequest(&'static str),
    ChartRequestRequired,
    OriginalCompilerRefused(&'static str),
    CompilerShapeChanged,
}

/// One captured request and its exact original compiler result.
/// Private fields keep accessors bound to the same input, registry and rows.
/// This is a mathematical native cell snapshot, NOT a Lean source-admission
/// proof or an authenticated claim that an external native process ran.
#[derive(Clone, Debug)]
pub struct CompiledCellRows {
    original_request: Vec<u8>,
    chart: Chart,
    compiled: Compiled,
}

impl CompiledCellRows {
    pub fn original_request(&self) -> &[u8] {
        &self.original_request
    }

    /// Original integer occurrence identities and port order are unchanged.
    /// Mapping these to a typed RootedBinary and effective complete registries
    /// remains a separate Lean obligation.
    pub fn original_chart(&self) -> &Chart {
        &self.chart
    }

    pub fn dimension(&self) -> usize {
        self.compiled.dimension
    }

    /// This cap belongs to a future solver call. Export does not run a solver.
    pub fn projection_cap(&self) -> usize {
        self.chart.cap
    }

    /// Preserves EVERY original compiler row in its exact block/list order.
    /// Do not sort, deduplicate, truncate or reinterpret the weight indexing.
    pub fn rows(&self) -> &[Row] {
        &self.compiled.rows
    }

    /// Historical RATE labels mean inverse pair rates u, not actual rho=1/u.
    /// COIN labels alone do not establish a parent0/parent1 routing convention.
    pub fn original_bank_names(&self) -> &[String] {
        &self.compiled.bank_names
    }

    pub fn age_coordinate(&self, vertex: usize) -> Option<usize> {
        (vertex < self.chart.source.vertices).then_some(vertex)
    }

    pub fn inverse_pair_rate_coordinate(&self, population: Population) -> Option<usize> {
        if matches!(population, Population::Edge(e) if e >= self.chart.source.edges.len()) {
            return None;
        }
        Some(self.chart.source.population_index(population))
    }

    /// Exactly the SAME one ancestral population slot, not one per exposure.
    pub fn ancestral_inverse_pair_rate_coordinate(&self) -> usize {
        self.chart.source.population_index(Population::Ancestral)
    }

    pub fn coin_coordinate(&self, hybrid: usize) -> Option<usize> {
        (hybrid < self.chart.source.hybrids.len())
            .then(|| self.chart.source.coin_index(hybrid))
    }
}

/// Parse through the ORIGINAL RC1 grammar and call ONLY the original row
/// compiler. There is no affine projection/search or source-feasibility result.
/// Every error is refusal/unavailability of this export, never mathematical NO.
pub fn compile_request(original_request: &[u8]) -> Result<CompiledCellRows, ExportError> {
    let chart = match protocol::parse(original_request).map_err(ExportError::InvalidRequest)? {
        Request::Chart(chart) => chart,
        _ => return Err(ExportError::ChartRequestRequired),
    };
    let compiled = natural_cell::compile(&chart)
        .map_err(ExportError::OriginalCompilerRefused)?;
    if compiled.dimension != chart.source.dimension()
        || compiled.dimension > MAX_DIMENSION
        || compiled.rows.len() > MAX_ORIGINAL_ROWS
        || compiled.bank_names.len() != compiled.dimension
        || compiled.rows.iter().any(|row| row.coefficients.len() != compiled.dimension)
    {
        return Err(ExportError::CompilerShapeChanged);
    }
    Ok(CompiledCellRows {
        original_request: original_request.to_vec(),
        chart,
        compiled,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use parity_solver::q;

    // Byte-exact existing controls at4e556c4a/tests/chart.rs.
    const ORDINARY: &str = "RC1 CHART 3 2 2 0 0 2 4096\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nLEAF 0 1\nLEAF 1 2\nEXPOSURE 0 E:0 V:1 V:0 LE:1/1 LE:4/1\nEXPOSURE 1 E:1 V:2 V:0 LE:1/1 LE:4/1\n";
    const PARALLEL: &str = "RC1 CHART 5 5 2 1 0 0 4096\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nEDGE 2 2 3\nEDGE 3 2 3\nEDGE 4 3 4\nLEAF 0 1\nLEAF 1 4\nHYBRID 0 3 2 3\nCOIN 0 NONE NONE\n";

    #[test]
    fn original_exposure_rows_and_inverse_slots() {
        let exported = compile_request(ORDINARY.as_bytes()).unwrap();
        assert_eq!(exported.dimension(), 6);
        assert_eq!(exported.rows().len(), 13);
        assert_eq!(exported.original_bank_names().iter().map(String::as_str).collect::<Vec<_>>(),
            ["AGE:0", "AGE:1", "AGE:2", "RATE:0", "RATE:1", "RATE:A"]);
        // Independent literal expectations from the original chart control.
        assert_eq!(exported.rows()[9].coefficients,
            vec![q(-1, 1), q(1, 1), q(0, 1), q(1, 1), q(0, 1), q(0, 1)]);
        assert_eq!(exported.rows()[10].coefficients,
            vec![q(1, 1), q(-1, 1), q(0, 1), q(-4, 1), q(0, 1), q(0, 1)]);
        assert_eq!(exported.inverse_pair_rate_coordinate(Population::Edge(0)), Some(3));
        assert_eq!(exported.ancestral_inverse_pair_rate_coordinate(), 5);
        assert_eq!(exported.inverse_pair_rate_coordinate(Population::Ancestral), Some(5));
        assert_eq!(exported.age_coordinate(3), None);
        assert_eq!(exported.inverse_pair_rate_coordinate(Population::Edge(2)), None);
        assert_eq!(exported.coin_coordinate(0), None);
    }

    #[test]
    fn parallel_occurrences_and_dimension_above_affine_limit_are_preserved() {
        let exported = compile_request(PARALLEL.as_bytes()).unwrap();
        assert_eq!(exported.dimension(), 12);
        let edges = &exported.original_chart().source.edges;
        assert_eq!(edges[2], edges[3]);
        assert_eq!(exported.inverse_pair_rate_coordinate(Population::Edge(2)), Some(7));
        assert_eq!(exported.inverse_pair_rate_coordinate(Population::Edge(3)), Some(8));
        assert_eq!(exported.ancestral_inverse_pair_rate_coordinate(), 10);
        assert_eq!(exported.coin_coordinate(0), Some(11));
        assert_eq!(exported.coin_coordinate(1), None);
        assert!(exported.rows().iter().all(|r| r.coefficients.len() == 12));
    }

    #[test]
    fn zero_projection_cap_still_exports_without_solving() {
        let raw = ORDINARY.replace("4096", "0");
        let exported = compile_request(raw.as_bytes()).unwrap();
        assert_eq!(exported.projection_cap(), 0);
        assert_eq!(exported.rows().len(), 13);
        assert_eq!(exported.original_request(), raw.as_bytes());
    }

    #[test]
    fn snapshot_owns_the_original_input_after_caller_mutation() {
        let mut raw = ORDINARY.as_bytes().to_vec();
        let exported = compile_request(&raw).unwrap();
        raw[0] = b'X';
        assert_eq!(exported.original_request(), ORDINARY.as_bytes());
        assert_eq!(exported.dimension(), 6);
        assert_eq!(exported.rows().len(), 13);
    }

    #[test]
    fn unsupported_request_and_noncanonical_original_input_refuse() {
        assert!(matches!(
            compile_request(b"RC1 AFFINE 1 1 1\nLT 0/1 1/1\n"),
            Err(ExportError::ChartRequestRequired)));
        let malformed = ORDINARY.replace("LE:1/1", "LE:2/2");
        assert!(matches!(compile_request(malformed.as_bytes()),
            Err(ExportError::InvalidRequest(_))));
    }
}
