//! A supplied checked CHART vector into the existing calendar/word providers.
//! SOURCE ONLY: uncompiled/unexecuted. No search, parser replacement or dispatch.
//! Exact request/rows/vector remain owned together; no physical-origin or native
//! refinement claim is created by these private Rust fields.
#![forbid(unsafe_code)]

use crate::{cell_rows::CompiledCellRows, controlled_word};
use parity_solver::{affine, natural_cell::Population, q, Rational,
    source_calendar as calendar, source_population::Context, source_word as word};

#[derive(Clone, Debug)]
pub struct Request {
    pub cell: CompiledCellRows,
    pub witness: Vec<Rational>,
    /// Local Copy positions -> original declared taxon indices.
    pub sample: Vec<usize>,
    /// Injective global identities for those same local Copy positions.
    pub global_labels: Vec<usize>,
    /// Original hybrid registry order; true means COMMON.
    pub common: Vec<bool>,
    pub terminal: word::Terminal,
    pub compiler_limits: calendar::CompilerLimits,
    pub word_limits: word::Limits,
    pub provider_limits: word::ProviderLimits,
}
#[derive(Clone, Copy, Debug)]
pub struct Limits { pub rational_bits: u64 }
impl Default for Limits {
    fn default() -> Self { Self { rational_bits: 65_536 } }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    /// Construction unavailable, never mathematical source/cell NO.
    Unknown { field: &'static str, required: Option<usize>, cap: usize },
    OriginalWitnessRejected,
    OriginalCalendar(calendar::Error),
    OriginalCalendarLimit(calendar::CompilerUnknown),
    ControlledWord(controlled_word::Error),
    Internal(&'static str),
}
type Result<T> = std::result::Result<T, Error>;

/// Owning, read-only association of the exact original request, emitted rows,
/// supplied vector, extracted one-bank calendar request and generated agenda.
#[derive(Debug)]
pub struct CellCalendar {
    original: Request,
    calendar_request: calendar::Request,
    generated: calendar::Generated,
}
#[derive(Debug)]
pub struct WordTable<'a> {
    calendar: &'a CellCalendar,
    table: controlled_word::Table<'a>,
}
impl<'a> WordTable<'a> {
    pub fn calendar(&self) -> &CellCalendar { self.calendar }
    pub fn table(&self) -> &controlled_word::Table<'a> { &self.table }
}
impl CellCalendar {
    pub fn original(&self) -> &Request { &self.original }
    pub fn calendar_request(&self) -> &calendar::Request { &self.calendar_request }
    pub fn generated(&self) -> &calendar::Generated { &self.generated }

    /// Reuses the SAME immutable source/calendar/bank. A mask changes only the
    /// programme. Caller supplies no replacement word, rates or gamma vector.
    pub fn controlled<'a>(&'a self, mask: &'a [Option<bool>],
        limits: controlled_word::Limits) -> Result<WordTable<'a>> {
        let table = controlled_word::controlled_word(&self.generated.child, mask, limits)
            .map_err(Error::ControlledWord)?;
        Ok(WordTable { calendar: self, table })
    }
}
fn unknown(field: &'static str, required: Option<usize>, cap: usize) -> Error {
    Error::Unknown { field, required, cap }
}
fn rational(value: &Rational, cap: u64) -> Result<()> {
    if value.denom() <= q(0, 1).numer() {
        return Err(Error::Invalid("CELL_CALENDAR_RATIONAL_DENOMINATOR"));
    }
    let bits = value.numer().bits().max(value.denom().bits());
    if bits > cap {
        return Err(unknown("rational_bits", usize::try_from(bits).ok(),
            usize::try_from(cap).unwrap_or(usize::MAX)));
    }
    let reduced = Rational::new(value.numer().clone(), value.denom().clone());
    if reduced.numer() != value.numer() || reduced.denom() != value.denom() {
        return Err(Error::Invalid("CELL_CALENDAR_NONCANONICAL_RATIONAL"));
    }
    Ok(())
}
fn coordinate(cell: &CompiledCellRows, position: Option<usize>,
    used: &mut [bool], witness: &[Rational]) -> Result<Rational> {
    let position = position.ok_or(Error::Internal("CELL_CALENDAR_MISSING_COORDINATE"))?;
    if position >= used.len() || position >= cell.dimension() || used[position] {
        return Err(Error::Internal("CELL_CALENDAR_COORDINATE_LAYOUT"));
    }
    let value = witness.get(position).ok_or(Error::Internal("CELL_CALENDAR_SHORT_VECTOR"))?;
    used[position] = true;
    Ok(value.clone())
}

/// Native original-row verification, not a solver or a Lean proof. No generated
/// agenda or partial CellCalendar is returned on any validation/budget failure.
pub fn prepare(original: Request, limits: Limits) -> Result<CellCalendar> {
    let cell = &original.cell;
    let source = &cell.original_chart().source;
    if original.witness.len() != cell.dimension() {
        return Err(Error::Invalid("CELL_CALENDAR_WITNESS_DIMENSION"));
    }
    if original.sample.len() > 4 {
        return Err(unknown("inherited_sampled_copies", Some(original.sample.len()), 4));
    }
    if limits.rational_bits > 65_536 {
        return Err(unknown("binding_rational_bit_profile", usize::try_from(limits.rational_bits).ok(), 65_536));
    }
    if original.common.len() != source.hybrids.len() {
        return Err(Error::Invalid("CELL_CALENDAR_MODE_REGISTRY"));
    }
    if original.global_labels.len() != original.sample.len()
        || original.sample.iter().any(|taxon| *taxon >= source.leaves.len()) {
        return Err(Error::Invalid("CELL_CALENDAR_SAMPLE_EMBEDDING"));
    }
    let context = Context { source: source.clone(), sample: original.sample.clone(),
        global_labels: original.global_labels.clone() };
    context.validate().map_err(Error::Invalid)?;
    for value in &original.witness { rational(value, limits.rational_bits)?; }
    for row in cell.rows() {
        rational(&row.bound, limits.rational_bits)?;
        for coefficient in &row.coefficients { rational(coefficient, limits.rational_bits)?; }
    }
    if !affine::check_witness(cell.dimension(), cell.rows(), &original.witness) {
        return Err(Error::OriginalWitnessRejected);
    }
    let mut used = vec![false; cell.dimension()];
    let ages = (0..source.vertices).map(|v|
        coordinate(cell, cell.age_coordinate(v), &mut used, &original.witness))
        .collect::<Result<Vec<_>>>()?;
    let mut inverse_rates = (0..source.edges.len()).map(|edge|
        coordinate(cell, cell.inverse_pair_rate_coordinate(Population::Edge(edge)),
            &mut used, &original.witness)).collect::<Result<Vec<_>>>()?;
    inverse_rates.push(coordinate(cell,
        Some(cell.ancestral_inverse_pair_rate_coordinate()), &mut used, &original.witness)?);
    // The typed Code/CHART receiver interprets these coins as ORIGINAL parent1
    // probabilities, under incoming[0]=parent(false), incoming[1]=parent(true).
    // This is not old LAW-v1 G=P(parent0), and no complement is applied here.
    let original_gamma = (0..source.hybrids.len()).map(|h|
        coordinate(cell, cell.coin_coordinate(h), &mut used, &original.witness))
        .collect::<Result<Vec<_>>>()?;
    if used.iter().any(|position| !*position) {
        return Err(Error::Internal("CELL_CALENDAR_BANK_NOT_BIJECTIVE"));
    }
    let calendar_request = calendar::Request { context, ages, inverse_rates,
        original_gamma, common: original.common.clone(), terminal: original.terminal,
        compiler_limits: original.compiler_limits, word_limits: original.word_limits,
        provider_limits: original.provider_limits };
    let generated = match calendar::compile_calendar(&calendar_request)
        .map_err(Error::OriginalCalendar)? {
        calendar::CompileDecision::Generated(generated) => generated,
        calendar::CompileDecision::Unknown(limit) => return Err(Error::OriginalCalendarLimit(limit)),
    };
    // ExpNeg arguments are exact duration/u metadata. This function evaluates
    // no logarithm/exponential, rounds no coordinate and frees no slot variable.
    Ok(CellCalendar { original, calendar_request, generated })
}
