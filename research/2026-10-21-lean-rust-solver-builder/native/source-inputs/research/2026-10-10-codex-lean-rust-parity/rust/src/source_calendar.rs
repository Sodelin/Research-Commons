//! One strict supplied original calendar into the unchanged private word law.
//!
//! SourceCalendarCompiler supplies the agenda; accepted phase permutations
//! justify ascending original IDs at the endpoint PMF scope. One inverse-rate
//! bank serves every interval. Exponential substitutions remain symbolic.
//! This module adds no source-class admission or public protocol operation.
use crate::{q, Rational, source_population::Context, source_word as word};
use crate::source_population::Location;
use num_traits::{Signed, Zero};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompilerLimits { pub word_length: usize, pub slots: usize, pub variables: usize }
impl Default for CompilerLimits {
    fn default() -> Self { Self { word_length: 32, slots: 16, variables: 256 } }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub context: Context,
    pub ages: Vec<Rational>,
    /// Original edge inverse rates ascending, followed by the one ancestral rate.
    pub inverse_rates: Vec<Rational>,
    /// P(true/parent1), in the original hybrid registry order.
    pub original_gamma: Vec<Rational>,
    pub common: Vec<bool>,
    pub terminal: word::Terminal,
    pub compiler_limits: CompilerLimits,
    pub word_limits: word::Limits,
    pub provider_limits: word::ProviderLimits,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Requirements { pub word_length: usize, pub slots: usize, pub variables: usize }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompilerLimitKind { WordLength, Slots, Variables }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompilerLimit { pub kind: CompilerLimitKind, pub required: usize, pub cap: usize }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompilerUnknown { pub requirements: Requirements, pub limit: CompilerLimit }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cohort {
    pub date_index: usize,
    pub representative: usize,
    pub vertices: Vec<usize>,
    pub exits: Vec<usize>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase { Exit, Enter, Interval }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Origin { pub date_index: usize, pub phase: Phase, pub index: usize }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Slot {
    pub slot: usize,
    pub word_position: usize,
    pub younger_date: Rational,
    pub older_date: Rational,
    pub duration: Rational,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoordinateKind { ExpNeg, Rational }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PhysicalCoordinate {
    pub variable: word::Variable,
    pub kind: CoordinateKind,
    /// Positive exposure for ExpNeg; supplied parent1-gamma for Rational.
    pub argument: Rational,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Agenda {
    pub dates: Vec<Rational>,
    pub cohorts: Vec<Cohort>,
    pub word: Vec<word::Symbol>,
    pub origins: Vec<Origin>,
    pub slots: Vec<Slot>,
    pub physical_coordinates: Vec<PhysicalCoordinate>,
    /// Additional G6 natural-cell specialization; not a generic Calendar premise.
    pub leaf_age_zero: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Generated { pub requirements: Requirements, pub agenda: Agenda, pub child: word::Request }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileDecision { Generated(Generated), Unknown(CompilerUnknown) }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    Table { generated: Generated, table: word::Table },
    WordUnknown { generated: Generated, limit: word::Limit },
    CompilerUnknown(CompilerUnknown),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error { InvalidInput(&'static str), Unsupported(&'static str), Internal(&'static str) }

fn add(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_add(b).ok_or(Error::Internal("SOURCE_CALENDAR_COUNT_OVERFLOW"))
}
fn multiply(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_mul(b).ok_or(Error::Internal("SOURCE_CALENDAR_COUNT_OVERFLOW"))
}
fn canonical_rational(value: &Rational) -> bool {
    if !value.denom().is_positive() { return false; }
    let reduced = Rational::new(value.numer().clone(), value.denom().clone());
    reduced.numer() == value.numer() && reduced.denom() == value.denom()
}

fn validate(request: &Request) -> Result<(), Error> {
    request.context.validate().map_err(|_| Error::InvalidInput("SOURCE_CALENDAR_INPUT"))?;
    let source = &request.context.source;
    let populations = add(source.edges.len(), 1)?;
    if populations > 32 || request.context.global_labels.iter().any(|label| u64::try_from(*label).is_err()) {
        return Err(Error::InvalidInput("SOURCE_CALENDAR_INPUT"));
    }
    if request.ages.len() != source.vertices || request.inverse_rates.len() != populations
        || request.original_gamma.len() != source.hybrids.len() || request.common.len() != source.hybrids.len() {
        return Err(Error::InvalidInput("SOURCE_CALENDAR_DIMENSIONS"));
    }
    if request.ages.iter().chain(&request.inverse_rates).chain(&request.original_gamma)
        .any(|value| !canonical_rational(value)) {
        return Err(Error::InvalidInput("SOURCE_CALENDAR_INPUT"));
    }
    if source.edges.iter().any(|edge| request.ages[edge.target] >= request.ages[edge.source]) {
        return Err(Error::InvalidInput("SOURCE_CALENDAR_STRICT_EDGE"));
    }
    if request.inverse_rates.iter().any(|value| !value.is_positive()) {
        return Err(Error::InvalidInput("SOURCE_CALENDAR_INVERSE_RATE"));
    }
    if request.original_gamma.iter().any(|value| value <= &q(0, 1) || value >= &q(1, 1)) {
        return Err(Error::InvalidInput("SOURCE_CALENDAR_GAMMA"));
    }
    let caps = request.compiler_limits;
    let w = request.word_limits;
    let p = request.provider_limits;
    let counts = [caps.word_length, caps.slots, caps.variables, w.initial_assignments, w.initial_terms,
        w.queries, w.branches, w.term_products, w.destinations, w.terms, p.epoch.calls, p.epoch.destinations,
        p.epoch.lifted_terms, p.epoch.branches, p.epoch.term_products, p.boundary.assignments,
        p.boundary.destinations, p.boundary.term_contributions, p.completion.calls,
        p.completion.destinations, p.completion.lifted_terms];
    if caps.word_length > 32 || caps.slots > 16 || caps.variables > 256
        || counts.iter().any(|cap| u64::try_from(*cap).is_err()) {
        return Err(Error::InvalidInput("SOURCE_CALENDAR_LIMITS"));
    }
    if request.terminal == word::Terminal::AncestralComplete && request.context.sample.is_empty() {
        return Err(Error::InvalidInput("SOURCE_WORD_COMPLETION_EMPTY_COPY"));
    }
    Ok(())
}

/// Pure exact producer. Every input premise is checked before generated caps.
/// CompilerUnknown contains requirements only, with no child or partial agenda.
pub fn compile_calendar(request: &Request) -> Result<CompileDecision, Error> {
    validate(request)?;
    let source = &request.context.source;
    let dates = request.ages.iter().cloned().collect::<BTreeSet<_>>().into_iter().collect::<Vec<_>>();
    let slots = dates.len().checked_sub(1).ok_or(Error::Internal("SOURCE_CALENDAR_EMPTY_DATES"))?;
    let populations = add(source.edges.len(), 1)?;
    let requirements = Requirements {
        word_length: add(add(source.edges.len(), source.vertices)?, slots)?, slots,
        variables: add(multiply(slots, populations)?, source.hybrids.len())?,
    };
    for (kind, required, cap) in [
        (CompilerLimitKind::WordLength, requirements.word_length, request.compiler_limits.word_length),
        (CompilerLimitKind::Slots, requirements.slots, request.compiler_limits.slots),
        (CompilerLimitKind::Variables, requirements.variables, request.compiler_limits.variables),
    ] {
        if required > cap { return Ok(CompileDecision::Unknown(CompilerUnknown {
            requirements, limit: CompilerLimit { kind, required, cap },
        })); }
    }
    let mut agenda = Agenda { dates: dates.clone(), cohorts: Vec::with_capacity(dates.len()),
        word: Vec::with_capacity(requirements.word_length), origins: Vec::with_capacity(requirements.word_length),
        slots: Vec::with_capacity(slots), physical_coordinates: Vec::with_capacity(requirements.variables),
        leaf_age_zero: source.leaves.iter().all(|vertex| request.ages[*vertex].is_zero()) };
    for (date_index, age) in dates.iter().enumerate() {
        if date_index > 0 {
            let slot = date_index - 1;
            let duration = age - &dates[slot];
            if !duration.is_positive() { return Err(Error::Internal("SOURCE_CALENDAR_DURATION")); }
            agenda.slots.push(Slot { slot, word_position: agenda.word.len(),
                younger_date: dates[slot].clone(), older_date: age.clone(), duration });
            agenda.word.push(word::Symbol::Interval(slot));
            agenda.origins.push(Origin { date_index, phase: Phase::Interval, index: slot });
        }
        let vertices = (0..source.vertices).filter(|vertex| &request.ages[*vertex] == age).collect::<Vec<_>>();
        let exits = source.edges.iter().enumerate().filter(|(_, edge)| &request.ages[edge.source] == age)
            .map(|(edge, _)| edge).collect::<Vec<_>>();
        let representative = *vertices.first().ok_or(Error::Internal("SOURCE_CALENDAR_COHORT"))?;
        for edge in &exits {
            agenda.word.push(word::Symbol::Exit(*edge));
            agenda.origins.push(Origin { date_index, phase: Phase::Exit, index: *edge });
        }
        for vertex in &vertices {
            agenda.word.push(word::Symbol::Enter(*vertex));
            agenda.origins.push(Origin { date_index, phase: Phase::Enter, index: *vertex });
        }
        agenda.cohorts.push(Cohort { date_index, representative, vertices, exits });
    }
    for slot in &agenda.slots {
        for (index, inverse_rate) in request.inverse_rates.iter().enumerate() {
            let population = if index < source.edges.len() { Location::Edge(index) }
                else { Location::Ancestral(source.root) };
            agenda.physical_coordinates.push(PhysicalCoordinate {
                variable: word::Variable::Survival { slot: slot.slot, population }, kind: CoordinateKind::ExpNeg,
                argument: &slot.duration / inverse_rate,
            });
        }
    }
    for (hybrid, gamma) in request.original_gamma.iter().enumerate() {
        agenda.physical_coordinates.push(PhysicalCoordinate { variable: word::Variable::OriginalGamma(hybrid),
            kind: CoordinateKind::Rational, argument: gamma.clone() });
    }
    if agenda.word.len() != requirements.word_length || agenda.origins.len() != requirements.word_length
        || agenda.slots.len() != requirements.slots || agenda.physical_coordinates.len() != requirements.variables
        || agenda.dates.last() != Some(&request.ages[source.root]) {
        return Err(Error::Internal("SOURCE_CALENDAR_AGENDA"));
    }
    let child = word::Request { context: request.context.clone(), initial: word::Initial::Natural,
        common: request.common.clone(), slots, word: agenda.word.clone(), terminal: request.terminal,
        limits: request.word_limits, provider_limits: request.provider_limits };
    Ok(CompileDecision::Generated(Generated { requirements, agenda, child }))
}

/// Compose only after complete compilation; preserve exact child failure data.
pub fn calendar_row(request: &Request) -> Result<Decision, Error> {
    let generated = match compile_calendar(request)? {
        CompileDecision::Unknown(limit) => return Ok(Decision::CompilerUnknown(limit)),
        CompileDecision::Generated(generated) => generated,
    };
    match word::word_row(&generated.child).map_err(|error| match error {
        word::Error::InvalidInput(reason) => Error::InvalidInput(reason),
        word::Error::Unsupported(reason) => Error::Unsupported(reason),
        word::Error::Internal(reason) => Error::Internal(reason),
    })? {
        word::Decision::Table(table) => Ok(Decision::Table { generated, table }),
        word::Decision::Unknown(limit) => Ok(Decision::WordUnknown { generated, limit }),
    }
}
