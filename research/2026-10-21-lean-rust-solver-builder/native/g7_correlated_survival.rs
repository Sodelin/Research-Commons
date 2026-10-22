//! Correlated positive-power coordinates for one fixed rational calendar.
//! SOURCE ONLY: uncompiled/unexecuted. This is a source-family candidate,
//! not preservation of the calibrated CHART cell or a physical admission proof.
#![forbid(unsafe_code)]

use crate::{cell_calendar::CellCalendar, word_readout::Batch, Predicate, Relation};
use parity_solver::{polynomial::Polynomial, q, Rational,
    source_population::Location, source_word::Variable};

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub dimension: usize,
    pub atoms: usize,
    pub units: usize,
    pub exponent: usize,
    pub rational_bits: u64,
}
impl Default for Limits {
    fn default() -> Self {
        Self { dimension: 4096, atoms: 4096, units: 1_000_000,
            exponent: 1_000_000, rational_bits: 65_536 }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    Unknown { field: &'static str, required: Option<usize>, cap: usize },
    Internal(&'static str),
}
type Result<T> = std::result::Result<T, Error>;

/// Indices below exclude the frontend's unchanged algebraic-constant prefix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositivePower {
    pub slot: usize,
    pub population: Location,
    pub base_parameter: usize,
    pub slot_parameter: usize,
    /// z^denominator = x^numerator, both x and z strictly between0 and1.
    pub numerator: usize,
    pub denominator: usize,
}

/// Private ownership binds the exact calendar/word-variable order. The supplied
/// numeric rates/gamma are NOT the varying family's fitted rates/gamma. This
/// plan does not preserve the original CHART exposure/coin constraints.
#[derive(Debug)]
pub struct FixedCalendarFamilyPlan<'a> {
    calendar: &'a CellCalendar,
    constant_count: usize,
    parameter_count: usize,
    dimension: usize,
    word_variables: Vec<Variable>,
    word_to_parameter: Vec<usize>,
    relations: Vec<PositivePower>,
    domain: Predicate,
    limits: Limits,
}
impl<'a> FixedCalendarFamilyPlan<'a> {
    pub fn calendar(&self) -> &CellCalendar { self.calendar }
    pub fn constant_count(&self) -> usize { self.constant_count }
    pub fn parameter_count(&self) -> usize { self.parameter_count }
    pub fn dimension(&self) -> usize { self.dimension }
    pub fn word_to_parameter(&self) -> &[usize] { &self.word_to_parameter }
    pub fn relations(&self) -> &[PositivePower] { &self.relations }
    pub fn domain(&self) -> &Predicate { &self.domain }

    /// Reindex every coefficient into the SAME domain, keeping the constant
    /// prefix and every zero polynomial. No independent slot fit is allowed.
    pub fn lift_batch<'p>(&'p self, batch: &'p Batch<'a>)
        -> Result<LiftedReadout<'p, 'a>> {
        if !std::ptr::eq(batch.word().calendar(), self.calendar)
            || batch.word().table().variables() != self.word_variables.as_slice() {
            return Err(Error::Invalid("SURVIVAL_DIFFERENT_WORD_OR_CALENDAR"));
        }
        let mut units = bounded_add(0, batch.blocks().len(), "units", self.limits.units)?;
        let mut blocks = Vec::with_capacity(batch.blocks().len());
        for block in batch.blocks() {
            units = bounded_add(units, block.len(), "units", self.limits.units)?;
            let mut lifted = Vec::with_capacity(block.len());
            for polynomial in block {
                if polynomial.dimension != self.word_to_parameter.len() {
                    return Err(Error::Invalid("SURVIVAL_WORD_POLYNOMIAL_DIMENSION"));
                }
                let mut output = Polynomial::zero(self.dimension);
                for (powers, coefficient) in &polynomial.terms {
                    if powers.len() != polynomial.dimension {
                        return Err(Error::Invalid("SURVIVAL_WORD_EXPONENT_ARITY"));
                    }
                    units = bounded_add(units, self.dimension, "units", self.limits.units)?;
                    rational(coefficient, self.limits)?;
                    let bits = coefficient.numer().bits().max(coefficient.denom().bits());
                    let integer_bytes = usize::try_from(bits).map_err(|_|
                        unknown("units", None, self.limits.units))? / 4 + 2;
                    units = bounded_add(units, integer_bytes, "units", self.limits.units)?;
                    if coefficient == &q(0,1) {
                        return Err(Error::Invalid("SURVIVAL_WORD_ZERO_TERM"));
                    }
                    let mut target = vec![0usize; self.dimension];
                    for (i, exponent) in powers.iter().copied().enumerate() {
                        if exponent > self.limits.exponent {
                            return Err(unknown("exponent", Some(exponent), self.limits.exponent));
                        }
                        let j = self.constant_count + self.word_to_parameter[i];
                        target[j] = exponent;
                    }
                    if output.terms.insert(target, coefficient.clone()).is_some() {
                        return Err(Error::Internal("SURVIVAL_NONINJECTIVE_VARIABLE_MAP"));
                    }
                }
                lifted.push(output);
            }
            blocks.push(lifted);
        }
        Ok(LiftedReadout { plan: self, original: batch, blocks })
    }
}
/// Retains the exact forcing mask, full word, menu maps and calendar through
/// the original Batch. It is not a SourceModel or a source-coverage certificate.
#[derive(Debug)]
pub struct LiftedReadout<'p, 'a> {
    plan: &'p FixedCalendarFamilyPlan<'a>,
    original: &'p Batch<'a>,
    blocks: Vec<Vec<Polynomial>>,
}
impl<'p, 'a> LiftedReadout<'p, 'a> {
    pub fn plan(&self) -> &FixedCalendarFamilyPlan<'a> { self.plan }
    pub fn original(&self) -> &Batch<'a> { self.original }
    pub fn blocks(&self) -> &[Vec<Polynomial>] { &self.blocks }
}

fn unknown(field: &'static str, required: Option<usize>, cap: usize) -> Error {
    Error::Unknown { field, required, cap }
}
fn bounded_add(a: usize, b: usize, field: &'static str, cap: usize) -> Result<usize> {
    let value = a.checked_add(b).ok_or_else(|| unknown(field, None, cap))?;
    if value > cap { return Err(unknown(field, Some(value), cap)); }
    Ok(value)
}
fn bounded_mul(a: usize, b: usize, field: &'static str, cap: usize) -> Result<usize> {
    let value = a.checked_mul(b).ok_or_else(|| unknown(field, None, cap))?;
    if value > cap { return Err(unknown(field, Some(value), cap)); }
    Ok(value)
}
fn rational(value: &Rational, limits: Limits) -> Result<()> {
    if value.denom() <= q(0,1).numer() {
        return Err(Error::Invalid("SURVIVAL_RATIONAL_DENOMINATOR"));
    }
    let bits = value.numer().bits().max(value.denom().bits());
    if bits > limits.rational_bits {
        return Err(unknown("rational_bits", usize::try_from(bits).ok(),
            usize::try_from(limits.rational_bits).unwrap_or(usize::MAX)));
    }
    let normalized = Rational::new(value.numer().clone(), value.denom().clone());
    if normalized.numer() != value.numer() || normalized.denom() != value.denom() {
        return Err(Error::Invalid("SURVIVAL_NONCANONICAL_RATIONAL"));
    }
    Ok(())
}
fn positive_exponents(value: &Rational, limits: Limits) -> Result<(usize, usize)> {
    rational(value, limits)?;
    if value <= &q(0,1) { return Err(Error::Invalid("SURVIVAL_NONPOSITIVE_POWER")); }
    // Bounded exact decimal integer conversion, never a float or rational fit.
    let n = value.numer().to_string().parse::<usize>()
        .map_err(|_| unknown("exponent", None, limits.exponent))?;
    let d = value.denom().to_string().parse::<usize>()
        .map_err(|_| unknown("exponent", None, limits.exponent))?;
    if n > limits.exponent || d > limits.exponent {
        return Err(unknown("exponent", Some(n.max(d)), limits.exponent));
    }
    Ok((n,d))
}

/// Builds ONLY the explicit fixed-calendar coordinate domain. The whole-edge
/// bank X, ancestral unit-survival XA and natural parent1 gamma precede all Z.
/// Exact positive powers tie EVERY slot to that ONE bank. Rate realization,
/// target pieces and both physical source/action coverage directions need
/// their actual original mathematical receivers.
pub fn fixed_calendar_family<'a>(calendar: &'a CellCalendar, constant_count: usize,
    limits: Limits) -> Result<FixedCalendarFamilyPlan<'a>> {
    let request = calendar.calendar_request();
    let generated = calendar.generated();
    let source = &request.context.source;
    let edges = source.edges.len();
    let populations = bounded_add(edges, 1, "dimension", limits.dimension)?;
    let hybrids = source.hybrids.len();
    let base = bounded_add(populations, hybrids, "dimension", limits.dimension)?;
    let slots = generated.agenda.slots.len();
    let slot_parameters = bounded_mul(slots, populations, "dimension", limits.dimension)?;
    let parameter_count = bounded_add(base, slot_parameters, "dimension", limits.dimension)?;
    let dimension = bounded_add(constant_count, parameter_count, "dimension", limits.dimension)?;
    let word_count = bounded_add(slot_parameters, hybrids, "dimension", limits.dimension)?;
    let atom_count = bounded_add(bounded_mul(parameter_count, 2, "atoms", limits.atoms)?,
        slot_parameters, "atoms", limits.atoms)?;
    // At most two terms per interval/power atom; charge before allocations.
    let _units = bounded_mul(bounded_mul(atom_count, 2, "units", limits.units)?,
        dimension, "units", limits.units)?;
    if request.ages.len() != source.vertices || request.common.len() != hybrids
        || generated.child.slots != slots || generated.requirements.variables != word_count
        || generated.agenda.physical_coordinates.len() != word_count {
        return Err(Error::Internal("SURVIVAL_CALENDAR_DIMENSION"));
    }
    let mut edge_durations = Vec::with_capacity(edges);
    for edge in &source.edges {
        let old = request.ages.get(edge.source).ok_or(Error::Internal("SURVIVAL_EDGE_SOURCE"))?;
        let young = request.ages.get(edge.target).ok_or(Error::Internal("SURVIVAL_EDGE_TARGET"))?;
        rational(old, limits)?;
        rational(young, limits)?;
        let duration = old - young;
        rational(&duration, limits)?;
        if duration <= q(0,1) { return Err(Error::Internal("SURVIVAL_EDGE_DURATION")); }
        edge_durations.push(duration);
    }
    let mut word_variables = Vec::with_capacity(word_count);
    let mut word_to_parameter = Vec::with_capacity(word_count);
    let mut relations = Vec::with_capacity(slot_parameters);
    for (j, slot) in generated.agenda.slots.iter().enumerate() {
        rational(&slot.duration, limits)?;
        if slot.slot != j || slot.duration <= q(0,1)
            || slot.duration != &slot.older_date - &slot.younger_date {
            return Err(Error::Internal("SURVIVAL_SLOT_DURATION"));
        }
        for p in 0..populations {
            let exponent = if p < edges { &slot.duration / &edge_durations[p] }
                else { slot.duration.clone() };
            let (numerator, denominator) = positive_exponents(&exponent, limits)?;
            let population = if p < edges { Location::Edge(p) }
                else { Location::Ancestral(source.root) };
            let slot_parameter = base + j * populations + p;
            word_variables.push(Variable::Survival { slot: j, population });
            word_to_parameter.push(slot_parameter);
            relations.push(PositivePower { slot: j, population, base_parameter: p,
                slot_parameter, numerator, denominator });
        }
    }
    for h in 0..hybrids {
        word_variables.push(Variable::OriginalGamma(h));
        word_to_parameter.push(populations + h);
    }
    if generated.agenda.physical_coordinates.iter().map(|c| &c.variable)
        .ne(word_variables.iter()) {
        return Err(Error::Internal("SURVIVAL_ORIGINAL_VARIABLE_ORDER"));
    }
    let mut atoms = Vec::with_capacity(atom_count);
    for i in 0..parameter_count {
        let x = Polynomial::variable(dimension, constant_count + i)
            .map_err(Error::Internal)?;
        atoms.push(Predicate::Atom(Relation::Positive, x.clone()));
        let one_minus = Polynomial::one(dimension).subtract(&x).map_err(Error::Internal)?;
        atoms.push(Predicate::Atom(Relation::Positive, one_minus));
    }
    for relation in &relations {
        let z = Polynomial::monomial(dimension, constant_count + relation.slot_parameter,
            relation.denominator, q(1,1)).map_err(Error::Internal)?;
        let x = Polynomial::monomial(dimension, constant_count + relation.base_parameter,
            relation.numerator, q(1,1)).map_err(Error::Internal)?;
        atoms.push(Predicate::Atom(Relation::Equal, z.subtract(&x).map_err(Error::Internal)?));
    }
    Ok(FixedCalendarFamilyPlan { calendar, constant_count, parameter_count, dimension,
        word_variables, word_to_parameter, relations, domain: Predicate::And(atoms), limits })
}
