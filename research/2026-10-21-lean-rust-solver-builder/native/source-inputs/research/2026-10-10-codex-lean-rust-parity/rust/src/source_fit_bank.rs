//! Supplied rational source-fit assignments transported to one physical bank.
//!
//! This is a representation consumer, not an observation-law compiler. Exact
//! satisfaction of the supplied sparse trace does not establish that the trace
//! was generated from the supplied source or that all observations were used.
//! Original occurrence IDs and the old parent-zero gamma convention are bound
//! explicitly. Logarithmic rates and fractional powers are never rounded or
//! inserted into the existing rational-inverse-rate Calendar request.
use crate::{canonical, natural_cell::Source, polynomial::Polynomial, q,
    source_calendar as calendar, source_population::{Context, Location},
    source_word as word, Rational};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::{BTreeSet, VecDeque};

pub const MAX_REQUEST_BYTES: usize = 65_536;
pub const MAX_RESULT_BYTES: usize = 4 * 1024 * 1024;

/// Preserves the inherited codec's ascending coefficients and one-based real
/// root index. Algebraic descriptors are syntactically checked, not evaluated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactValue {
    Rational(Rational),
    Algebraic { polynomial_ascending: Vec<Rational>, real_root_index: usize },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mechanism { Common, Independent }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub equations: usize,
    pub terms: usize,
    pub arithmetic_steps: usize,
    pub rational_bits: usize,
    pub power_exponent: usize,
}
impl Default for Limits {
    fn default() -> Self { Self { equations: 4096, terms: 65_536,
        arithmetic_steps: 1_000_000, rational_bits: 4096, power_exponent: 4096 } }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    /// One selected panel on the same original source. This does not bind the
    /// sampled panels or randomization programs that generated the trace.
    pub context: Context,
    /// Bijection from native vertex IDs to inherited graph vertex names.
    pub vertex_names: Vec<String>,
    /// Declared original taxon IDs in source.leaves order, which need not be
    /// the inherited engine's L0,L1,... names.
    pub taxon_labels: Vec<String>,
    /// Declared original hybrid labels in the native hybrid bank order.
    pub hybrid_labels: Vec<String>,
    /// Original sampled alphabet in the local Copy order; global_labels
    /// retains the native embedding independently of this string alphabet.
    pub copy_labels: Vec<String>,
    /// Exactly x0..x(E-1), then g_<hybrid-name> in inherited sorted-name order.
    pub variables: Vec<String>,
    pub values: Vec<ExactValue>,
    /// Canonical sparse rows in that same bank. Every row is checked with one
    /// assignment; no row-specific or configuration-specific fit is allowed.
    pub equations: Vec<Polynomial>,
    /// The recovered fitter has one global mechanism, not mixed site modes.
    pub mechanism: Mechanism,
    pub terminal: word::Terminal,
    pub compiler_limits: calendar::CompilerLimits,
    pub limits: Limits,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limit {
    pub stage: &'static str,
    pub kind: &'static str,
    /// Canonical natural decimal; exponent counts may exceed machine usize.
    pub required: String,
    pub cap: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidInput(&'static str), Internal(&'static str),
    /// A serializer stopped before appending a token. This is a lower bound
    /// on the full frame size, not a claim to have generated that full frame.
    FrameLimit { required_at_least: usize, cap: usize },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision {
    SymbolicBank(Bank),
    Unknown(Limit),
    /// The complete original descriptor remains in the bound Request.
    Unsupported { first_algebraic_variable: usize, reason: &'static str },
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Work { pub supplied_equations: usize, pub supplied_terms: usize, pub arithmetic_steps: usize }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EdgeBank {
    pub original_edge: usize,
    pub source: usize,
    pub target: usize,
    pub duration: Rational,
    pub survival: Rational,
    /// References the same fitted atom for every active piece of this edge.
    pub active_slots: Vec<usize>,
    pub active_exponent_sum: Rational,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridBank {
    pub original_hybrid: usize,
    pub vertex: usize,
    pub incoming: [usize; 2],
    pub old_parent_zero_probability: Rational,
    pub original_parent_one_probability: Rational,
}
/// Primitive integer polynomial leading*X^degree + constant, and 0<X<1.
/// It selects the unique positive root but does not evaluate that root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositiveRootConstraint {
    pub degree: usize,
    pub leading: BigInt,
    pub constant: BigInt,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expression {
    /// x_e^(numerator/denominator), with x_e shared across all cuts.
    EdgePower {
        original_edge: usize,
        exponent: Rational,
        active: bool,
        /// Only active coordinates emit a positive-root equation.
        constraint: Option<PositiveRootConstraint>,
        /// Integer exponents only. A fractional result remains unevaluated,
        /// even when a particular atom happens to have a rational root.
        rational_value: Option<Rational>,
    },
    /// Ancestral inverse rate is exactly one. Finite agenda ancestral slots
    /// are unused; exp(-duration) is not treated as a rational number.
    AncestralExpNeg { duration: Rational, active: bool },
    OriginalGamma(Rational),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Coordinate { pub variable: word::Variable, pub expression: Expression }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Agenda {
    pub dates: Vec<Rational>,
    pub cohorts: Vec<calendar::Cohort>,
    pub origins: Vec<calendar::Origin>,
    pub slots: Vec<calendar::Slot>,
    pub leaf_age_zero: bool,
}
/// Fields are private so a successful consumer cannot fabricate a checked
/// bank. Accessors expose the source/trace and the unchanged symbolic word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bank {
    request: Request,
    ages: Vec<Rational>,
    edges: Vec<EdgeBank>,
    hybrids: Vec<HybridBank>,
    agenda: Agenda,
    coordinates: Vec<Coordinate>,
    symbolic_word: word::Request,
    evaluations: Vec<Rational>,
    work: Work,
}
impl Bank {
    pub fn request(&self) -> &Request { &self.request }
    pub fn ages(&self) -> &[Rational] { &self.ages }
    pub fn edges(&self) -> &[EdgeBank] { &self.edges }
    pub fn hybrids(&self) -> &[HybridBank] { &self.hybrids }
    pub fn agenda(&self) -> &Agenda { &self.agenda }
    pub fn coordinates(&self) -> &[Coordinate] { &self.coordinates }
    pub fn symbolic_word(&self) -> &word::Request { &self.symbolic_word }
    pub fn evaluations(&self) -> &[Rational] { &self.evaluations }
    pub fn work(&self) -> &Work { &self.work }
    /// Forcing addresses the unchanged original incoming occurrence bit. The
    /// probability complement is never applied to the forced bit itself.
    pub fn forced_parent(&self, original_hybrid: usize, bit: usize) -> Result<usize, Error> {
        let hybrid = self.hybrids.get(original_hybrid).ok_or(Error::InvalidInput("SOURCE_FIT_HYBRID_REFERENCE"))?;
        hybrid.incoming.get(bit).copied().ok_or(Error::InvalidInput("SOURCE_FIT_FORCED_BIT"))
    }
    /// There is no rational rounding escape hatch. This bank supplies exact
    /// logarithmic definitions, not Rational inverse-rate values.
    pub fn rational_calendar_request(&self) -> Result<calendar::Request, &'static str> {
        Err("SOURCE_FIT_LOG_INVERSE_RATE_UNREPRESENTED_IN_RATIONAL_DTO")
    }
}

enum Failure { Unknown(Limit), Error(Error) }
impl From<Error> for Failure { fn from(error: Error) -> Self { Self::Error(error) } }
fn invalid(code: &'static str) -> Error { Error::InvalidInput(code) }
fn internal(code: &'static str) -> Error { Error::Internal(code) }
fn check(stage: &'static str, kind: &'static str, required: usize, cap: usize) -> Result<(), Failure> {
    if required > cap { Err(Failure::Unknown(Limit { stage, kind, required: required.to_string(), cap })) }
    else { Ok(()) }
}
fn bits(value: &Rational) -> usize { value.numer().bits().max(value.denom().bits()) as usize }
fn canonical_rational(value: &Rational) -> bool {
    value.denom().is_positive() && value.numer().gcd(value.denom()) == BigInt::one()
}
fn interior(value: &Rational) -> bool {
    // Same positive denominator: no cross-products needed for the domain gate.
    value.numer().is_positive() && value.numer() < value.denom()
}
fn bounded_rational(value: &Rational) -> Result<(), Error> {
    if bits(value) > 65_536 { return Err(invalid("SOURCE_FIT_HARD_RATIONAL_BITS")); }
    if !canonical_rational(value) { return Err(invalid("SOURCE_FIT_NONCANONICAL_RATIONAL")); }
    Ok(())
}
fn labels(values: &[String], expected: usize) -> bool {
    values.len() == expected
        && !values.iter().any(|name| name.is_empty() || name.len() > 128 || name.contains('\0'))
        && values.iter().collect::<BTreeSet<_>>().len() == expected
}
fn validate(request: &Request) -> Result<(usize, usize), Error> {
    request.context.validate().map_err(|_| invalid("SOURCE_FIT_CONTEXT"))?;
    let source = &request.context.source;
    if source.edges.len() + 1 > 32 { return Err(invalid("SOURCE_FIT_POPULATION_BANK")); }
    let dimension = source.edges.len() + source.hybrids.len();
    if !labels(&request.vertex_names, source.vertices)
        || !labels(&request.taxon_labels, source.leaves.len())
        || !labels(&request.hybrid_labels, source.hybrids.len())
        || !labels(&request.copy_labels, request.context.sample.len()) {
        return Err(invalid("SOURCE_FIT_VERTEX_BIJECTION"));
    }
    // The inherited Network enumerates incoming original occurrences in input
    // order and sorts hybrid names. Silently sorting native parents would flip
    // stored bits and would change parallel-edge identity.
    if source.hybrids.iter().any(|h| h.incoming[0] >= h.incoming[1])
        || source.hybrids.windows(2).any(|h|
            request.vertex_names[h[0].vertex] >= request.vertex_names[h[1].vertex]) {
        return Err(invalid("SOURCE_FIT_INHERITED_PARENT_ORDER"));
    }
    let expected = (0..source.edges.len()).map(|i| format!("x{i}"))
        .chain(source.hybrids.iter().map(|h| format!("g_{}", request.vertex_names[h.vertex])))
        .collect::<Vec<_>>();
    if request.variables != expected || request.values.len() != dimension {
        return Err(invalid("SOURCE_FIT_VARIABLE_BANK"));
    }
    let limits = request.limits;
    if limits.equations > 4096 || limits.terms > 65_536 || limits.arithmetic_steps > 1_000_000
        || limits.rational_bits > 65_536 || limits.power_exponent > 4096
        || request.compiler_limits.word_length > 32 || request.compiler_limits.slots > 16
        || request.compiler_limits.variables > 256 {
        return Err(invalid("SOURCE_FIT_LIMITS"));
    }
    if request.terminal == word::Terminal::AncestralComplete && request.context.sample.is_empty() {
        return Err(invalid("SOURCE_WORD_COMPLETION_EMPTY_COPY"));
    }
    for value in &request.values { match value {
        ExactValue::Rational(value) => {
            bounded_rational(value)?;
            if !interior(value) { return Err(invalid("SOURCE_FIT_STRICT_INTERIOR")); }
        }
        ExactValue::Algebraic { polynomial_ascending, real_root_index } => {
            if polynomial_ascending.len() < 2 || polynomial_ascending.len() > 65
                || *real_root_index == 0 || *real_root_index >= polynomial_ascending.len()
                || polynomial_ascending.last().is_some_and(Rational::is_zero) {
                return Err(invalid("SOURCE_FIT_ALGEBRAIC_DESCRIPTOR"));
            }
            for coefficient in polynomial_ascending { bounded_rational(coefficient)?; }
        }
    } }
    if request.equations.is_empty() || request.equations.len() > 4096 {
        return Err(invalid("SOURCE_FIT_TRACE_SIZE"));
    }
    let mut terms = 0usize;
    let mut maximum_power = 0usize;
    for polynomial in &request.equations {
        if polynomial.dimension != dimension { return Err(invalid("SOURCE_FIT_TRACE_BANK")); }
        terms = terms.checked_add(polynomial.terms.len()).ok_or(invalid("SOURCE_FIT_TRACE_SIZE"))?;
        if terms > 65_536 { return Err(invalid("SOURCE_FIT_TRACE_SIZE")); }
        for (powers, coefficient) in &polynomial.terms {
            if powers.len() != dimension || powers.iter().any(|power| *power > 4096)
                || coefficient.is_zero() { return Err(invalid("SOURCE_FIT_TRACE_CANONICAL")); }
            bounded_rational(coefficient)?;
            maximum_power = maximum_power.max(powers.iter().copied().max().unwrap_or(0));
        }
    }
    Ok((terms, maximum_power))
}

/// Every operand/result is bit-checked. Rational multiplication/division uses
/// bounded cross-products; addition has at most 2B+1 numerator bits before
/// normalization. Exponentiation never skips intermediate bit checks.
struct Arithmetic { limits: Limits, steps: usize }
impl Arithmetic {
    fn check(&self, stage: &'static str, value: &Rational) -> Result<(), Failure> {
        check(stage, "rational_bits", bits(value), self.limits.rational_bits)
    }
    fn step(&mut self, stage: &'static str) -> Result<(), Failure> {
        let next = self.steps.checked_add(1).ok_or(internal("SOURCE_FIT_COUNT_OVERFLOW"))?;
        check(stage, "arithmetic_steps", next, self.limits.arithmetic_steps)?;
        self.steps = next;
        Ok(())
    }
    fn add(&mut self, stage: &'static str, a: &Rational, b: &Rational) -> Result<Rational, Failure> {
        self.check(stage, a)?; self.check(stage, b)?; self.step(stage)?;
        let result = a + b; self.check(stage, &result)?; Ok(result)
    }
    fn multiply(&mut self, stage: &'static str, a: &Rational, b: &Rational) -> Result<Rational, Failure> {
        self.check(stage, a)?; self.check(stage, b)?; self.step(stage)?;
        let result = a * b; self.check(stage, &result)?; Ok(result)
    }
    fn divide(&mut self, stage: &'static str, a: &Rational, b: &Rational) -> Result<Rational, Failure> {
        self.check(stage, a)?; self.check(stage, b)?;
        if b.is_zero() { return Err(internal("SOURCE_FIT_ZERO_DIVISOR").into()); }
        self.step(stage)?;
        let result = a / b; self.check(stage, &result)?; Ok(result)
    }
    fn power(&mut self, stage: &'static str, base: &Rational, exponent: usize) -> Result<Rational, Failure> {
        check(stage, "power_exponent", exponent, self.limits.power_exponent)?;
        self.check(stage, base)?;
        let mut result = q(1, 1);
        self.check(stage, &result)?;
        let mut factor = base.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining & 1 == 1 { result = self.multiply(stage, &result, &factor)?; }
            remaining >>= 1;
            if remaining > 0 { factor = self.multiply(stage, &factor, &factor)?; }
        }
        Ok(result)
    }
}

/// Exact old physical_realization height construction: leaves zero, every
/// other vertex 1+max(child heights), original occurrences left in place.
fn heights(source: &Source) -> Result<Vec<Rational>, Error> {
    let mut indegree = vec![0usize; source.vertices];
    for edge in &source.edges { indegree[edge.target] += 1; }
    let mut ready = VecDeque::from([source.root]);
    let mut order = Vec::with_capacity(source.vertices);
    while let Some(vertex) = ready.pop_front() {
        order.push(vertex);
        for edge in &source.edges { if edge.source == vertex {
            indegree[edge.target] -= 1;
            if indegree[edge.target] == 0 { ready.push_back(edge.target); }
        } }
    }
    if order.len() != source.vertices { return Err(internal("SOURCE_FIT_TOPOLOGICAL_ORDER")); }
    let mut ages = vec![q(0, 1); source.vertices];
    for vertex in order.into_iter().rev() {
        if source.leaves.contains(&vertex) { continue; }
        let maximum = source.edges.iter().filter(|edge| edge.source == vertex)
            .map(|edge| ages[edge.target].clone()).max().ok_or(internal("SOURCE_FIT_HEIGHT_CHILD"))?;
        ages[vertex] = maximum + q(1, 1);
    }
    Ok(ages)
}
fn exponent_count(value: &BigInt, arithmetic: &Arithmetic) -> Result<usize, Failure> {
    if value > &BigInt::from(arithmetic.limits.power_exponent) {
        return Err(Failure::Unknown(Limit { stage: "COORDINATES", kind: "power_exponent",
            required: value.to_string(), cap: arithmetic.limits.power_exponent }));
    }
    value.to_usize().ok_or_else(|| internal("SOURCE_FIT_POWER_CONVERSION").into())
}
fn edge_expression(edge: &EdgeBank, exponent: Rational, active: bool,
    arithmetic: &mut Arithmetic) -> Result<Expression, Failure> {
    arithmetic.check("COORDINATES", &exponent)?;
    if !exponent.is_positive() { return Err(internal("SOURCE_FIT_SLOT_DOMAIN").into()); }
    if !active { return Ok(Expression::EdgePower { original_edge: edge.original_edge,
        exponent, active, constraint: None, rational_value: None }); }
    let numerator = exponent_count(exponent.numer(), arithmetic)?;
    let denominator = exponent_count(exponent.denom(), arithmetic)?;
    let power = arithmetic.power("COORDINATES", &edge.survival, numerator)?;
    let constraint = PositiveRootConstraint { degree: denominator,
        leading: power.denom().clone(), constant: -power.numer().clone() };
    Ok(Expression::EdgePower { original_edge: edge.original_edge, exponent, active,
        constraint: Some(constraint), rational_value: if denominator == 1 { Some(power) } else { None } })
}

fn run(request: &Request, supplied_terms: usize, maximum_power: usize) -> Result<Bank, Failure> {
    check("INPUT", "equations", request.equations.len(), request.limits.equations)?;
    check("INPUT", "terms", supplied_terms, request.limits.terms)?;
    check("INPUT", "power_exponent", maximum_power, request.limits.power_exponent)?;
    let mut arithmetic = Arithmetic { limits: request.limits, steps: 0 };
    arithmetic.check("INPUT", &q(1, 1))?;
    let values = request.values.iter().map(|value| match value {
        ExactValue::Rational(value) => Ok(value.clone()),
        ExactValue::Algebraic { .. } => Err(internal("SOURCE_FIT_UNSUPPORTED_REACHED")),
    }).collect::<Result<Vec<_>, _>>()?;
    for value in &values { arithmetic.check("INPUT", value)?; }
    for polynomial in &request.equations {
        for coefficient in polynomial.terms.values() { arithmetic.check("INPUT", coefficient)?; }
    }
    let mut evaluations = Vec::with_capacity(request.equations.len());
    for polynomial in &request.equations {
        let mut sum = q(0, 1);
        for (powers, coefficient) in &polynomial.terms {
            let mut term = coefficient.clone();
            for (value, exponent) in values.iter().zip(powers) { if *exponent > 0 {
                let factor = arithmetic.power("TRACE", value, *exponent)?;
                term = arithmetic.multiply("TRACE", &term, &factor)?;
            } }
            sum = arithmetic.add("TRACE", &sum, &term)?;
        }
        if !sum.is_zero() { return Err(invalid("SOURCE_FIT_UNSATISFIED_SUPPLIED_TRACE").into()); }
        evaluations.push(sum);
    }
    let source = &request.context.source;
    let ages = heights(source)?;
    for age in &ages { arithmetic.check("CALENDAR", age)?; }
    let mut edges = source.edges.iter().enumerate().map(|(i, edge)| EdgeBank {
        original_edge: i, source: edge.source, target: edge.target,
        duration: &ages[edge.source] - &ages[edge.target], survival: values[i].clone(),
        active_slots: Vec::new(), active_exponent_sum: q(0, 1),
    }).collect::<Vec<_>>();
    if edges.iter().any(|edge| !edge.duration.is_positive()) {
        return Err(internal("SOURCE_FIT_STRICT_EDGE_DURATION").into());
    }
    let mut hybrids = Vec::with_capacity(source.hybrids.len());
    for (i, hybrid) in source.hybrids.iter().enumerate() {
        let old = &values[source.edges.len() + i];
        let gamma = arithmetic.add("GAMMA", &q(1, 1), &(-old))?;
        hybrids.push(HybridBank { original_hybrid: i, vertex: hybrid.vertex, incoming: hybrid.incoming,
            old_parent_zero_probability: old.clone(), original_parent_one_probability: gamma });
    }
    // Reuse the accepted producer for dates/word only. Every numerical proxy
    // coordinate and the parent unit-u Request are discarded below; none is
    // returned as an actual fitted physical rate or fitted calendar result.
    let proxy = calendar::Request { context: request.context.clone(), ages: ages.clone(),
        inverse_rates: vec![q(1, 1); source.edges.len() + 1],
        original_gamma: hybrids.iter().map(|h| h.original_parent_one_probability.clone()).collect(),
        common: vec![request.mechanism == Mechanism::Common; source.hybrids.len()],
        terminal: request.terminal, compiler_limits: request.compiler_limits,
        word_limits: word::Limits::default(), provider_limits: word::ProviderLimits::default() };
    let generated = match calendar::compile_calendar(&proxy) {
        Ok(calendar::CompileDecision::Generated(value)) => value,
        Ok(calendar::CompileDecision::Unknown(value)) => {
            let kind = match value.limit.kind { calendar::CompilerLimitKind::WordLength => "word_length",
                calendar::CompilerLimitKind::Slots => "slots", calendar::CompilerLimitKind::Variables => "variables" };
            return Err(Failure::Unknown(Limit { stage: "COMPILER", kind,
                required: value.limit.required.to_string(), cap: value.limit.cap }));
        }
        Err(calendar::Error::InvalidInput(code)) => return Err(invalid(code).into()),
        Err(calendar::Error::Unsupported(code)) | Err(calendar::Error::Internal(code)) =>
            return Err(internal(code).into()),
    };
    let mut coordinates = Vec::with_capacity(generated.requirements.variables);
    for slot in &generated.agenda.slots {
        arithmetic.check("COORDINATES", &slot.duration)?;
        if !slot.duration.is_positive() || slot.younger_date >= slot.older_date {
            return Err(internal("SOURCE_FIT_SLOT_DOMAIN").into());
        }
        for edge in &mut edges {
            let active = slot.younger_date >= ages[edge.target] && slot.older_date <= ages[edge.source];
            let exponent = arithmetic.divide("COORDINATES", &slot.duration, &edge.duration)?;
            let expression = edge_expression(edge, exponent.clone(), active, &mut arithmetic)?;
            if active {
                edge.active_slots.push(slot.slot);
                edge.active_exponent_sum = arithmetic.add("COORDINATES", &edge.active_exponent_sum, &exponent)?;
            }
            coordinates.push(Coordinate { variable: word::Variable::Survival {
                slot: slot.slot, population: Location::Edge(edge.original_edge) }, expression });
        }
        coordinates.push(Coordinate { variable: word::Variable::Survival {
            slot: slot.slot, population: Location::Ancestral(source.root) },
            expression: Expression::AncestralExpNeg { duration: slot.duration.clone(), active: false } });
    }
    if edges.iter().any(|edge| edge.active_exponent_sum != q(1, 1)) {
        return Err(internal("SOURCE_FIT_INCOMPLETE_EDGE_PARTITION").into());
    }
    for hybrid in &hybrids {
        coordinates.push(Coordinate { variable: word::Variable::OriginalGamma(hybrid.original_hybrid),
            expression: Expression::OriginalGamma(hybrid.original_parent_one_probability.clone()) });
    }
    let agenda = Agenda { dates: generated.agenda.dates, cohorts: generated.agenda.cohorts,
        origins: generated.agenda.origins, slots: generated.agenda.slots,
        leaf_age_zero: generated.agenda.leaf_age_zero };
    // generated.agenda.physical_coordinates and proxy are intentionally not
    // copied into Bank. symbolic_word carries no inverse rates at all.
    Ok(Bank { request: request.clone(), ages, edges, hybrids, agenda, coordinates,
        symbolic_word: generated.child, evaluations,
        work: Work { supplied_equations: request.equations.len(), supplied_terms,
            arithmetic_steps: arithmetic.steps } })
}

/// Shape/domain validation precedes soft arithmetic limits. An algebraic
/// descriptor returns Unsupported without claiming trace satisfaction.
pub fn bind(request: &Request) -> Result<Decision, Error> {
    let (terms, maximum_power) = validate(request)?;
    // Canonical bound transport is also a pre-generation input byte gate.
    canonical_request(request)?;
    let preflight = (|| {
        check("INPUT", "equations", request.equations.len(), request.limits.equations)?;
        check("INPUT", "terms", terms, request.limits.terms)?;
        check("INPUT", "power_exponent", maximum_power, request.limits.power_exponent)?;
        let arithmetic = Arithmetic { limits: request.limits, steps: 0 };
        arithmetic.check("INPUT", &q(1, 1))?;
        for value in &request.values { match value {
            ExactValue::Rational(value) => arithmetic.check("INPUT", value)?,
            ExactValue::Algebraic { polynomial_ascending, .. } => {
                for coefficient in polynomial_ascending { arithmetic.check("INPUT", coefficient)?; }
            }
        } }
        for polynomial in &request.equations {
            for coefficient in polynomial.terms.values() { arithmetic.check("INPUT", coefficient)?; }
        }
        Ok::<(), Failure>(())
    })();
    match preflight {
        Err(Failure::Unknown(limit)) => return Ok(Decision::Unknown(limit)),
        Err(Failure::Error(error)) => return Err(error),
        Ok(()) => {}
    }
    if let Some(first) = request.values.iter().position(|value| matches!(value, ExactValue::Algebraic { .. })) {
        return Ok(Decision::Unsupported { first_algebraic_variable: first,
            reason: "SOURCE_FIT_ALGEBRAIC_EVALUATION_NOT_IMPLEMENTED" });
    }
    match run(request, terms, maximum_power) {
        Ok(bank) => {
            let decision = Decision::SymbolicBank(bank);
            match canonical_response(request, &decision) {
                Ok(_) => Ok(decision),
                Err(Error::FrameLimit { required_at_least, cap }) => Ok(Decision::Unknown(Limit {
                    stage: "OUTPUT", kind: "result_bytes_lower_bound",
                    required: required_at_least.to_string(), cap })),
                Err(error) => Err(error),
            }
        }
        Err(Failure::Unknown(limit)) => Ok(Decision::Unknown(limit)),
        Err(Failure::Error(error)) => Err(error),
    }
}

/// Additional cuts may only lie inside the very same original edge. This is
/// useful for transporting an externally selected observation interval; it is
/// not a timed merger-history law or a new fitted slot variable.
pub fn coordinate_for_interval(bank: &Bank, original_edge: usize,
    younger: &Rational, older: &Rational, limits: Limits) -> Result<DecisionCoordinate, Error> {
    bounded_rational(younger)?; bounded_rational(older)?;
    if limits.equations > 4096 || limits.terms > 65_536 || limits.arithmetic_steps > 1_000_000
        || limits.rational_bits > 65_536 || limits.power_exponent > 4096 {
        return Err(invalid("SOURCE_FIT_LIMITS"));
    }
    let edge = bank.edges.get(original_edge).ok_or(invalid("SOURCE_FIT_EDGE_REFERENCE"))?;
    if younger >= older || younger < &bank.ages[edge.target] || older > &bank.ages[edge.source] {
        return Err(invalid("SOURCE_FIT_INTERVAL_DOMAIN"));
    }
    let mut arithmetic = Arithmetic { limits, steps: 0 };
    let result = (|| {
        arithmetic.check("COORDINATES", younger)?; arithmetic.check("COORDINATES", older)?;
        let duration = arithmetic.add("COORDINATES", older, &(-younger))?;
        let exponent = arithmetic.divide("COORDINATES", &duration, &edge.duration)?;
        edge_expression(edge, exponent, true, &mut arithmetic)
    })();
    match result {
        Ok(expression) => Ok(DecisionCoordinate::Coordinate(expression)),
        Err(Failure::Unknown(limit)) => Ok(DecisionCoordinate::Unknown(limit)),
        Err(Failure::Error(error)) => Err(error),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecisionCoordinate { Coordinate(Expression), Unknown(Limit) }

/// A bounded ASCII encoder, without adding a parser or a serde dependency to
/// the accepted core crate. Canonical fields are emitted in lexical key order.
/// This transport binds the complete semantic Request, not external raw-file
/// bytes. A wrapper must separately bind captured raw requests/source hashes.
struct Writer { text: String, cap: usize }
impl Writer {
    fn new(cap: usize) -> Self { Self { text: String::new(), cap } }
    fn raw(&mut self, token: &str) -> Result<(), Error> {
        let required = self.text.len().checked_add(token.len()).ok_or(internal("SOURCE_FIT_FRAME_COUNT"))?;
        if required > self.cap { return Err(Error::FrameLimit { required_at_least: required, cap: self.cap }); }
        self.text.push_str(token); Ok(())
    }
    fn string(&mut self, value: &str) -> Result<(), Error> {
        self.raw("\"")?;
        for unit in value.encode_utf16() {
            match unit {
                0x22 => self.raw("\\\"")?, 0x5c => self.raw("\\\\")?,
                0x20..=0x7e => self.raw(&(unit as u8 as char).to_string())?,
                _ => self.raw(&format!("\\u{unit:04x}"))?,
            }
        }
        self.raw("\"")
    }
    fn natural(&mut self, value: usize) -> Result<(), Error> { self.raw(&value.to_string()) }
    fn rational(&mut self, value: &Rational) -> Result<(), Error> { self.string(&canonical(value)) }
    fn boolean(&mut self, value: bool) -> Result<(), Error> { self.raw(if value { "true" } else { "false" }) }
    fn naturals(&mut self, values: &[usize]) -> Result<(), Error> {
        self.raw("[")?;
        for (i, value) in values.iter().enumerate() { if i > 0 { self.raw(",")?; } self.natural(*value)?; }
        self.raw("]")
    }
    fn rationals(&mut self, values: &[Rational]) -> Result<(), Error> {
        self.raw("[")?;
        for (i, value) in values.iter().enumerate() { if i > 0 { self.raw(",")?; } self.rational(value)?; }
        self.raw("]")
    }
    fn strings(&mut self, values: &[String]) -> Result<(), Error> {
        self.raw("[")?;
        for (i, value) in values.iter().enumerate() { if i > 0 { self.raw(",")?; } self.string(value)?; }
        self.raw("]")
    }
    fn context(&mut self, context: &Context) -> Result<(), Error> {
        let source = &context.source;
        self.raw("{\"edges\":[")?;
        for (i, edge) in source.edges.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.naturals(&[edge.source, edge.target])?; }
        self.raw("],\"global_labels\":")?; self.naturals(&context.global_labels)?;
        self.raw(",\"hybrids\":[")?;
        for (i, hybrid) in source.hybrids.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.naturals(&[hybrid.vertex, hybrid.incoming[0], hybrid.incoming[1]])?; }
        self.raw("],\"leaves\":")?; self.naturals(&source.leaves)?;
        self.raw(",\"local_samples\":")?; self.naturals(&context.sample)?;
        self.raw(",\"root\":")?; self.natural(source.root)?;
        self.raw(",\"vertices\":")?; self.natural(source.vertices)?; self.raw("}")
    }
    fn request(&mut self, request: &Request) -> Result<(), Error> {
        self.raw("{\"compiler_limits\":{\"slots\":")?; self.natural(request.compiler_limits.slots)?;
        self.raw(",\"variables\":")?; self.natural(request.compiler_limits.variables)?;
        self.raw(",\"word_length\":")?; self.natural(request.compiler_limits.word_length)?;
        self.raw("},\"context\":")?; self.context(&request.context)?;
        self.raw(",\"copy_labels\":")?; self.strings(&request.copy_labels)?;
        self.raw(",\"equations\":[")?;
        for (i, polynomial) in request.equations.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.raw("{\"dimension\":")?; self.natural(polynomial.dimension)?;
            self.raw(",\"terms\":[")?;
            for (j, (powers, coefficient)) in polynomial.terms.iter().enumerate() { if j > 0 { self.raw(",")?; }
                self.raw("[")?; self.naturals(powers)?; self.raw(",")?; self.rational(coefficient)?; self.raw("]")?; }
            self.raw("]}")?;
        }
        self.raw("],\"hybrid_labels\":")?; self.strings(&request.hybrid_labels)?;
        self.raw(",\"limits\":{\"arithmetic_steps\":")?; self.natural(request.limits.arithmetic_steps)?;
        self.raw(",\"equations\":")?; self.natural(request.limits.equations)?;
        self.raw(",\"power_exponent\":")?; self.natural(request.limits.power_exponent)?;
        self.raw(",\"rational_bits\":")?; self.natural(request.limits.rational_bits)?;
        self.raw(",\"terms\":")?; self.natural(request.limits.terms)?;
        self.raw("},\"mechanism\":")?;
        self.string(match request.mechanism { Mechanism::Common => "COMMON", Mechanism::Independent => "INDEPENDENT" })?;
        self.raw(",\"schema\":\"source_fit_bank_request_v1\",\"taxon_labels\":")?; self.strings(&request.taxon_labels)?;
        self.raw(",\"terminal\":")?;
        self.string(match request.terminal { word::Terminal::FullView => "FULL_VIEW", word::Terminal::AncestralComplete => "ANCESTRAL_COMPLETE" })?;
        self.raw(",\"values\":[")?;
        for (i, value) in request.values.iter().enumerate() { if i > 0 { self.raw(",")?; }
            match value {
                ExactValue::Rational(value) => { self.raw("{\"kind\":\"rational\",\"value\":")?;
                    self.rational(value)?; self.raw("}")?; }
                ExactValue::Algebraic { polynomial_ascending, real_root_index } => {
                    self.raw("{\"kind\":\"algebraic\",\"polynomial_ascending\":")?; self.rationals(polynomial_ascending)?;
                    self.raw(",\"real_root_index\":")?; self.natural(*real_root_index)?; self.raw("}")?;
                }
            }
        }
        self.raw("],\"variables\":")?; self.strings(&request.variables)?;
        self.raw(",\"vertex_names\":")?; self.strings(&request.vertex_names)?; self.raw("}")
    }
    fn expression(&mut self, expression: &Expression) -> Result<(), Error> {
        match expression {
            Expression::EdgePower { original_edge, exponent, active, constraint, rational_value } => {
                self.raw("{\"active\":")?; self.boolean(*active)?;
                if let Some(constraint) = constraint {
                    self.raw(",\"constraint\":{\"coefficients\":[[0,")?;
                    self.string(&format!("{}/1", constraint.constant))?;
                    self.raw("],[")?; self.natural(constraint.degree)?; self.raw(",")?;
                    self.string(&format!("{}/1", constraint.leading))?;
                    self.raw("]],\"domain\":[\"0/1\",\"1/1\"],\"root_evaluated\":false}")?;
                }
                self.raw(",\"exponent\":")?; self.rational(exponent)?;
                self.raw(",\"kind\":\"EDGE_POWER\",\"original_edge\":")?; self.natural(*original_edge)?;
                if let Some(value) = rational_value { self.raw(",\"rational_value\":")?; self.rational(value)?; }
                self.raw("}")
            }
            Expression::AncestralExpNeg { duration, active } => {
                self.raw("{\"active\":")?; self.boolean(*active)?;
                self.raw(",\"argument\":")?; self.rational(duration)?;
                self.raw(",\"kind\":\"EXP_NEG_ANCESTRAL_UNIT\",\"value_evaluated\":false}")
            }
            Expression::OriginalGamma(value) => { self.raw("{\"kind\":\"RATIONAL_ORIGINAL_GAMMA\",\"value\":")?;
                self.rational(value)?; self.raw("}") }
        }
    }
    fn variable(&mut self, variable: word::Variable) -> Result<(), Error> {
        self.string(&match variable {
            word::Variable::Survival { slot, population: Location::Edge(edge) } => format!("X:{slot}:E:{edge}"),
            word::Variable::Survival { slot, population: Location::Ancestral(root) } => format!("X:{slot}:A:{root}"),
            word::Variable::Survival { slot, population: Location::Node(vertex) } => format!("X:{slot}:V:{vertex}"),
            word::Variable::OriginalGamma(hybrid) => format!("ORIGINAL_GAMMA:{hybrid}"),
        })
    }
    fn bank(&mut self, bank: &Bank) -> Result<(), Error> {
        self.raw("{\"agenda\":{\"cohorts\":[")?;
        for (i, cohort) in bank.agenda.cohorts.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.raw("{\"date_index\":")?; self.natural(cohort.date_index)?;
            self.raw(",\"exits\":")?; self.naturals(&cohort.exits)?;
            self.raw(",\"representative\":")?; self.natural(cohort.representative)?;
            self.raw(",\"vertices\":")?; self.naturals(&cohort.vertices)?; self.raw("}")?; }
        self.raw("],\"dates\":")?; self.rationals(&bank.agenda.dates)?;
        self.raw(",\"leaf_age_zero\":")?; self.boolean(bank.agenda.leaf_age_zero)?;
        self.raw(",\"origins\":[")?;
        for (i, origin) in bank.agenda.origins.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.raw("{\"date_index\":")?; self.natural(origin.date_index)?;
            self.raw(",\"index\":")?; self.natural(origin.index)?;
            self.raw(",\"phase\":")?; self.string(match origin.phase {
                calendar::Phase::Exit => "EXIT", calendar::Phase::Enter => "ENTER", calendar::Phase::Interval => "INTERVAL" })?;
            self.raw("}")?; }
        self.raw("],\"slots\":[")?;
        for (i, slot) in bank.agenda.slots.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.raw("{\"duration\":")?; self.rational(&slot.duration)?;
            self.raw(",\"older_date\":")?; self.rational(&slot.older_date)?;
            self.raw(",\"slot\":")?; self.natural(slot.slot)?;
            self.raw(",\"word_position\":")?; self.natural(slot.word_position)?;
            self.raw(",\"younger_date\":")?; self.rational(&slot.younger_date)?; self.raw("}")?; }
        self.raw("]},\"ages\":")?; self.rationals(&bank.ages)?;
        self.raw(",\"ancestral_inverse_rate\":\"1/1\",\"coordinates\":[")?;
        for (i, coordinate) in bank.coordinates.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.raw("{\"expression\":")?; self.expression(&coordinate.expression)?;
            self.raw(",\"variable\":")?; self.variable(coordinate.variable)?; self.raw("}")?; }
        self.raw("],\"edges\":[")?;
        for (i, edge) in bank.edges.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.raw("{\"active_exponent_sum\":")?; self.rational(&edge.active_exponent_sum)?;
            self.raw(",\"active_slots\":")?; self.naturals(&edge.active_slots)?;
            self.raw(",\"duration\":")?; self.rational(&edge.duration)?;
            self.raw(",\"inverse_rate\":{\"denominator\":{\"kind\":\"NEG_LOG\",\"original_edge\":")?;
            self.natural(edge.original_edge)?; self.raw(",\"survival\":")?; self.rational(&edge.survival)?;
            self.raw("},\"numerator\":")?; self.rational(&edge.duration)?;
            self.raw("},\"original_edge\":")?; self.natural(edge.original_edge)?;
            self.raw(",\"source\":")?; self.natural(edge.source)?;
            self.raw(",\"survival\":")?; self.rational(&edge.survival)?;
            self.raw(",\"target\":")?; self.natural(edge.target)?; self.raw("}")?; }
        self.raw("],\"evaluations\":")?; self.rationals(&bank.evaluations)?;
        self.raw(",\"hybrids\":[")?;
        for (i, hybrid) in bank.hybrids.iter().enumerate() { if i > 0 { self.raw(",")?; }
            self.raw("{\"incoming\":")?; self.naturals(&hybrid.incoming)?;
            self.raw(",\"old_parent_zero_probability\":")?; self.rational(&hybrid.old_parent_zero_probability)?;
            self.raw(",\"original_hybrid\":")?; self.natural(hybrid.original_hybrid)?;
            self.raw(",\"original_parent_one_probability\":")?; self.rational(&hybrid.original_parent_one_probability)?;
            self.raw(",\"vertex\":")?; self.natural(hybrid.vertex)?; self.raw("}")?; }
        self.raw("],\"rational_calendar_dto_supported\":false,\"symbolic_word\":{\"common\":[")?;
        for (i, value) in bank.symbolic_word.common.iter().enumerate() { if i > 0 { self.raw(",")?; } self.boolean(*value)?; }
        self.raw("],\"initial\":\"NATURAL\",\"slots\":")?; self.natural(bank.symbolic_word.slots)?;
        self.raw(",\"terminal\":")?; self.string(match bank.symbolic_word.terminal {
            word::Terminal::FullView => "FULL_VIEW", word::Terminal::AncestralComplete => "ANCESTRAL_COMPLETE" })?;
        self.raw(",\"word\":[")?;
        for (i, symbol) in bank.symbolic_word.word.iter().enumerate() { if i > 0 { self.raw(",")?; }
            let (name, index) = match symbol { word::Symbol::Interval(index) => ("INTERVAL", *index),
                word::Symbol::Exit(index) => ("EXIT", *index), word::Symbol::Enter(index) => ("ENTER", *index) };
            self.raw("[")?; self.string(name)?; self.raw(",")?; self.natural(index)?; self.raw("]")?; }
        self.raw("]},\"work\":{\"arithmetic_steps\":")?; self.natural(bank.work.arithmetic_steps)?;
        self.raw(",\"supplied_equations\":")?; self.natural(bank.work.supplied_equations)?;
        self.raw(",\"supplied_terms\":")?; self.natural(bank.work.supplied_terms)?; self.raw("}}")
    }
}

pub fn canonical_request(request: &Request) -> Result<String, Error> {
    validate(request)?;
    let mut writer = Writer::new(MAX_REQUEST_BYTES);
    match writer.request(request).and_then(|_| writer.raw("\n")) {
        Ok(()) => Ok(writer.text),
        Err(Error::FrameLimit { .. }) => Err(invalid("SOURCE_FIT_REQUEST_BYTES")),
        Err(error) => Err(error),
    }
}
pub fn canonical_response(request: &Request, decision: &Decision) -> Result<String, Error> {
    canonical_request(request)?;
    if let Decision::SymbolicBank(bank) = decision {
        if bank.request() != request { return Err(invalid("SOURCE_FIT_RESPONSE_REQUEST_BINDING")); }
    }
    let mut writer = Writer::new(MAX_RESULT_BYTES);
    writer.raw("{")?;
    if let Decision::SymbolicBank(bank) = decision { writer.raw("\"bank\":")?; writer.bank(bank)?; writer.raw(",")?; }
    writer.raw("\"certificate_valid\":false,\"full_solver_verified\":false")?;
    match decision {
        Decision::Unknown(limit) => {
            writer.raw(",\"limit\":{\"cap\":")?; writer.natural(limit.cap)?;
            writer.raw(",\"kind\":")?; writer.string(limit.kind)?;
            writer.raw(",\"required\":")?; writer.string(&limit.required)?;
            writer.raw(",\"stage\":")?; writer.string(limit.stage)?; writer.raw("}")?;
        }
        Decision::Unsupported { first_algebraic_variable, reason } => {
            writer.raw(",\"reason\":{\"first_algebraic_variable\":")?; writer.natural(*first_algebraic_variable)?;
            writer.raw(",\"kind\":")?; writer.string(reason)?; writer.raw("}")?;
        }
        Decision::SymbolicBank(_) => {}
    }
    writer.raw(",\"request\":")?; writer.request(request)?;
    writer.raw(",\"schema\":\"source_fit_bank_result_v1\",\"source_admission_verified\":false,\"source_observation_fit_verified\":false,\"source_provenance_verified\":false,\"status\":")?;
    writer.string(match decision { Decision::SymbolicBank(_) => "SYMBOLIC_BANK",
        Decision::Unknown(_) => "UNKNOWN", Decision::Unsupported { .. } => "UNSUPPORTED" })?;
    writer.raw(",\"supplied_trace_checked\":")?; writer.boolean(matches!(decision, Decision::SymbolicBank(_)))?;
    writer.raw(",\"timed_readout_verified\":false}\n")?;
    Ok(writer.text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::natural_cell::{Edge, Hybrid};
    use std::collections::BTreeMap;

    fn polynomial(terms: &[(&[usize], i64, i64)]) -> Polynomial {
        Polynomial { dimension: 6, terms: terms.iter().map(|(powers, n, d)|
            (powers.to_vec(), q(*n, *d))).collect::<BTreeMap<_, _>>() }
    }
    /// Direct transcription of all twelve equations, including the 1/4,3/4
    /// randomized joint program, in the preserved hybrid-common-sat result.
    fn common_witness() -> Request {
        let natural = polynomial(&[
            (&[0,1,0,1,0,1],1,3), (&[0,0,1,1,0,1],-1,3),
            (&[0,0,1,1,0,0],1,3), (&[0,0,0,0,0,0],-17,135)]);
        let forced_zero = polynomial(&[(&[0,1,0,1,0,0],1,3), (&[0,0,0,0,0,0],-1,9)]);
        let forced_one = polynomial(&[(&[0,0,1,1,0,0],1,3), (&[0,0,0,0,0,0],-2,15)]);
        let randomized = polynomial(&[(&[0,1,0,1,0,0],1,12), (&[0,0,1,1,0,0],1,4),
            (&[0,0,0,0,0,0],-23,180)]);
        let mut equations = Vec::new();
        for row in [natural, forced_zero, forced_one, randomized] {
            equations.push(row.clone()); equations.push(row.clone()); equations.push(row.scale(&q(-2, 1)));
        }
        Request {
            context: Context { source: Source { vertices: 5, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
                    Edge { source: 1, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 1, target: 4 }],
                leaves: vec![3,4], hybrids: vec![Hybrid { vertex: 2, incoming: [1,2] }] },
                sample: vec![0,0,1], global_labels: vec![0,1,2] },
            vertex_names: ["R","T0","H0","L0","L1"].map(str::to_string).to_vec(),
            taxon_labels: ["L0","L1"].map(str::to_string).to_vec(),
            hybrid_labels: vec!["site_alpha".into()], copy_labels: ["a","b","c"].map(str::to_string).to_vec(),
            variables: ["x0","x1","x2","x3","x4","g_H0"].map(str::to_string).to_vec(),
            values: [q(1,2),q(2,3),q(4,5),q(1,2),q(1,2),q(1,3)].map(ExactValue::Rational).to_vec(),
            equations, mechanism: Mechanism::Common, terminal: word::Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits::default(), limits: Limits::default(),
        }
    }
    fn bank(request: &Request) -> Bank {
        match bind(request).unwrap() { Decision::SymbolicBank(bank) => bank,
            other => panic!("expected bank, got {other:?}") }
    }

    #[test]
    fn recovered_joint_trace_orientation_and_shared_cuts() {
        let request = common_witness();
        let bank = bank(&request);
        assert_eq!(bank.ages(), &[q(3,1),q(2,1),q(1,1),q(0,1),q(0,1)]);
        assert_eq!(bank.evaluations(), &vec![q(0,1);12]);
        assert_eq!(bank.hybrids()[0].original_parent_one_probability, q(2,3));
        assert_eq!(bank.forced_parent(0,0).unwrap(),1);
        assert_eq!(bank.forced_parent(0,1).unwrap(),2);
        assert_eq!(bank.symbolic_word().common, vec![true]);
        assert_eq!(bank.symbolic_word().initial, word::Initial::Natural);
        assert!(bank.edges().iter().all(|edge| edge.active_exponent_sum == q(1,1)));
        assert_eq!(bank.edges()[1].active_slots, vec![1,2]);
        let fractional = coordinate_for_interval(&bank,1,&q(1,1),&q(2,1),Limits::default()).unwrap();
        assert_eq!(fractional, DecisionCoordinate::Coordinate(Expression::EdgePower { original_edge: 1,
            exponent: q(1,2), active: true, constraint: Some(PositiveRootConstraint {
                degree: 2, leading: 3.into(), constant: (-2).into() }), rational_value: None }));
        let whole = coordinate_for_interval(&bank,1,&q(1,1),&q(3,1),Limits::default()).unwrap();
        assert!(matches!(whole, DecisionCoordinate::Coordinate(Expression::EdgePower {
            rational_value: Some(value), .. }) if value == q(2,3)));
        assert!(bank.rational_calendar_request().is_err());
        let response = canonical_response(&request,&Decision::SymbolicBank(bank)).unwrap();
        assert!(response.contains("\"source_observation_fit_verified\":false"));
        assert!(response.contains("\"timed_readout_verified\":false"));
        assert!(!response.contains("\"physical_coordinates\""));
        assert!(!response.contains("\"inverse_rates\""));
    }
    #[test]
    fn mismatched_trace_binding_and_interval_are_refused() {
        let request = common_witness();
        let solved = bank(&request);
        let mut changed = request.clone();
        changed.equations[0].terms.insert(vec![0;6],q(-18,135));
        assert_eq!(bind(&changed),Err(invalid("SOURCE_FIT_UNSATISFIED_SUPPLIED_TRACE")));
        changed = request.clone(); changed.variables.swap(0,1);
        assert_eq!(bind(&changed),Err(invalid("SOURCE_FIT_VARIABLE_BANK")));
        changed = request.clone(); changed.context.source.hybrids[0].incoming.swap(0,1);
        assert_eq!(bind(&changed),Err(invalid("SOURCE_FIT_INHERITED_PARENT_ORDER")));
        changed = request.clone(); changed.values[5] = ExactValue::Rational(q(1,2));
        assert_eq!(canonical_response(&changed,&Decision::SymbolicBank(solved.clone())),
            Err(invalid("SOURCE_FIT_RESPONSE_REQUEST_BINDING")));
        assert_eq!(coordinate_for_interval(&solved,1,&q(0,1),&q(2,1),Limits::default()),
            Err(invalid("SOURCE_FIT_INTERVAL_DOMAIN")));
        assert_eq!(coordinate_for_interval(&solved,1,&q(2,1),&q(2,1),Limits::default()),
            Err(invalid("SOURCE_FIT_INTERVAL_DOMAIN")));
    }
    #[test]
    fn parallel_occurrences_remain_distinct_and_forcing_is_not_complemented() {
        let mut request = common_witness();
        request.context.source = Source { vertices: 5, root: 0,
            edges: vec![Edge { source:0,target:1 },Edge { source:0,target:2 },
                Edge { source:2,target:3 },Edge { source:2,target:3 },Edge { source:3,target:4 }],
            leaves: vec![1,4],hybrids:vec![Hybrid {vertex:3,incoming:[2,3]}] };
        request.vertex_names = ["R","L0","T0","H0","L1"].map(str::to_string).to_vec();
        request.values[2] = ExactValue::Rational(q(1,2));
        request.values[3] = ExactValue::Rational(q(3,4));
        // This trace is deliberately uninformative. It must not establish
        // source-observation fit merely because zero is satisfied.
        request.equations = vec![Polynomial::zero(6)];
        let solved = bank(&request);
        assert_eq!(solved.edges()[2].survival,q(1,2));
        assert_eq!(solved.edges()[3].survival,q(3,4));
        assert_eq!(solved.forced_parent(0,0).unwrap(),2);
        assert_eq!(solved.forced_parent(0,1).unwrap(),3);
        assert!(solved.forced_parent(0,2).is_err());
        assert!(canonical_response(&request,&Decision::SymbolicBank(solved)).unwrap()
            .contains("\"source_observation_fit_verified\":false"));
    }
    #[test]
    fn algebraic_codec_is_preserved_without_a_fictitious_root_check() {
        let mut request = common_witness();
        request.values[1] = ExactValue::Algebraic { polynomial_ascending: vec![q(-2,3),q(0,1),q(1,1)],
            real_root_index: 2 };
        let decision = bind(&request).unwrap();
        assert!(matches!(decision, Decision::Unsupported { first_algebraic_variable: 1, .. }));
        let response = canonical_response(&request,&decision).unwrap();
        assert!(response.contains("\"polynomial_ascending\":[\"-2/3\",\"0/1\",\"1/1\"]"));
        assert!(response.contains("\"real_root_index\":2"));
        assert!(response.contains("\"supplied_trace_checked\":false"));
    }
    #[test]
    fn input_and_root_budgets_return_no_partial_bank_and_domain_takes_priority() {
        let mut request = common_witness(); request.limits.rational_bits = 2;
        assert!(matches!(bind(&request).unwrap(), Decision::Unknown(Limit {
            stage:"INPUT",kind:"rational_bits",.. })));
        request = common_witness(); request.limits.power_exponent = 1;
        assert!(matches!(bind(&request).unwrap(), Decision::Unknown(Limit {
            stage:"COORDINATES",kind:"power_exponent",.. })));
        request = common_witness(); request.values[0] = ExactValue::Rational(q(0,1));
        request.limits.arithmetic_steps = 0;
        assert_eq!(bind(&request),Err(invalid("SOURCE_FIT_STRICT_INTERIOR")));
    }
}

