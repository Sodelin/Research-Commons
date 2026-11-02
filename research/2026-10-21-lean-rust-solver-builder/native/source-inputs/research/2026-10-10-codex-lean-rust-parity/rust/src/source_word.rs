//! One supplied original-source symbolic word on the full ordered carrier.
//!
//! SourceProgramTransport and G7SymbolicProgramPolynomial already establish
//! source-side word projection. This internal port composes the existing exact
//! epoch/boundary providers with range witnesses and one shared variable bank.
//! It does not admit arbitrary words as physical calendars or add an endpoint.
use crate::{forest::Tree, polynomial::Polynomial, source_boundary as boundary, source_completion as completion,
    source_epoch::{self as epoch, SelectedView, Transition},
    source_population::{self as population, Context, Location, Snapshot}};
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Initial { Natural, Conditional(Snapshot) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Symbol { Interval(usize), Exit(usize), Enter(usize) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Terminal { FullView, AncestralComplete }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Variable {
    Survival { slot: usize, population: Location },
    OriginalGamma(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub initial_assignments: usize,
    pub initial_terms: usize,
    pub queries: usize,
    pub branches: usize,
    pub term_products: usize,
    pub destinations: usize,
    pub terms: usize,
}
impl Default for Limits {
    fn default() -> Self { Self { initial_assignments: 16, initial_terms: 256,
        queries: 4096, branches: 65536, term_products: 262144,
        destinations: 4096, terms: 65536 } }
}
/// These limits apply separately to each unchanged conditional provider query.
/// Provider refusals retain their original kind, count and population metadata.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct ProviderLimits {
    pub epoch: epoch::Limits,
    pub boundary: boundary::Limits,
    pub completion: population::Limits,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub context: Context,
    pub initial: Initial,
    /// Exactly one fixed mode per original hybrid; true means COMMON.
    pub common: Vec<bool>,
    pub slots: usize,
    pub word: Vec<Symbol>,
    pub terminal: Terminal,
    pub limits: Limits,
    pub provider_limits: ProviderLimits,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage { Initialization, Letter(usize), Completion }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitKind {
    InitialAssignments, InitialTerms, Queries, Branches, TermProducts,
    Destinations, Terms, Epoch(epoch::LimitKind), Boundary(boundary::LimitKind),
    Completion(population::LimitKind),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limit {
    pub stage: Stage,
    pub kind: LimitKind,
    pub population: Option<Location>,
    pub required: usize,
    pub cap: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Work {
    pub initial_assignments: usize,
    pub initial_term_contributions: usize,
    pub queries: usize,
    pub branches: usize,
    pub term_products: usize,
    pub largest_row: usize,
    pub largest_terms: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table { pub variables: Vec<Variable>, pub transitions: Vec<Transition>, pub work: Work }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision { Table(Table), Unknown(Limit) }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error { InvalidInput(&'static str), Unsupported(&'static str), Internal(&'static str) }

#[derive(Clone, Copy)]
enum Step { Epoch(usize), Boundary(boundary::Action), Completion }
enum Failure { Unknown(Limit), Error(Error) }
impl From<Error> for Failure { fn from(error: Error) -> Self { Self::Error(error) } }
type Row = BTreeMap<String, Transition>;

fn add(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_add(b).ok_or(Error::Internal("SOURCE_WORD_WORK_OVERFLOW"))
}
fn multiply(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_mul(b).ok_or(Error::Internal("SOURCE_WORD_WORK_OVERFLOW"))
}
fn check(stage: Stage, kind: LimitKind, required: usize, cap: usize) -> Result<(), Failure> {
    if required > cap { Err(Failure::Unknown(Limit { stage, kind, required, cap, population: None })) }
    else { Ok(()) }
}

/// Resolve Enter from the same original registry/modes for the whole word.
fn resolve(request: &Request, symbol: Symbol) -> Result<Step, Error> {
    let source = &request.context.source;
    match symbol {
        Symbol::Interval(slot) if slot < request.slots => Ok(Step::Epoch(slot)),
        Symbol::Interval(_) => Err(Error::InvalidInput("SOURCE_WORD_SLOT")),
        Symbol::Exit(edge) if edge < source.edges.len() => Ok(Step::Boundary(boundary::Action::Exit(edge))),
        Symbol::Exit(_) => Err(Error::InvalidInput("SOURCE_WORD_EDGE")),
        Symbol::Enter(vertex) => {
            if vertex >= source.vertices { return Err(Error::InvalidInput("SOURCE_WORD_VERTEX")); }
            if vertex == source.root { return Ok(Step::Boundary(boundary::Action::Root)); }
            if let Some(hybrid) = source.hybrids.iter().position(|entry| entry.vertex == vertex) {
                return Ok(Step::Boundary(if request.common[hybrid] { boundary::Action::Common(hybrid) }
                    else { boundary::Action::Independent(hybrid) }));
            }
            let incoming = source.edges.iter().enumerate().filter(|(_, edge)| edge.target == vertex)
                .map(|(edge, _)| edge).collect::<Vec<_>>();
            if incoming.len() != 1 { return Err(Error::InvalidInput("SOURCE_WORD_ORDINARY_DEGREE")); }
            Ok(Step::Boundary(boundary::Action::Ordinary(incoming[0])))
        }
    }
}

fn validate(request: &Request) -> Result<(Vec<Variable>, Vec<Step>), Error> {
    request.context.validate().map_err(Error::InvalidInput)?;
    let source = &request.context.source;
    if request.common.len() != source.hybrids.len() {
        return Err(Error::InvalidInput("SOURCE_WORD_MODE_REGISTRY"));
    }
    if request.slots > 16 || request.word.len() > 32
        || request.context.global_labels.iter().any(|label| u64::try_from(*label).is_err()) {
        return Err(Error::InvalidInput("SOURCE_WORD_INPUT_CAP"));
    }
    let populations = source.edges.len().checked_add(1).ok_or(Error::InvalidInput("SOURCE_WORD_BANK"))?;
    let dimension = request.slots.checked_mul(populations).and_then(|n| n.checked_add(source.hybrids.len()))
        .ok_or(Error::InvalidInput("SOURCE_WORD_BANK"))?;
    if populations > 32 || dimension > 256 { return Err(Error::InvalidInput("SOURCE_WORD_BANK")); }
    if let Initial::Conditional(snapshot) = &request.initial {
        request.context.validate_snapshot(snapshot).map_err(Error::InvalidInput)?;
    }
    // Validate all letters before a low work cap can mask a malformed tail.
    let steps = request.word.iter().map(|symbol| resolve(request, *symbol)).collect::<Result<Vec<_>, _>>()?;
    if request.terminal == Terminal::AncestralComplete && request.context.sample.is_empty() {
        return Err(Error::InvalidInput("SOURCE_WORD_COMPLETION_EMPTY_COPY"));
    }
    let variables = (0..request.slots).flat_map(|slot|
        (0..source.edges.len()).map(move |edge| Variable::Survival { slot, population: Location::Edge(edge) })
            .chain(std::iter::once(Variable::Survival { slot, population: Location::Ancestral(source.root) })))
        .chain((0..source.hybrids.len()).map(Variable::OriginalGamma)).collect::<Vec<_>>();
    if variables.len() != dimension { return Err(Error::Internal("SOURCE_WORD_BANK")); }
    Ok((variables, steps))
}

fn embed(polynomial: &Polynomial, dimension: usize, map: &[usize]) -> Result<Polynomial, Error> {
    if polynomial.dimension != map.len() || map.iter().any(|variable| *variable >= dimension)
        || map.iter().collect::<BTreeSet<_>>().len() != map.len() {
        return Err(Error::Internal("SOURCE_WORD_VARIABLE_EMBEDDING"));
    }
    let mut result = Polynomial::zero(dimension);
    for (powers, coefficient) in &polynomial.terms {
        if powers.len() != map.len() || coefficient.is_zero() {
            return Err(Error::Internal("SOURCE_WORD_PROVIDER_POLYNOMIAL"));
        }
        let mut renamed = vec![0; dimension];
        for (power, variable) in powers.iter().zip(map) { renamed[*variable] = *power; }
        if result.terms.insert(renamed, coefficient.clone()).is_some() {
            return Err(Error::Internal("SOURCE_WORD_VARIABLE_EMBEDDING"));
        }
    }
    Ok(result)
}

fn accumulate(context: &Context, row: &mut Row, transition: Transition) -> Result<(), Error> {
    if epoch::selected_view(context, &transition.witness).map_err(Error::Internal)? != transition.view {
        return Err(Error::Internal("SOURCE_WORD_RANGE_WITNESS"));
    }
    if transition.polynomial.is_zero() { return Ok(()); }
    let key = epoch::selected_key(&transition.view);
    if let Some(old) = row.get(&key) {
        let polynomial = old.polynomial.add(&transition.polynomial).map_err(Error::Internal)?;
        let witness = if population::snapshot_key(&old.witness) < population::snapshot_key(&transition.witness) {
            old.witness.clone()
        } else { transition.witness };
        if polynomial.is_zero() { row.remove(&key); }
        else { row.insert(key, Transition { view: transition.view, witness, polynomial }); }
    } else { row.insert(key, transition); }
    Ok(())
}
fn terms(row: &Row) -> Result<usize, Error> {
    row.values().try_fold(0, |total, transition| add(total, transition.polynomial.terms.len()))
}
fn stage_check(row: &Row, stage: Stage, limits: Limits, work: &mut Work) -> Result<(), Failure> {
    check(stage, LimitKind::Destinations, row.len(), limits.destinations)?;
    let count = terms(row)?;
    check(stage, LimitKind::Terms, count, limits.terms)?;
    work.largest_row = work.largest_row.max(row.len());
    work.largest_terms = work.largest_terms.max(count);
    Ok(())
}

fn initial_rows(request: &Request, dimension: usize, work: &mut Work) -> Result<Row, Failure> {
    let hybrids = request.context.source.hybrids.len();
    let (assignments, contributions) = match request.initial {
        Initial::Conditional(_) => (1, 1),
        Initial::Natural => {
            let exponent = u32::try_from(hybrids).map_err(|_| Error::Internal("SOURCE_WORD_WORK_OVERFLOW"))?;
            (2usize.checked_pow(exponent).ok_or(Error::Internal("SOURCE_WORD_WORK_OVERFLOW"))?,
                3usize.checked_pow(exponent).ok_or(Error::Internal("SOURCE_WORD_WORK_OVERFLOW"))?)
        }
    };
    check(Stage::Initialization, LimitKind::InitialAssignments, assignments, request.limits.initial_assignments)?;
    check(Stage::Initialization, LimitKind::InitialTerms, contributions, request.limits.initial_terms)?;
    let mut row = Row::new();
    let gamma_base = dimension.checked_sub(hybrids).ok_or(Error::Internal("SOURCE_WORD_BANK"))?;
    for mask in 0..assignments {
        let (witness, polynomial) = match &request.initial {
            Initial::Conditional(snapshot) => (snapshot.clone(), Polynomial::one(dimension)),
            Initial::Natural => {
                let copies = request.context.sample.len();
                let mut register = vec![false; request.context.source.vertices];
                let mut polynomial = Polynomial::one(dimension);
                for (hybrid, original) in request.context.source.hybrids.iter().enumerate() {
                    let bit = mask & (1usize << (hybrids - hybrid - 1)) != 0;
                    register[original.vertex] = bit;
                    let gamma = Polynomial::variable(dimension, add(gamma_base, hybrid)?).map_err(Error::Internal)?;
                    let factor = if bit { gamma } else { Polynomial::one(dimension).subtract(&gamma).map_err(Error::Internal)? };
                    polynomial = polynomial.multiply(&factor).map_err(Error::Internal)?;
                }
                (Snapshot { live: (0..copies).collect(), ancestor: (0..copies).collect(),
                    genealogy: (0..copies).map(|copy| Some(Tree::Leaf(copy))).collect(),
                    population: request.context.sample.iter().map(|sample|
                        Some(Location::Node(request.context.source.leaves[*sample]))).collect(), register }, polynomial)
            }
        };
        let view = epoch::selected_view(&request.context, &witness).map_err(Error::Internal)?;
        accumulate(&request.context, &mut row, Transition { view, witness, polynomial })?;
    }
    if row.len() != assignments || terms(&row)? != contributions {
        return Err(Error::Internal("SOURCE_WORD_INITIAL_WORK_IDENTITY").into());
    }
    work.initial_assignments = assignments;
    work.initial_term_contributions = contributions;
    stage_check(&row, Stage::Initialization, request.limits, work)?;
    Ok(row)
}

fn provider_row(request: &Request, snapshot: &Snapshot, step: Step, stage: Stage, dimension: usize)
    -> Result<Vec<Transition>, Failure> {
    let source = &request.context.source;
    let populations = add(source.edges.len(), 1)?;
    let (transitions, map) = match step {
        Step::Epoch(slot) => {
            let result = epoch::epoch_row(&request.context, snapshot, request.provider_limits.epoch)
                .map_err(Error::Internal)?;
            let table = match result {
                epoch::Decision::Unknown(limit) => return Err(Failure::Unknown(Limit { stage,
                    kind: LimitKind::Epoch(limit.kind), population: Some(limit.population),
                    required: limit.required, cap: limit.cap })),
                epoch::Decision::Table(table) => table,
            };
            let expected = (0..source.edges.len()).map(Location::Edge)
                .chain(std::iter::once(Location::Ancestral(source.root))).collect::<Vec<_>>();
            if table.variables != expected { return Err(Error::Internal("SOURCE_WORD_EPOCH_BANK").into()); }
            let base = multiply(slot, populations)?;
            (table.transitions, (0..populations).map(|offset| add(base, offset)).collect::<Result<Vec<_>, _>>()?)
        }
        Step::Boundary(action) => {
            let result = boundary::boundary_row(&request.context, snapshot, action, request.provider_limits.boundary)
                .map_err(|error| match error {
                    boundary::Error::InvalidInput(reason) | boundary::Error::Internal(reason) => Error::Internal(reason),
                })?;
            let table = match result {
                boundary::Decision::Unknown(limit) => return Err(Failure::Unknown(Limit { stage,
                    kind: LimitKind::Boundary(limit.kind), population: None,
                    required: limit.required, cap: limit.cap })),
                boundary::Decision::Table(table) => table,
            };
            if table.variables != (0..source.hybrids.len()).collect::<Vec<_>>() {
                return Err(Error::Internal("SOURCE_WORD_GAMMA_BANK").into());
            }
            let base = dimension.checked_sub(source.hybrids.len()).ok_or(Error::Internal("SOURCE_WORD_BANK"))?;
            (table.transitions, (0..source.hybrids.len()).map(|offset| add(base, offset)).collect::<Result<Vec<_>, _>>()?)
        }
        Step::Completion => {
            let result = completion::completion_row(&request.context, snapshot, request.provider_limits.completion)
                .map_err(|error| match error {
                    completion::Error::InvalidInput(reason) | completion::Error::Internal(reason) => Error::Internal(reason),
                })?;
            let table = match result {
                completion::Decision::Unknown(limit) => return Err(Failure::Unknown(Limit { stage,
                    kind: LimitKind::Completion(limit.kind), population: Some(Location::Ancestral(source.root)),
                    required: limit.required, cap: limit.cap })),
                completion::Decision::Table(table) => table,
            };
            if table.population != Location::Ancestral(source.root) {
                return Err(Error::Internal("SOURCE_WORD_COMPLETION_BANK").into());
            }
            let transitions = table.transitions.into_iter().map(|transition| Transition {
                view: transition.view, witness: transition.witness,
                polynomial: Polynomial::one(dimension).scale(&transition.weight),
            }).collect::<Vec<_>>();
            // Constants already inhabit the same complete word bank. No survival
            // coordinate, gamma alias or register draw is introduced here.
            (transitions, (0..dimension).collect())
        }
    };
    let mut row = Row::new();
    for transition in transitions {
        if transition.witness.register != snapshot.register || transition.view.register != snapshot.register {
            return Err(Error::Internal("SOURCE_WORD_REGISTER_PRESERVATION").into());
        }
        accumulate(&request.context, &mut row, Transition { polynomial: embed(&transition.polynomial, dimension, &map)?,
            view: transition.view, witness: transition.witness })?;
    }
    let mass = row.values().try_fold(Polynomial::zero(dimension), |sum, transition|
        sum.add(&transition.polynomial).map_err(Error::Internal))?;
    if mass != Polynomial::one(dimension) { return Err(Error::Internal("SOURCE_WORD_PROVIDER_MASS").into()); }
    Ok(row.into_values().collect())
}

fn compose(request: &Request, variables: Vec<Variable>, steps: Vec<Step>) -> Result<Table, Failure> {
    let dimension = variables.len();
    let mut work = Work::default();
    let mut current = initial_rows(request, dimension, &mut work)?;
    let mut stages = steps.into_iter().enumerate().map(|(letter, step)| (Stage::Letter(letter), step)).collect::<Vec<_>>();
    if request.terminal == Terminal::AncestralComplete { stages.push((Stage::Completion, Step::Completion)); }
    for (stage, step) in stages {
        if matches!(step, Step::Completion) {
            // Inspect every formal nonzero entering row before any completion
            // resource check. Parameter-specific zero values cannot omit rows.
            for entering in current.values() {
                let view = completion::validate_root_support(&request.context, &entering.witness)
                    .map_err(|error| match error {
                        completion::Error::InvalidInput(reason) => Error::InvalidInput(reason),
                        completion::Error::Internal(reason) => Error::Internal(reason),
                    })?;
                if view != entering.view { return Err(Error::Internal("SOURCE_WORD_RANGE_WITNESS").into()); }
            }
        }
        let queries = add(work.queries, current.len())?;
        check(stage, LimitKind::Queries, queries, request.limits.queries)?;
        let mut conditional = Vec::with_capacity(current.len());
        let mut branches = work.branches;
        let mut products = work.term_products;
        for entering in current.values() {
            let destinations = provider_row(request, &entering.witness, step, stage, dimension)?;
            branches = add(branches, destinations.len())?;
            let outgoing_terms = destinations.iter().try_fold(0, |sum, destination|
                add(sum, destination.polynomial.terms.len()))?;
            products = add(products, multiply(entering.polynomial.terms.len(), outgoing_terms)?)?;
            conditional.push(destinations);
        }
        check(stage, LimitKind::Branches, branches, request.limits.branches)?;
        check(stage, LimitKind::TermProducts, products, request.limits.term_products)?;
        let mut next = Row::new();
        for (entering, destinations) in current.values().zip(conditional) {
            for destination in destinations {
                let polynomial = entering.polynomial.multiply(&destination.polynomial).map_err(Error::Internal)?;
                accumulate(&request.context, &mut next, Transition { polynomial,
                    view: destination.view, witness: destination.witness })?;
            }
        }
        stage_check(&next, stage, request.limits, &mut work)?;
        work.queries = queries;
        work.branches = branches;
        work.term_products = products;
        current = next;
    }
    let mass = current.values().try_fold(Polynomial::zero(dimension), |sum, transition|
        sum.add(&transition.polynomial).map_err(Error::Internal))?;
    if mass != Polynomial::one(dimension) { return Err(Error::Internal("SOURCE_WORD_MASS_IDENTITY").into()); }
    Ok(Table { variables, transitions: current.into_values().collect(), work })
}

/// Full ordered finite endpoint law of a supplied original-ID word.
/// Input validation precedes limits. UNKNOWN carries no partial table.
/// Ancestral completion requires actual root support and introduces no variable.
pub fn word_row(request: &Request) -> Result<Decision, Error> {
    let (variables, steps) = validate(request)?;
    match compose(request, variables, steps) {
        Ok(table) => Ok(Decision::Table(table)),
        Err(Failure::Unknown(limit)) => Ok(Decision::Unknown(limit)),
        Err(Failure::Error(error)) => Err(error),
    }
}
