//! Conditional original-source boundary rows on the canonical encoded carrier.
//!
//! This port follows SourceBoundaryKernels.boundaryKernel and
//! G7OriginalBoundaryPolynomial.nodePolynomial. The entering register is fixed;
//! COMMON is deterministic and INDEPENDENT draws one coin per current owner.
//! Original gamma is P(true/parent1), unlike the complemented LAW-v1 bank.
//! Every ordered selected row retains a validated literal range witness.
//! No public operation, scientific admission or general refinement is claimed.
use crate::{polynomial::Polynomial, q, source_epoch::{self as epoch, Transition},
    source_population::{self as population, Context, Location, Snapshot}};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Action { Exit(usize), Ordinary(usize), Root, Common(usize), Independent(usize) }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub assignments: usize,
    pub destinations: usize,
    pub term_contributions: usize,
}
impl Default for Limits {
    fn default() -> Self { Self { assignments: 16, destinations: 16, term_contributions: 128 } }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitKind { Assignments, Destinations, TermContributions }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limit { pub kind: LimitKind, pub required: usize, pub cap: usize }
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Work {
    pub owners: usize,
    pub assignments: usize,
    pub destinations: usize,
    pub term_contributions: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    /// Original hybrid IDs, ascending; each coordinate is P(true/parent1).
    pub variables: Vec<usize>,
    /// Complete ordered selected keys in ascending epoch::selected_key order.
    pub transitions: Vec<Transition>,
    pub work: Work,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision { Table(Table), Unknown(Limit) }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error { InvalidInput(&'static str), Internal(&'static str) }

#[derive(Clone, Copy)]
enum Routing {
    Deterministic { at: Location, to: Location },
    Coin { at: Location, parents: [usize; 2], variable: usize, common_bit: Option<bool> },
}
impl Routing {
    fn at(self) -> Location { match self {
        Self::Deterministic { at, .. } | Self::Coin { at, .. } => at,
    } }
    fn independent(self) -> bool { matches!(self, Self::Coin { common_bit: None, .. }) }
}

fn resolve(context: &Context, snapshot: &Snapshot, action: Action) -> Result<Routing, Error> {
    match action {
        Action::Exit(edge) => {
            let original = context.source.edges.get(edge).ok_or(Error::InvalidInput("SOURCE_BOUNDARY_EDGE"))?;
            Ok(Routing::Deterministic { at: Location::Edge(edge), to: Location::Node(original.source) })
        }
        Action::Ordinary(edge) => {
            let original = context.source.edges.get(edge).ok_or(Error::InvalidInput("SOURCE_BOUNDARY_EDGE"))?;
            if context.source.edges.iter().filter(|candidate| candidate.target == original.target).count() != 1 {
                return Err(Error::InvalidInput("SOURCE_BOUNDARY_ORDINARY_DEGREE"));
            }
            Ok(Routing::Deterministic { at: Location::Node(original.target), to: Location::Edge(edge) })
        }
        Action::Root => Ok(Routing::Deterministic { at: Location::Node(context.source.root),
            to: Location::Ancestral(context.source.root) }),
        Action::Common(variable) | Action::Independent(variable) => {
            // Context validation authenticates the complete original registry:
            // distinct genuine occurrences, common target and binary degrees.
            let hybrid = context.source.hybrids.get(variable).ok_or(Error::InvalidInput("SOURCE_BOUNDARY_HYBRID"))?;
            let common_bit = if matches!(action, Action::Common(_)) { Some(snapshot.register[hybrid.vertex]) }
                else { None };
            Ok(Routing::Coin { at: Location::Node(hybrid.vertex), parents: hybrid.incoming, variable, common_bit })
        }
    }
}

fn check(kind: LimitKind, required: usize, cap: usize) -> Option<Limit> {
    (required > cap).then_some(Limit { kind, required, cap })
}

fn binomial(n: usize, k: usize) -> usize {
    // The validated carrier has at most four copies, hence n <= 4.
    (0..k).fold(1, |value, i| value * (n - i) / (i + 1))
}
fn assignment_polynomial(dimension: usize, variable: usize, owners: usize, mask: usize)
    -> Result<Polynomial, Error> {
    let trues = mask.count_ones() as usize;
    let falses = owners.checked_sub(trues).ok_or(Error::Internal("SOURCE_BOUNDARY_ASSIGNMENT"))?;
    (0..=falses).try_fold(Polynomial::zero(dimension), |sum, extra| {
        let coefficient = binomial(falses, extra) as i64 * if extra % 2 == 0 { 1 } else { -1 };
        let term = Polynomial::monomial(dimension, variable, trues + extra, q(coefficient, 1))
            .map_err(Error::Internal)?;
        sum.add(&term).map_err(Error::Internal)
    })
}

fn accumulate(row: &mut BTreeMap<String, Transition>, transition: Transition) -> Result<(), Error> {
    let key = epoch::selected_key(&transition.view);
    if let Some(old) = row.get(&key) {
        let polynomial = old.polynomial.add(&transition.polynomial).map_err(Error::Internal)?;
        let witness = if population::snapshot_key(&old.witness) < population::snapshot_key(&transition.witness) {
            old.witness.clone()
        } else { transition.witness };
        if polynomial.is_zero() { row.remove(&key); }
        else { row.insert(key, Transition { view: transition.view, witness, polynomial }); }
    } else if !transition.polynomial.is_zero() { row.insert(key, transition); }
    Ok(())
}

/// One exact conditional row of an original finite boundary action.
/// Invalid inputs are rejected before limits; resource refusal has no table.
/// All three requirements are checked before coin/monomial generation.
pub fn boundary_row(context: &Context, snapshot: &Snapshot, action: Action, limits: Limits)
    -> Result<Decision, Error> {
    context.validate_snapshot(snapshot).map_err(Error::InvalidInput)?;
    let routing = resolve(context, snapshot, action)?;
    let owners = snapshot.live.iter().copied().filter(|owner| snapshot.population[*owner] == Some(routing.at()))
        .collect::<Vec<_>>();
    let assignments = if routing.independent() { 1usize << owners.len() } else { 1 };
    let terms = if routing.independent() && !owners.is_empty() { assignments + owners.len() * (assignments / 2) }
        else { 1 };
    for (kind, required, cap) in [(LimitKind::Assignments, assignments, limits.assignments),
        (LimitKind::Destinations, assignments, limits.destinations),
        (LimitKind::TermContributions, terms, limits.term_contributions)] {
        if let Some(limit) = check(kind, required, cap) { return Ok(Decision::Unknown(limit)); }
    }
    let dimension = context.source.hybrids.len();
    let mut row = BTreeMap::new();
    let mut observed_terms = 0usize;
    for mask in 0..assignments {
        let mut destination = snapshot.clone();
        for (index, owner) in owners.iter().enumerate() {
            let place = match routing {
                Routing::Deterministic { to, .. } => to,
                Routing::Coin { parents, common_bit, .. } => {
                    // Lexicographic assignments: first owner is the high bit.
                    let bit = common_bit.unwrap_or_else(|| mask & (1 << (owners.len() - index - 1)) != 0);
                    Location::Edge(parents[usize::from(bit)])
                }
            };
            destination.population[*owner] = Some(place);
        }
        if destination.live != snapshot.live || destination.ancestor != snapshot.ancestor
            || destination.genealogy != snapshot.genealogy || destination.register != snapshot.register {
            return Err(Error::Internal("SOURCE_BOUNDARY_PRESERVATION"));
        }
        context.validate_snapshot(&destination).map_err(Error::Internal)?;
        let polynomial = match routing {
            Routing::Coin { variable, common_bit: None, .. } =>
                assignment_polynomial(dimension, variable, owners.len(), mask)?,
            _ => Polynomial::one(dimension),
        };
        observed_terms += polynomial.terms.len();
        let view = epoch::selected_view(context, &destination).map_err(Error::Internal)?;
        accumulate(&mut row, Transition { view, witness: destination, polynomial })?;
    }
    if row.len() != assignments || observed_terms != terms
        || row.values().map(|transition| transition.polynomial.terms.len()).sum::<usize>() != terms {
        return Err(Error::Internal("SOURCE_BOUNDARY_WORK_IDENTITY"));
    }
    let total = row.values().try_fold(Polynomial::zero(dimension), |sum, transition|
        sum.add(&transition.polynomial).map_err(Error::Internal))?;
    if total != Polynomial::one(dimension) { return Err(Error::Internal("SOURCE_BOUNDARY_MASS_IDENTITY")); }
    Ok(Decision::Table(Table { variables: (0..dimension).collect(), transitions: row.into_values().collect(),
        work: Work { owners: owners.len(), assignments, destinations: assignments, term_contributions: terms } }))
}
