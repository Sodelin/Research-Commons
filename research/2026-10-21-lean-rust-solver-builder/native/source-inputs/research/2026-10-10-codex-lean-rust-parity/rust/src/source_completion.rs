//! Exact rational ancestral completion on the full ordered source carrier.
//!
//! The inherited actual_completion_rational theorem justifies the constant
//! coefficient through the positive-rate infinite-time limit. This private
//! consumer extracts that coefficient from the unchanged literal population
//! recurrence and sums complete selected fibres. Native typed correspondence
//! remains a separate obligation; no public endpoint or admission is added.
use crate::{q, Rational, source_epoch::{self as epoch, SelectedView},
    source_population::{self as population, Context, Location, Snapshot}};
use num_traits::Zero;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition { pub view: SelectedView, pub witness: Snapshot, pub weight: Rational }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    pub population: Location,
    pub transitions: Vec<Transition>,
    /// Observed work of the complete polynomial provider before extraction.
    pub work: population::Work,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision { Table(Table), Unknown(population::Limit) }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error { InvalidInput(&'static str), Internal(&'static str) }

/// Inspect the entire copied carrier, including carried ancestry fibres.
/// This check precedes every completion budget, even a zero query allowance.
pub fn validate_root_support(context: &Context, snapshot: &Snapshot) -> Result<SelectedView, Error> {
    context.validate_snapshot(snapshot).map_err(Error::InvalidInput)?;
    if context.sample.is_empty() {
        return Err(Error::InvalidInput("SOURCE_WORD_COMPLETION_EMPTY_COPY"));
    }
    let root = Some(Location::Ancestral(context.source.root));
    let view = epoch::selected_view(context, snapshot).map_err(Error::InvalidInput)?;
    if view.population.iter().any(|place| *place != root)
        || snapshot.live.iter().any(|owner| snapshot.population[*owner] != root)
        || snapshot.ancestor.iter().any(|owner| snapshot.population[*owner] != root) {
        return Err(Error::InvalidInput("SOURCE_WORD_COMPLETION_ROOT_SUPPORT"));
    }
    Ok(view)
}

/// Full selected rational row of the actual ancestral completion consumer.
/// Original ordered destinations are summed; UNKNOWN contains no partial row.
pub fn completion_row(context: &Context, snapshot: &Snapshot, limits: population::Limits)
    -> Result<Decision, Error> {
    validate_root_support(context, snapshot)?;
    let root = Location::Ancestral(context.source.root);
    let result = population::population_row(context, snapshot, root, limits).map_err(Error::Internal)?;
    let table = match result {
        population::Decision::Unknown(limit) => return Ok(Decision::Unknown(limit)),
        population::Decision::Table(table) => table,
    };
    if table.population != root { return Err(Error::Internal("SOURCE_COMPLETION_POPULATION")); }
    let mut row: BTreeMap<String, Transition> = BTreeMap::new();
    for literal in table.transitions {
        if literal.polynomial.dimension != 1 || literal.polynomial.terms.iter().any(|(powers, coefficient)|
            powers.len() != 1 || coefficient.is_zero()) {
            return Err(Error::Internal("SOURCE_COMPLETION_PROVIDER_POLYNOMIAL"));
        }
        let weight = literal.polynomial.terms.get(&vec![0]).cloned().unwrap_or_else(|| q(0, 1));
        if weight < q(0, 1) { return Err(Error::Internal("SOURCE_COMPLETION_NEGATIVE_WEIGHT")); }
        if weight.is_zero() { continue; }
        let witness = literal.destination;
        let view = validate_root_support(context, &witness).map_err(|error| match error {
            Error::InvalidInput(reason) | Error::Internal(reason) => Error::Internal(reason),
        })?;
        if witness.live.len() != 1 || witness.ancestor.iter().any(|owner| *owner != witness.live[0]) {
            return Err(Error::Internal("SOURCE_COMPLETION_INCOMPLETE_GENEALOGY"));
        }
        if witness.register != snapshot.register || view.register != snapshot.register {
            return Err(Error::Internal("SOURCE_COMPLETION_REGISTER_PRESERVATION"));
        }
        let key = epoch::selected_key(&view);
        if let Some(old) = row.get_mut(&key) {
            old.weight += weight;
            if population::snapshot_key(&witness) < population::snapshot_key(&old.witness) {
                old.witness = witness;
            }
        } else { row.insert(key, Transition { view, witness, weight }); }
    }
    let mass = row.values().fold(q(0, 1), |sum, transition| sum + &transition.weight);
    if mass != q(1, 1) { return Err(Error::Internal("SOURCE_COMPLETION_MASS_IDENTITY")); }
    Ok(Decision::Table(Table { population: root, transitions: row.into_values().collect(), work: table.work }))
}
