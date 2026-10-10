//! Internal original-source full epoch, retaining ordered per-copy views.
//!
//! This consumer restricts whole ancestor-closed original population panels,
//! executes the literal source_population recurrence, and glues their supported
//! outputs. Every view retains a validated canonical snapshot range witness.
//! The bank is original edges followed by ancestral, without hybrid variables.
//! No public RC1 operation or biological source-admission claim is added.
use crate::{forest::{Forest, Tree}, polynomial::Polynomial, q,
    source_population::{self as population, Context, Location, Snapshot}};
use std::collections::{BTreeMap, BTreeSet};

/// Exact full selected view. Every entry is Some on the full Copy carrier;
/// representatives and ancestry are omitted, while ordered trees remain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectedView {
    pub genealogy: Vec<Option<Tree>>,
    pub population: Vec<Option<Location>>,
    pub register: Vec<bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub calls: usize,
    pub destinations: usize,
    pub lifted_terms: usize,
    pub branches: usize,
    pub term_products: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self { calls: 4096, destinations: 4096, lifted_terms: 65536,
            branches: 4096, term_products: 65536 }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitKind { Calls, Destinations, LiftedTerms, Branches, TermProducts }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limit {
    pub kind: LimitKind,
    pub population: Location,
    pub required: usize,
    pub cap: usize,
}
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Work {
    pub calls: usize,
    pub lifted_terms: usize,
    pub largest_panel_row: usize,
    pub branches: usize,
    pub term_products: usize,
    pub largest_row: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition {
    pub view: SelectedView,
    pub witness: Snapshot,
    pub polynomial: Polynomial,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PanelSummary {
    pub population: Location,
    /// Original outer Copy IDs, in ascending order; never just current roots.
    pub copies: Vec<usize>,
    pub literal_destinations: usize,
    pub selected_destinations: usize,
    pub calls: usize,
    pub lifted_terms: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    pub variables: Vec<Location>,
    /// Ascending selected_key order, with a literal range witness per key.
    pub transitions: Vec<Transition>,
    pub panels: Vec<PanelSummary>,
    pub work: Work,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision { Table(Table), Unknown(Limit) }

#[derive(Debug)]
enum Failure { Limit(Limit), Invalid(&'static str) }
impl From<&'static str> for Failure {
    fn from(error: &'static str) -> Self { Self::Invalid(error) }
}
type Row = BTreeMap<String, Transition>;

pub fn selected_key(view: &SelectedView) -> String {
    let trees = view.genealogy.iter().map(|tree| tree.as_ref()
        .map(population::tree_string).unwrap_or_else(|| "-".into()))
        .collect::<Vec<_>>().join(";");
    let places = view.population.iter().map(|place| place.map(population::location_string)
        .unwrap_or_else(|| "-".into())).collect::<Vec<_>>().join(";");
    let register: String = view.register.iter().map(|bit| if *bit { '1' } else { '0' }).collect();
    format!("GENEALOGY[{trees}]POPULATION[{places}]REGISTER[{register}]")
}

/// The ancestor's complete ordered genealogy and location for every copy.
/// Full-carrier pruning is identity under the checked forest leaf invariant.
pub fn selected_view(context: &Context, snapshot: &Snapshot)
    -> Result<SelectedView, &'static str> {
    context.validate_snapshot(snapshot)?;
    Ok(SelectedView {
        genealogy: snapshot.ancestor.iter().map(|a| snapshot.genealogy[*a].clone()).collect(),
        population: snapshot.ancestor.iter().map(|a| snapshot.population[*a]).collect(),
        register: snapshot.register.clone(),
    })
}

fn remap_tree(tree: &Tree, labels: &[Option<usize>]) -> Result<Tree, &'static str> {
    match tree {
        Tree::Leaf(copy) => Ok(Tree::Leaf(*labels.get(*copy).ok_or("SOURCE_EPOCH_LABEL_MAP")?
            .as_ref().ok_or("SOURCE_EPOCH_PANEL_NOT_CLOSED")?)),
        Tree::Node(left, right) => Ok(Tree::Node(Box::new(remap_tree(left, labels)?),
            Box::new(remap_tree(right, labels)?))),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RestrictedPanel {
    pub copies: Vec<usize>,
    pub context: Context,
    pub start: Snapshot,
    pub population: Location,
}

/// Restrict the entire leaf fibre of each current lineage in one population.
/// An explicit bijection renames outer Copy IDs to 0..panel cardinality-1.
pub fn restrict_panel(context: &Context, snapshot: &Snapshot, place: Location)
    -> Result<RestrictedPanel, &'static str> {
    context.validate_snapshot(snapshot)?;
    let valid_place = match place {
        Location::Edge(edge) => edge < context.source.edges.len(),
        Location::Ancestral(root) => root == context.source.root,
        Location::Node(_) => false,
    };
    if !valid_place { return Err("SOURCE_EPOCH_POPULATION"); }
    let copies = (0..context.sample.len()).filter(|copy|
        snapshot.population[snapshot.ancestor[*copy]] == Some(place)).collect::<Vec<_>>();
    let mut outer_to_local = vec![None; context.sample.len()];
    for (local, outer) in copies.iter().enumerate() { outer_to_local[*outer] = Some(local); }
    let restricted_context = Context { source: context.source.clone(),
        sample: copies.iter().map(|copy| context.sample[*copy]).collect(),
        global_labels: copies.iter().map(|copy| context.global_labels[*copy]).collect() };
    let live = snapshot.live.iter().filter_map(|copy| outer_to_local[*copy]).collect();
    let ancestor = copies.iter().map(|copy| outer_to_local[snapshot.ancestor[*copy]]
        .ok_or("SOURCE_EPOCH_PANEL_NOT_CLOSED")).collect::<Result<Vec<_>, _>>()?;
    let genealogy = copies.iter().map(|copy| snapshot.genealogy[*copy].as_ref()
        .map(|tree| remap_tree(tree, &outer_to_local)).transpose())
        .collect::<Result<Vec<_>, _>>()?;
    let start = Snapshot { live, ancestor, genealogy,
        population: copies.iter().map(|copy| snapshot.population[*copy]).collect(),
        register: snapshot.register.clone() };
    restricted_context.validate_snapshot(&start)?;
    Ok(RestrictedPanel { copies, context: restricted_context, start, population: place })
}

/// Construct a canonical outer snapshot from a supported panel destination.
/// Untouched panels remain exactly as they were in the supplied outer state.
pub fn join_panel(context: &Context, outer: &Snapshot, panel: &RestrictedPanel,
    destination: &Snapshot) -> Result<Snapshot, &'static str> {
    context.validate_snapshot(outer)?;
    panel.context.validate_snapshot(destination)?;
    if panel.context.source != context.source || panel.copies.len() != panel.context.sample.len()
        || panel.copies.windows(2).any(|pair| pair[0] >= pair[1])
        || panel.copies.iter().any(|copy| *copy >= context.sample.len())
        || destination.register != outer.register
        || panel.context.sample != panel.copies.iter().map(|copy| context.sample[*copy]).collect::<Vec<_>>()
        || panel.context.global_labels != panel.copies.iter().map(|copy| context.global_labels[*copy]).collect::<Vec<_>>() {
        return Err("SOURCE_EPOCH_PANEL_CONTEXT");
    }
    let expected = restrict_panel(context, outer, panel.population)?;
    if expected.copies != panel.copies
        || destination.live.iter().any(|copy| destination.population[*copy] != Some(panel.population)) {
        return Err("SOURCE_EPOCH_PANEL_NOT_CLOSED");
    }
    let labels = panel.copies.iter().copied().map(Some).collect::<Vec<_>>();
    let copy_set = panel.copies.iter().copied().collect::<BTreeSet<_>>();
    let mut result = outer.clone();
    result.live.retain(|copy| !copy_set.contains(copy));
    result.live.extend(destination.live.iter().map(|copy| panel.copies[*copy]));
    result.live.sort_unstable();
    for (local, outer_copy) in panel.copies.iter().enumerate() {
        result.ancestor[*outer_copy] = panel.copies[destination.ancestor[local]];
        result.genealogy[*outer_copy] = destination.genealogy[local].as_ref()
            .map(|tree| remap_tree(tree, &labels)).transpose()?;
        result.population[*outer_copy] = destination.population[local];
    }
    context.validate_snapshot(&result)?;
    let mut expected_view = selected_view(context, outer)?;
    let local_view = selected_view(&panel.context, destination)?;
    for (local, outer_copy) in panel.copies.iter().enumerate() {
        expected_view.genealogy[*outer_copy] = local_view.genealogy[local].as_ref()
            .map(|tree| remap_tree(tree, &labels)).transpose()?;
        expected_view.population[*outer_copy] = local_view.population[local];
    }
    if selected_view(context, &result)? != expected_view {
        return Err("SOURCE_EPOCH_RANGE_WITNESS");
    }
    Ok(result)
}

fn accumulate(row: &mut Row, transition: Transition) -> Result<(), &'static str> {
    if transition.polynomial.is_zero() { return Ok(()); }
    let key = selected_key(&transition.view);
    let polynomial = match row.get(&key) {
        Some(old) => old.polynomial.add(&transition.polynomial)?,
        None => transition.polynomial.clone(),
    };
    if polynomial.is_zero() { row.remove(&key); return Ok(()); }
    let witness = match row.get(&key) {
        Some(old) if population::snapshot_key(&old.witness) < population::snapshot_key(&transition.witness)
            => old.witness.clone(),
        _ => transition.witness,
    };
    row.insert(key, Transition { view: transition.view, witness, polynomial });
    Ok(())
}
fn embed(polynomial: &Polynomial, dimension: usize, variable: usize)
    -> Result<Polynomial, &'static str> {
    if polynomial.dimension != 1 || polynomial.terms.keys().any(|powers| powers.len() != 1) {
        return Err("SOURCE_EPOCH_KERNEL_DIMENSION");
    }
    polynomial.terms.iter().try_fold(Polynomial::zero(dimension), |sum, (powers, coefficient)|
        sum.add(&Polynomial::monomial(dimension, variable, powers[0], coefficient.clone())?))
}
fn check(kind: LimitKind, population: Location, required: usize, cap: usize)
    -> Result<(), Failure> {
    if required > cap { Err(Failure::Limit(Limit { kind, population, required, cap })) }
    else { Ok(()) }
}
fn sum_terms(row: &Row) -> Result<usize, &'static str> {
    row.values().try_fold(0usize, |sum, transition| sum.checked_add(transition.polynomial.terms.len())
        .ok_or("SOURCE_EPOCH_WORK_OVERFLOW"))
}

fn full_row(context: &Context, snapshot: &Snapshot, limits: Limits)
    -> Result<Table, Failure> {
    context.validate_snapshot(snapshot)?;
    let dimension = context.source.edges.len().checked_add(1).ok_or("SOURCE_EPOCH_BANK")?;
    if dimension > 32 { return Err(Failure::Invalid("SOURCE_EPOCH_BANK")); }
    let variables = (0..context.source.edges.len()).map(Location::Edge)
        .chain(std::iter::once(Location::Ancestral(context.source.root))).collect::<Vec<_>>();
    let entering_view = selected_view(context, snapshot)?;
    let mut current = Row::new();
    accumulate(&mut current, Transition { view: entering_view.clone(), witness: snapshot.clone(),
        polynomial: Polynomial::one(dimension) })?;
    let mut work = Work { largest_row: 1, ..Work::default() };
    let mut summaries = vec![];
    for (variable, place) in variables.iter().copied().enumerate() {
        let panel = restrict_panel(context, snapshot, place)?;
        let panel_limits = population::Limits {
            calls: limits.calls.saturating_sub(work.calls),
            destinations: limits.destinations,
            lifted_terms: limits.lifted_terms.saturating_sub(work.lifted_terms),
        };
        let literal = match population::population_row(&panel.context, &panel.start, place, panel_limits)? {
            population::Decision::Table(table) => table,
            population::Decision::Unknown(limit) => {
                let (kind, prior, cap) = match limit.kind {
                    population::LimitKind::Calls => (LimitKind::Calls, work.calls, limits.calls),
                    population::LimitKind::Destinations => (LimitKind::Destinations, 0, limits.destinations),
                    population::LimitKind::LiftedTerms => (LimitKind::LiftedTerms, work.lifted_terms, limits.lifted_terms),
                };
                return Err(Failure::Limit(Limit { kind, population: place,
                    required: prior.checked_add(limit.required).ok_or("SOURCE_EPOCH_WORK_OVERFLOW")?, cap }));
            }
        };
        work.calls = work.calls.checked_add(literal.work.calls).ok_or("SOURCE_EPOCH_WORK_OVERFLOW")?;
        work.lifted_terms = work.lifted_terms.checked_add(literal.work.lifted_terms)
            .ok_or("SOURCE_EPOCH_WORK_OVERFLOW")?;
        work.largest_panel_row = work.largest_panel_row.max(literal.work.largest_row);
        let mut selected_panel = Row::new();
        for transition in &literal.transitions {
            accumulate(&mut selected_panel, Transition {
                view: selected_view(&panel.context, &transition.destination)?,
                witness: transition.destination.clone(),
                polynomial: embed(&transition.polynomial, dimension, variable)?,
            })?;
        }
        let branch_count = current.len().checked_mul(selected_panel.len()).ok_or("SOURCE_EPOCH_WORK_OVERFLOW")?;
        let required_branches = work.branches.checked_add(branch_count).ok_or("SOURCE_EPOCH_WORK_OVERFLOW")?;
        check(LimitKind::Branches, place, required_branches, limits.branches)?;
        let term_count = sum_terms(&current)?.checked_mul(sum_terms(&selected_panel)?)
            .ok_or("SOURCE_EPOCH_WORK_OVERFLOW")?;
        let required_terms = work.term_products.checked_add(term_count).ok_or("SOURCE_EPOCH_WORK_OVERFLOW")?;
        check(LimitKind::TermProducts, place, required_terms, limits.term_products)?;
        work.branches = required_branches;
        work.term_products = required_terms;
        let mut next = Row::new();
        for outer in current.values() { for inner in selected_panel.values() {
            let witness = join_panel(context, &outer.witness, &panel, &inner.witness)?;
            let view = selected_view(context, &witness)?;
            let polynomial = outer.polynomial.multiply(&inner.polynomial)?;
            accumulate(&mut next, Transition { view, witness, polynomial })?;
        } }
        work.largest_row = work.largest_row.max(next.len());
        summaries.push(PanelSummary { population: place, copies: panel.copies,
            literal_destinations: literal.transitions.len(), selected_destinations: selected_panel.len(),
            calls: literal.work.calls, lifted_terms: literal.work.lifted_terms });
        current = next;
    }
    let sum = current.values().try_fold(Polynomial::zero(dimension),
        |sum, transition| sum.add(&transition.polynomial))?;
    if sum != Polynomial::one(dimension) { return Err(Failure::Invalid("SOURCE_EPOCH_ROW_NOT_NORMALIZED")); }
    let identity = vec![q(1, 1); dimension];
    for transition in current.values() {
        if selected_view(context, &transition.witness)? != transition.view
            || transition.witness.register != snapshot.register {
            return Err(Failure::Invalid("SOURCE_EPOCH_RANGE_WITNESS"));
        }
        if transition.polynomial.evaluate(&identity)? != q(i64::from(transition.view == entering_view), 1) {
            return Err(Failure::Invalid("SOURCE_EPOCH_ZERO_TIME"));
        }
    }
    Ok(Table { variables, transitions: current.into_values().collect(), panels: summaries, work })
}

/// Exact normalized supported full selected-view row. A limit returns no table.
/// Physical evaluation is X_i=exp(-pairRate(r,i)*t) for one shared epoch time.
pub fn epoch_row(context: &Context, snapshot: &Snapshot, limits: Limits)
    -> Result<Decision, &'static str> {
    match full_row(context, snapshot, limits) {
        Ok(table) => Ok(Decision::Table(table)),
        Err(Failure::Limit(limit)) => Ok(Decision::Unknown(limit)),
        Err(Failure::Invalid(error)) => Err(error),
    }
}

/// Separately declared readout forgetting ordered children, representatives,
/// populations and register. The full Table above keeps the original metadata.
pub fn unordered_pushforward(context: &Context, table: &Table)
    -> Result<BTreeMap<String, (Forest, Polynomial)>, &'static str> {
    let mut result: BTreeMap<String, (Forest, Polynomial)> = BTreeMap::new();
    for transition in &table.transitions {
        if selected_view(context, &transition.witness)? != transition.view {
            return Err("SOURCE_EPOCH_RANGE_WITNESS");
        }
        let forest = population::unordered_forest(context, &transition.witness)?;
        let key = population::forest_key(&forest);
        let polynomial = match result.get(&key) {
            Some((_, old)) => old.add(&transition.polynomial)?,
            None => transition.polynomial.clone(),
        };
        if polynomial.is_zero() { result.remove(&key); }
        else { result.insert(key, (forest, polynomial)); }
    }
    Ok(result)
}
