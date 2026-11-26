//! Literal ordered original-source population coefficient recurrence.
//!
//! This library port follows EffectivePopulationCoefficients.coefficients and
//! SinglePopulationPolynomialKernel.liftTerm. It retains live representatives,
//! ordered grafts, ancestry, original locations and the complete vertex register.
//! The input is the canonical live-only snapshot encoding on a restricted Copy
//! carrier. Reachable-row enumeration, the unordered quotient and the typed
//! source correspondence still need the separate Lean refinement obligations.
//! No public RC1 operation or scientific admission is added here.
use crate::{forest::{Forest, Tree}, natural_cell::Source, polynomial::Polynomial, q};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Location { Node(usize), Edge(usize), Ancestral(usize) }

/// Indices are local copies. The embedding preserves their global identities;
/// it need not be monotone. Every sample is an original declared taxon ID.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    pub source: Source,
    pub sample: Vec<usize>,
    pub global_labels: Vec<usize>,
}

/// Literal inherited Snapshot fields, with dead genealogy/population = none.
/// Ordered tree leaves and live representative IDs use the local Copy carrier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Snapshot {
    pub live: Vec<usize>,
    pub ancestor: Vec<usize>,
    pub genealogy: Vec<Option<Tree>>,
    pub population: Vec<Option<Location>>,
    pub register: Vec<bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits { pub calls: usize, pub destinations: usize, pub lifted_terms: usize }
impl Default for Limits {
    fn default() -> Self { Self { calls: 4096, destinations: 4096, lifted_terms: 65536 } }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitKind { Calls, Destinations, LiftedTerms }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limit { pub kind: LimitKind, pub required: usize, pub cap: usize }
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Work { pub calls: usize, pub lifted_terms: usize, pub largest_row: usize }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition { pub destination: Snapshot, pub polynomial: Polynomial }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    pub population: Location,
    /// Full literal ordered destination row in ascending snapshot_key order.
    pub transitions: Vec<Transition>,
    pub work: Work,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision { Table(Table), Unknown(Limit) }

#[derive(Debug)]
enum Failure { Limit(Limit), Invalid(&'static str) }
impl From<&'static str> for Failure { fn from(e: &'static str) -> Self { Self::Invalid(e) } }

pub fn tree_string(tree: &Tree) -> String { match tree {
    Tree::Leaf(i) => i.to_string(),
    Tree::Node(a, b) => format!("({},{})", tree_string(a), tree_string(b)),
} }
pub fn location_string(location: Location) -> String { match location {
    Location::Node(v) => format!("V:{v}"),
    Location::Edge(e) => format!("E:{e}"),
    Location::Ancestral(v) => format!("A:{v}"),
} }
fn numbers(values: &[usize]) -> String {
    values.iter().map(usize::to_string).collect::<Vec<_>>().join(",")
}
pub fn snapshot_key(snapshot: &Snapshot) -> String {
    let trees = snapshot.genealogy.iter().map(|t| t.as_ref().map(tree_string)
        .unwrap_or_else(|| "-".into())).collect::<Vec<_>>().join(";");
    let places = snapshot.population.iter().map(|p| p.map(location_string)
        .unwrap_or_else(|| "-".into())).collect::<Vec<_>>().join(";");
    let register: String = snapshot.register.iter().map(|b| if *b { '1' } else { '0' }).collect();
    format!("LIVE[{}]ANCESTOR[{}]GENEALOGY[{}]POPULATION[{}]REGISTER[{register}]",
        numbers(&snapshot.live), numbers(&snapshot.ancestor), trees, places)
}

/// Iterative scan rejects oversized/deep or repeated-label trees before any
/// recursive rendering or coefficient computation touches caller input.
fn leaves(tree: &Tree, copies: usize) -> Result<Vec<usize>, &'static str> {
    let mut stack = vec![tree];
    let mut labels = BTreeSet::new();
    let mut nodes = 0;
    while let Some(tree) = stack.pop() {
        nodes += 1;
        if nodes > copies.saturating_mul(2).saturating_sub(1) { return Err("SOURCE_TREE_SIZE"); }
        match tree {
            Tree::Leaf(i) => {
                if *i >= copies || !labels.insert(*i) { return Err("SOURCE_TREE_LABELS"); }
            }
            Tree::Node(a, b) => { stack.push(b); stack.push(a); }
        }
    }
    Ok(labels.into_iter().collect())
}

impl Context {
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.source.vertices > 32 || self.source.edges.len() > 32
            || self.source.leaves.len() > 32 || self.source.hybrids.len() > 32 || self.source.dimension() > 32
            || self.sample.len() > 4 || self.sample.len() != self.global_labels.len()
            || self.sample.iter().any(|x| *x >= self.source.leaves.len())
            || self.global_labels.iter().collect::<BTreeSet<_>>().len() != self.global_labels.len() {
            return Err("SOURCE_POPULATION_CONTEXT");
        }
        self.source.validate()
    }
    fn place_valid(&self, place: Location) -> bool { match place {
        Location::Node(v) => v < self.source.vertices,
        Location::Edge(e) => e < self.source.edges.len(),
        Location::Ancestral(v) => v == self.source.root,
    } }
    fn descends(&self, place: Location, taxon: usize) -> bool {
        let start = match place {
            Location::Node(v) | Location::Ancestral(v) => v,
            Location::Edge(e) => self.source.edges[e].target,
        };
        let target = self.source.leaves[taxon];
        let mut seen = vec![false; self.source.vertices];
        let mut stack = vec![start];
        seen[start] = true;
        while let Some(v) = stack.pop() {
            if v == target { return true; }
            for edge in &self.source.edges {
                if edge.source == v && !seen[edge.target] {
                    seen[edge.target] = true; stack.push(edge.target);
                }
            }
        }
        false
    }

    /// Checks the inherited forest invariant and original descendant predicate
    /// for this finite structural graph. It supplies no missing class admission.
    pub fn validate_snapshot(&self, snapshot: &Snapshot) -> Result<(), &'static str> {
        self.validate()?;
        let copies = self.sample.len();
        if snapshot.ancestor.len() != copies || snapshot.genealogy.len() != copies
            || snapshot.population.len() != copies || snapshot.register.len() != self.source.vertices
            || snapshot.live.windows(2).any(|w| w[0] >= w[1])
            || snapshot.live.iter().any(|i| *i >= copies) {
            return Err("SOURCE_SNAPSHOT_FIELDS");
        }
        let live: BTreeSet<_> = snapshot.live.iter().copied().collect();
        if snapshot.ancestor.iter().any(|a| !live.contains(a))
            || snapshot.live.iter().any(|a| snapshot.ancestor[*a] != *a) {
            return Err("SOURCE_ANCESTOR");
        }
        let mut seen = vec![false; copies];
        for i in 0..copies {
            if !live.contains(&i) {
                if snapshot.genealogy[i].is_some() || snapshot.population[i].is_some() {
                    return Err("SOURCE_CANONICAL_DEAD_FIELDS");
                }
                continue;
            }
            let tree = snapshot.genealogy[i].as_ref().ok_or("SOURCE_LIVE_GENEALOGY")?;
            let place = snapshot.population[i].ok_or("SOURCE_LIVE_POPULATION")?;
            if !self.place_valid(place) { return Err("SOURCE_LOCATION"); }
            let labels = leaves(tree, copies)?;
            for x in labels {
                if seen[x] || snapshot.ancestor[x] != i { return Err("SOURCE_LEAF_FIBER"); }
                seen[x] = true;
            }
        }
        if seen.iter().any(|b| !b) { return Err("SOURCE_LEAF_FIBER"); }
        for x in 0..copies {
            let place = snapshot.population[snapshot.ancestor[x]].ok_or("SOURCE_LIVE_POPULATION")?;
            if !self.descends(place, self.sample[x]) { return Err("SOURCE_DESCENDANT"); }
        }
        Ok(())
    }
}

impl Snapshot {
    pub fn from_lineages(context: &Context, lineages: &[(usize, Tree)],
        population: Location, register: Vec<bool>) -> Result<Self, &'static str> {
        context.validate()?;
        let copies = context.sample.len();
        let mut snapshot = Self { live: vec![], ancestor: vec![usize::MAX; copies],
            genealogy: vec![None; copies], population: vec![None; copies], register };
        for (representative, tree) in lineages {
            if *representative >= copies || snapshot.genealogy[*representative].is_some() {
                return Err("SOURCE_REPRESENTATIVE");
            }
            for x in leaves(tree, copies)? {
                if snapshot.ancestor[x] != usize::MAX { return Err("SOURCE_LEAF_FIBER"); }
                snapshot.ancestor[x] = *representative;
            }
            snapshot.live.push(*representative);
            snapshot.genealogy[*representative] = Some(tree.clone());
            snapshot.population[*representative] = Some(population);
        }
        snapshot.live.sort_unstable();
        context.validate_snapshot(&snapshot)?;
        Ok(snapshot)
    }

    /// Exact inherited merge followed by live-only encodeActual. Child order
    /// and the chosen survivor are retained; no quotient is taken here.
    pub fn merge(&self, context: &Context, a: usize, b: usize) -> Result<Self, &'static str> {
        context.validate_snapshot(self)?;
        if a == b || !self.live.contains(&a) || !self.live.contains(&b)
            || self.population[a] != self.population[b]
            || matches!(self.population[a], Some(Location::Node(_)) | None) {
            return Err("SOURCE_ILLEGAL_MERGER");
        }
        let result = self.merge_unchecked(a, b);
        context.validate_snapshot(&result)?;
        Ok(result)
    }
    fn merge_unchecked(&self, a: usize, b: usize) -> Self {
        let mut result = self.clone();
        result.live.retain(|i| *i != b);
        for ancestor in &mut result.ancestor { if *ancestor == b { *ancestor = a; } }
        result.genealogy[a] = Some(Tree::Node(Box::new(self.genealogy[a].as_ref().unwrap().clone()),
            Box::new(self.genealogy[b].as_ref().unwrap().clone())));
        result.genealogy[b] = None;
        result.population[b] = None;
        result
    }
}

type Row = BTreeMap<String, Transition>;
fn check(kind: LimitKind, required: usize, cap: usize) -> Result<(), Failure> {
    if required > cap { Err(Failure::Limit(Limit { kind, required, cap })) } else { Ok(()) }
}
fn accumulate(row: &mut Row, snapshot: Snapshot, polynomial: Polynomial, limits: Limits,
    work: &mut Work) -> Result<(), Failure> {
    if polynomial.is_zero() { return Ok(()); }
    let key = snapshot_key(&snapshot);
    let sum = match row.get(&key) {
        Some(old) => old.polynomial.add(&polynomial)?,
        None => {
            check(LimitKind::Destinations, row.len() + 1, limits.destinations)?;
            polynomial
        }
    };
    if sum.is_zero() { row.remove(&key); }
    else { row.insert(key, Transition { destination: snapshot, polynomial: sum }); }
    work.largest_row = work.largest_row.max(row.len());
    Ok(())
}
fn lift(holding: usize, polynomial: &Polynomial, limits: Limits, work: &mut Work)
    -> Result<Polynomial, Failure> {
    let required = work.lifted_terms.checked_add(2 * polynomial.terms.len())
        .ok_or("SOURCE_WORK_OVERFLOW")?;
    check(LimitKind::LiftedTerms, required, limits.lifted_terms)?;
    work.lifted_terms = required;
    let mut result = Polynomial::zero(1);
    for (powers, coefficient) in &polynomial.terms {
        let exponent = powers[0];
        if exponent >= holding { return Err(Failure::Invalid("SOURCE_DEGREE_DESCENT")); }
        let b = coefficient / q(2 * (holding - exponent) as i64, 1);
        result = result.add(&Polynomial::monomial(1, 0, exponent, b.clone())?)?
            .add(&Polynomial::monomial(1, 0, holding, -b)?)?;
    }
    Ok(result)
}
fn coefficients(fuel: usize, snapshot: &Snapshot, limits: Limits, work: &mut Work)
    -> Result<Row, Failure> {
    let required = work.calls.checked_add(1).ok_or("SOURCE_WORK_OVERFLOW")?;
    check(LimitKind::Calls, required, limits.calls)?;
    work.calls = required;
    let mut row = Row::new();
    if fuel == 0 || snapshot.live.len() <= 1 {
        accumulate(&mut row, snapshot.clone(), Polynomial::one(1), limits, work)?;
        return Ok(row);
    }
    let holding = snapshot.live.len() * (snapshot.live.len() - 1) / 2;
    accumulate(&mut row, snapshot.clone(), Polynomial::monomial(1, 0, holding, q(1, 1))?, limits, work)?;
    for &a in &snapshot.live { for &b in &snapshot.live {
        if a == b { continue; }
        let next = snapshot.merge_unchecked(a, b);
        for transition in coefficients(fuel - 1, &next, limits, work)?.into_values() {
            let polynomial = lift(holding, &transition.polynomial, limits, work)?;
            accumulate(&mut row, transition.destination, polynomial, limits, work)?;
        }
    } }
    Ok(row)
}

/// Executes the actual half-rate recurrence at fuel = card(local Copy).
/// Missing resource budget returns UNKNOWN with no partial transition row.
pub fn population_row(context: &Context, snapshot: &Snapshot, population: Location, limits: Limits)
    -> Result<Decision, &'static str> {
    context.validate_snapshot(snapshot)?;
    if !context.place_valid(population) || matches!(population, Location::Node(_))
        || snapshot.live.iter().any(|a| snapshot.population[*a] != Some(population)) {
        return Err("SOURCE_NOT_COLOCATED");
    }
    let mut work = Work::default();
    match coefficients(context.sample.len(), snapshot, limits, &mut work) {
        Ok(row) => {
            let sum = row.values().try_fold(Polynomial::zero(1),
                |sum, transition| sum.add(&transition.polynomial))?;
            if sum != Polynomial::one(1) { return Err("SOURCE_ROW_NOT_NORMALIZED"); }
            for transition in row.values() {
                context.validate_snapshot(&transition.destination)?;
                if transition.destination.register != snapshot.register
                    || transition.destination.live.iter().any(|a|
                        transition.destination.population[*a] != Some(population)) {
                    return Err("SOURCE_ROW_METADATA_CHANGED");
                }
            }
            Ok(Decision::Table(Table { population, transitions: row.into_values().collect(), work }))
        }
        Err(Failure::Limit(limit)) => Ok(Decision::Unknown(limit)),
        Err(Failure::Invalid(error)) => Err(error),
    }
}

fn canonical_tree(tree: &Tree, labels: &[usize]) -> (Tree, usize) { match tree {
    Tree::Leaf(i) => (Tree::Leaf(labels[*i]), labels[*i]),
    Tree::Node(a, b) => {
        let (a, first) = canonical_tree(a, labels);
        let (b, second) = canonical_tree(b, labels);
        if first < second { (Tree::Node(Box::new(a), Box::new(b)), first) }
        else { (Tree::Node(Box::new(b), Box::new(a)), second) }
    }
} }
pub fn unordered_forest(context: &Context, snapshot: &Snapshot) -> Result<Forest, &'static str> {
    context.validate_snapshot(snapshot)?;
    let mut forest = snapshot.live.iter().map(|a|
        canonical_tree(snapshot.genealogy[*a].as_ref().unwrap(), &context.global_labels))
        .collect::<Vec<_>>();
    forest.sort_by_key(|(_, least)| *least);
    Ok(forest.into_iter().map(|(tree, _)| tree).collect())
}
pub fn forest_key(forest: &Forest) -> String {
    format!("[{}]", forest.iter().map(tree_string).collect::<Vec<_>>().join(","))
}
/// The explicit fibre sum forgets representatives and ordered grafts. Original
/// population/register metadata remain in Table and in every literal row.
pub fn unordered_pushforward(context: &Context, table: &Table)
    -> Result<BTreeMap<String, (Forest, Polynomial)>, &'static str> {
    let mut result: BTreeMap<String, (Forest, Polynomial)> = BTreeMap::new();
    for transition in &table.transitions {
        let forest = unordered_forest(context, &transition.destination)?;
        let key = forest_key(&forest);
        let sum = match result.get(&key) { Some((_, old)) => old.add(&transition.polynomial)?,
            None => transition.polynomial.clone() };
        if sum.is_zero() { result.remove(&key); }
        else { result.insert(key, (forest, sum)); }
    }
    Ok(result)
}

#[cfg(test)]
mod refinement_tests {
    use super::*;
    use crate::natural_cell::Edge;

    #[test]
    fn all_literal_fibres_match_the_existing_law_edge_kernel() {
        let source = Source { vertices: 3, root: 0, edges: vec![Edge { source: 0, target: 1 },
            Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] };
        for copies in 0..=4 {
            let context = Context { source: source.clone(), sample: vec![0; copies],
                global_labels: (0..copies).rev().map(|i| i + 2).collect() };
            let lineages = (0..copies).map(|i| (i, Tree::Leaf(i))).collect::<Vec<_>>();
            let snapshot = Snapshot::from_lineages(&context, &lineages, Location::Edge(0),
                vec![true, false, true]).unwrap();
            let Decision::Table(table) = population_row(&context, &snapshot, Location::Edge(0),
                Limits::default()).unwrap() else { panic!("unexpected resource refusal"); };
            let quotient = unordered_pushforward(&context, &table).unwrap();
            let forest = unordered_forest(&context, &snapshot).unwrap();
            let native = crate::law::edge_kernel_for_refinement_test(&forest).unwrap()
                .into_iter().map(|(f, p)| (forest_key(&f), (f, p))).collect::<BTreeMap<_, _>>();
            assert_eq!(quotient, native, "all coefficient fibres, copies={copies}");
        }
        let context = Context { source, sample: vec![0; 4], global_labels: vec![3, 0, 2, 1] };
        let carried = Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(1)),
            Box::new(Tree::Leaf(0)))), Box::new(Tree::Leaf(2)));
        let snapshot = Snapshot::from_lineages(&context, &[(2, carried), (3, Tree::Leaf(3))],
            Location::Edge(0), vec![false, true, false]).unwrap();
        let Decision::Table(table) = population_row(&context, &snapshot, Location::Edge(0),
            Limits::default()).unwrap() else { panic!("unexpected resource refusal"); };
        let quotient = unordered_pushforward(&context, &table).unwrap();
        let native = crate::law::edge_kernel_for_refinement_test(&unordered_forest(&context, &snapshot).unwrap())
            .unwrap().into_iter().map(|(f, p)| (forest_key(&f), (f, p))).collect::<BTreeMap<_, _>>();
        assert_eq!(quotient, native, "carried subtree, nonminimum representative, restricted permutation");
    }
}
