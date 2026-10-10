//! Actual supplied-source joint terminal genealogy compiler.
//! Ports the inherited G7 full frontier DP, not products of pair marginals.
//! Its formal survival variables are not admitted natural physical images.
use crate::{forest::{ordinary_path_coefficients, Forest, Tree}, natural_cell::Source,
    polynomial::Polynomial, Rational};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mechanism { Common, Independent }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Budgets { pub states: usize, pub terms: usize, pub histories: usize }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request { pub source: Source, pub samples: Vec<usize>, pub mechanism: Mechanism, pub budgets: Budgets }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitKind { History, State, Term, Output }
impl LimitKind {
    pub fn token(self) -> &'static str { match self {
        Self::History => "HISTORY", Self::State => "STATE", Self::Term => "TERM", Self::Output => "OUTPUT",
    } }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limit { pub kind: LimitKind, pub vertex: usize, pub required: BigUint, pub cap: BigUint }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    pub rooted: BTreeMap<String, (Tree, Polynomial)>,
    pub unrooted: BTreeMap<String, Polynomial>,
    pub dimension: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision { Table(Table), Unknown(Limit) }

#[derive(Debug)]
enum Failure { Budget(Limit), Internal(&'static str) }
impl From<&'static str> for Failure { fn from(value: &'static str) -> Self { Self::Internal(value) } }

pub fn tree_string(tree: &Tree) -> String { match tree {
    Tree::Leaf(i) => i.to_string(),
    Tree::Node(a, b) => format!("({},{})", tree_string(a), tree_string(b)),
} }
fn least(tree: &Tree) -> usize { match tree { Tree::Leaf(i) => *i, Tree::Node(a, _) => least(a) } }
fn canonical_forest(mut forest: Forest) -> Forest { forest.sort_by_key(least); forest }
fn forest_string(forest: &Forest) -> String {
    format!("[{}]", forest.iter().map(tree_string).collect::<Vec<_>>().join(","))
}
fn joined(a: &Tree, b: &Tree) -> Tree {
    if least(a) < least(b) { Tree::Node(Box::new(a.clone()), Box::new(b.clone())) }
    else { Tree::Node(Box::new(b.clone()), Box::new(a.clone())) }
}
fn key(frontier: &[Forest]) -> Vec<String> { frontier.iter().map(forest_string).collect() }
fn pairs(k: usize) -> usize { k * k.saturating_sub(1) / 2 }
fn check_budget(kind: LimitKind, vertex: usize, required: BigUint, cap: usize) -> Result<(), Failure> {
    if required > BigUint::from(cap) {
        Err(Failure::Budget(Limit { kind, vertex, required, cap: BigUint::from(cap) }))
    } else { Ok(()) }
}

type Histories = BTreeMap<String, (Forest, BigInt)>;
fn merge_levels(start: &Forest, vertex: usize, cap: usize) -> Result<Vec<(usize, Histories)>, Failure> {
    let mut current = BTreeMap::new();
    current.insert(forest_string(start), (start.clone(), BigInt::one()));
    let mut k = start.len();
    let mut levels = vec![(k, current.clone())];
    while k > 1 {
        check_budget(LimitKind::History, vertex, BigUint::from(current.len()) * BigUint::from(pairs(k)), cap)?;
        let mut next: Histories = BTreeMap::new();
        for (forest, count) in current.values() {
            for i in 0..k { for j in i + 1..k {
                let mut out: Forest = forest.iter().enumerate().filter(|(a, _)| *a != i && *a != j)
                    .map(|(_, t)| t.clone()).collect();
                out.push(joined(&forest[i], &forest[j]));
                out = canonical_forest(out);
                let entry = next.entry(forest_string(&out)).or_insert((out, BigInt::zero()));
                entry.1 += count;
            } }
        }
        k -= 1;
        current = next;
        levels.push((k, current.clone()));
    }
    Ok(levels)
}

type Kernel = Vec<(Forest, Polynomial)>;
fn edge_kernel(start: &Forest, edge: usize, dimension: usize, vertex: usize, cap: usize)
    -> Result<Kernel, Failure> {
    if start.len() <= 1 { return Ok(vec![(start.clone(), Polynomial::one(dimension))]); }
    let mut outputs: BTreeMap<String, (Forest, Polynomial)> = BTreeMap::new();
    for (j, histories) in merge_levels(start, vertex, cap)? {
        for (forest, count) in histories.values() {
            let mut probability = Polynomial::zero(dimension);
            for (exponent, coefficient) in ordinary_path_coefficients(start.len(), j)? {
                let monomial = Polynomial::monomial(dimension, edge, exponent,
                    coefficient * Rational::from_integer(count.clone()))?;
                probability = probability.add(&monomial)?;
            }
            outputs.insert(forest_string(forest), (forest.clone(), probability));
        }
    }
    Ok(outputs.into_values().collect())
}
fn root_kernel(start: &Forest, dimension: usize, vertex: usize, cap: usize)
    -> Result<Vec<(Tree, Polynomial)>, Failure> {
    if start.is_empty() { return Err(Failure::Internal("LAW_EMPTY_ROOT")); }
    let levels = merge_levels(start, vertex, cap)?;
    let denominator: BigInt = (2..=start.len()).map(|k| BigInt::from(pairs(k))).product();
    let mut outputs: BTreeMap<String, (Tree, Polynomial)> = BTreeMap::new();
    for (forest, count) in levels.last().unwrap().1.values() {
        let tree = forest[0].clone();
        outputs.insert(tree_string(&tree), (tree, Polynomial::constant(dimension,
            Rational::new(count.clone(), denominator.clone()))));
    }
    Ok(outputs.into_values().collect())
}

fn routes(forest: &Forest, hybrid: Option<usize>, request: &Request, dimension: usize)
    -> Result<Vec<(Vec<Forest>, Polynomial)>, Failure> {
    let Some(hybrid) = hybrid else { return Ok(vec![(vec![forest.clone()], Polynomial::one(dimension))]); };
    let gamma = Polynomial::variable(dimension, request.source.edges.len() + hybrid)?;
    let complement = Polynomial::one(dimension).subtract(&gamma)?;
    if request.mechanism == Mechanism::Common {
        return Ok(vec![(vec![forest.clone(), vec![]], gamma), (vec![vec![], forest.clone()], complement)]);
    }
    let mut result = Vec::new();
    // Numeric masks with the first position as the high bit give lexicographic
    // vectors (0 before 1) rather than interchanging route occurrence order.
    for mask in 0usize..1usize << forest.len() {
        let mut groups = vec![vec![], vec![]];
        for (i, tree) in forest.iter().enumerate() {
            let bit = (mask >> (forest.len() - i - 1)) & 1;
            groups[bit].push(tree.clone());
        }
        let factor = gamma.power(groups[0].len())?.multiply(&complement.power(groups[1].len())?)?;
        result.push((groups, factor));
    }
    Ok(result)
}

struct State { frontier: Vec<Forest>, polynomial: Polynomial }
struct EdgeBranch { base: Vec<Forest>, incoming: Vec<usize>, kernels: Vec<Kernel>,
    incoming_probability: Polynomial, route_probability: Polynomial }
struct RootBranch { incoming_probability: Polynomial, outputs: Vec<(Tree, Polynomial)> }
enum Branch { Edge(EdgeBranch), Root(RootBranch) }

fn branch_counts(branch: &Branch) -> (BigUint, BigUint) { match branch {
    Branch::Root(b) => (BigUint::from(b.outputs.len()),
        BigUint::from(b.incoming_probability.terms.len()) * BigUint::from(b.outputs.len())),
    Branch::Edge(b) => {
        let mut state_count = BigUint::one();
        let mut term_count = BigUint::from(b.incoming_probability.terms.len())
            * BigUint::from(b.route_probability.terms.len());
        for kernel in &b.kernels {
            state_count *= BigUint::from(kernel.len());
            let total: BigUint = kernel.iter().map(|(_, p)| BigUint::from(p.terms.len())).sum();
            term_count *= total;
        }
        (state_count, term_count)
    }
} }

fn add_root(table: &mut BTreeMap<String, (Tree, Polynomial)>, tree: &Tree, polynomial: Polynomial)
    -> Result<(), Failure> {
    let name = tree_string(tree);
    let sum = match table.get(&name) { None => polynomial, Some((_, old)) => old.add(&polynomial)? };
    if sum.is_zero() { table.remove(&name); }
    else { table.insert(name, (tree.clone(), sum)); }
    Ok(())
}
fn add_state(states: &mut BTreeMap<Vec<String>, State>, frontier: Vec<Forest>, polynomial: Polynomial)
    -> Result<(), Failure> {
    let name = key(&frontier);
    let sum = match states.get(&name) { None => polynomial, Some(old) => old.polynomial.add(&polynomial)? };
    if sum.is_zero() { states.remove(&name); }
    else { states.insert(name, State { frontier, polynomial: sum }); }
    Ok(())
}
fn emit_edge(branch: &EdgeBranch, index: usize, frontier: Vec<Forest>, polynomial: Polynomial,
    states: &mut BTreeMap<Vec<String>, State>) -> Result<(), Failure> {
    if index == branch.kernels.len() { return add_state(states, frontier, polynomial); }
    for (forest, factor) in &branch.kernels[index] {
        let mut out = frontier.clone();
        out[branch.incoming[index]] = forest.clone();
        emit_edge(branch, index + 1, out, polynomial.multiply(factor)?, states)?;
    }
    Ok(())
}

pub fn split_string(tree: &Tree, samples: usize) -> String {
    type Cut = (Vec<usize>, Vec<usize>);
    fn visit(tree: &Tree, samples: usize, cuts: &mut BTreeSet<Cut>) -> Vec<usize> {
        let mut side = match tree {
            Tree::Leaf(i) => vec![*i],
            Tree::Node(a, b) => { let mut xs = visit(a, samples, cuts); xs.extend(visit(b, samples, cuts)); xs }
        };
        side.sort_unstable();
        let other: Vec<_> = (0..samples).filter(|i| !side.contains(i)).collect();
        if side.len() >= 2 && other.len() >= 2 {
            cuts.insert(if side < other { (side.clone(), other) } else { (other, side.clone()) });
        }
        side
    }
    let mut cuts = BTreeSet::new();
    visit(tree, samples, &mut cuts);
    let side = |v: &Vec<usize>| format!("[{}]", v.iter().map(usize::to_string).collect::<Vec<_>>().join(","));
    format!("[{}]", cuts.iter().map(|(a, b)| format!("{}|{}", side(a), side(b))).collect::<Vec<_>>().join(";"))
}
fn tree_labels(tree: &Tree) -> Vec<usize> { match tree {
    Tree::Leaf(i) => vec![*i],
    Tree::Node(a, b) => { let mut ids = tree_labels(a); ids.extend(tree_labels(b)); ids.sort_unstable(); ids }
} }

impl Request {
    pub fn validate(&self) -> Result<(), &'static str> {
        self.source.validate()?;
        if self.source.vertices < 3 || self.source.vertices > 32 || self.source.edges.len() < 2
            || self.source.edges.len() > 32 || self.source.dimension() > 32
            || self.samples.is_empty() || self.samples.len() > 4
            || self.samples.iter().any(|taxon| *taxon >= self.source.leaves.len())
            || self.budgets.states > 4096 || self.budgets.terms > 65536 || self.budgets.histories > 4096 {
            return Err("LAW_LIMIT");
        }
        Ok(())
    }
}

fn compile_inner(request: &Request) -> Result<Table, Failure> {
    let source = &request.source;
    let dimension = source.edges.len() + source.hybrids.len();
    let mut incoming = vec![vec![]; source.vertices];
    let mut outgoing = vec![vec![]; source.vertices];
    for (i, edge) in source.edges.iter().enumerate() { incoming[edge.target].push(i); outgoing[edge.source].push(i); }
    let mut remaining: Vec<_> = incoming.iter().map(Vec::len).collect();
    let mut ready: BTreeSet<_> = (0..source.vertices).filter(|i| remaining[*i] == 0).collect();
    let mut order = Vec::new();
    while let Some(vertex) = ready.pop_first() {
        order.push(vertex);
        for e in &outgoing[vertex] {
            let target = source.edges[*e].target;
            remaining[target] -= 1;
            if remaining[target] == 0 { ready.insert(target); }
        }
    }
    if order.len() != source.vertices { return Err(Failure::Internal("LAW_TOPOLOGY")); }
    let mut hybrid_ids = vec![None; source.vertices];
    for (id, hybrid) in source.hybrids.iter().enumerate() {
        hybrid_ids[hybrid.vertex] = Some(id);
        incoming[hybrid.vertex] = hybrid.incoming.to_vec();
    }
    let mut sampled = vec![vec![]; source.vertices];
    for (id, taxon) in request.samples.iter().enumerate() { sampled[source.leaves[*taxon]].push(Tree::Leaf(id)); }
    let initial = State { frontier: vec![vec![]; source.edges.len()], polynomial: Polynomial::one(dimension) };
    let mut states = BTreeMap::new();
    states.insert(key(&initial.frontier), initial);
    let mut rooted = BTreeMap::new();
    for vertex in order.into_iter().rev() {
        let mut branches = Vec::new();
        // All HISTORY checks happen here, before either stage STATE/TERM check.
        for state in states.values() {
            let mut base = state.frontier.clone();
            let mut live = sampled[vertex].clone();
            for edge in &outgoing[vertex] { live.append(&mut base[*edge]); }
            live = canonical_forest(live);
            if vertex == source.root {
                if base.iter().any(|forest| !forest.is_empty()) { return Err(Failure::Internal("LAW_UNCONSUMED_ROOT")); }
                branches.push(Branch::Root(RootBranch { incoming_probability: state.polynomial.clone(),
                    outputs: root_kernel(&live, dimension, vertex, request.budgets.histories)? }));
            } else {
                for (groups, route_probability) in routes(&live, hybrid_ids[vertex], request, dimension)? {
                    let mut kernels = Vec::new();
                    for (group, edge) in groups.iter().zip(&incoming[vertex]) {
                        kernels.push(edge_kernel(group, *edge, dimension, vertex, request.budgets.histories)?);
                    }
                    branches.push(Branch::Edge(EdgeBranch { base: base.clone(), incoming: incoming[vertex].clone(),
                        kernels, incoming_probability: state.polynomial.clone(), route_probability }));
                }
            }
        }
        let (required_states, required_terms) = branches.iter().map(branch_counts)
            .fold((BigUint::zero(), BigUint::zero()), |(a, b), (c, d)| (a + c, b + d));
        check_budget(LimitKind::State, vertex, required_states, request.budgets.states)?;
        check_budget(LimitKind::Term, vertex, required_terms, request.budgets.terms)?;
        let mut next = BTreeMap::new();
        for branch in branches {
            match branch {
                Branch::Root(b) => for (tree, factor) in b.outputs {
                    add_root(&mut rooted, &tree, b.incoming_probability.multiply(&factor)?)?;
                },
                Branch::Edge(b) => {
                    let probability = b.incoming_probability.multiply(&b.route_probability)?;
                    emit_edge(&b, 0, b.base.clone(), probability, &mut next)?;
                }
            }
        }
        if vertex != source.root { states = next; }
    }
    let mut sum = Polynomial::zero(dimension);
    let mut unrooted: BTreeMap<String, Polynomial> = BTreeMap::new();
    for (tree, polynomial) in rooted.values() {
        if tree_labels(tree) != (0..request.samples.len()).collect::<Vec<_>>() {
            return Err(Failure::Internal("LAW_TERMINAL_LABELS"));
        }
        sum = sum.add(polynomial)?;
        let signature = split_string(tree, request.samples.len());
        let old = unrooted.remove(&signature).unwrap_or_else(|| Polynomial::zero(dimension));
        let updated = old.add(polynomial)?;
        if !updated.is_zero() { unrooted.insert(signature, updated); }
    }
    if sum != Polynomial::one(dimension) { return Err(Failure::Internal("LAW_TOTAL_MASS")); }
    Ok(Table { rooted, unrooted, dimension })
}

pub fn compile(request: &Request) -> Result<Decision, &'static str> {
    request.validate()?;
    match compile_inner(request) {
        Ok(table) => Ok(Decision::Table(table)),
        Err(Failure::Budget(limit)) => Ok(Decision::Unknown(limit)),
        Err(Failure::Internal(error)) => Err(error),
    }
}
