//! Literal natural-cell forms compiled to one shared rational bank.
//! Mirrors NaturalCellAffineCompiler.compileCell's eight row groups. Graph
//! validation checks the finite predicates of RootedBinary (including source
//! LSA), but does not discharge missing typed-source/class refinement proofs,
//! active-epoch chart coverage or any observation-law correspondence.
use crate::{affine::Row, q, Rational};
use std::collections::VecDeque;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge { pub source: usize, pub target: usize }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hybrid { pub vertex: usize, pub incoming: [usize; 2] }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Source {
    pub vertices: usize,
    pub root: usize,
    /// Index is original edge occurrence identity; parallel endpoints remain.
    pub edges: Vec<Edge>,
    /// Index is original taxon identity; the map must be injective.
    pub leaves: Vec<usize>,
    pub hybrids: Vec<Hybrid>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgeAtom { Node(usize), Fixed(Rational) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Comparison { Strict, Weak, Equal }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgeConstraint { pub kind: Comparison, pub left: AgeAtom, pub right: AgeAtom }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bound { pub value: Rational, pub strict: bool }
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Interval { pub lower: Option<Bound>, pub upper: Option<Bound> }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Population { Edge(usize), Ancestral }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exposure {
    pub population: Population,
    pub younger: AgeAtom,
    pub older: AgeAtom,
    pub interval: Interval,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chart {
    pub source: Source,
    pub chronology: Vec<AgeConstraint>,
    /// All exposure rows share rates for the same original population ID.
    pub exposures: Vec<Exposure>,
    pub coins: Vec<Interval>,
    pub cap: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Compiled { pub dimension: usize, pub rows: Vec<Row>, pub bank_names: Vec<String> }

impl Source {
    fn reachable(&self, blocked: Option<usize>) -> Vec<bool> {
        let mut visited = vec![false; self.vertices];
        if blocked == Some(self.root) { return visited; }
        let mut stack = vec![self.root];
        visited[self.root] = true;
        while let Some(v) = stack.pop() {
            for edge in &self.edges {
                if edge.source == v && blocked != Some(edge.target) && !visited[edge.target] {
                    visited[edge.target] = true;
                    stack.push(edge.target);
                }
            }
        }
        visited
    }

    /// Explicit finite structural predicates; distinct edge IDs are counted
    /// independently even when their source/target endpoints coincide.
    pub fn validate(&self) -> Result<(), &'static str> {
        let v = self.vertices;
        if v == 0 || self.root >= v || self.leaves.len() < 2 { return Err("SOURCE_SIZE"); }
        if self.edges.iter().any(|e| e.source >= v || e.target >= v)
            || self.leaves.iter().any(|leaf| *leaf >= v) { return Err("SOURCE_REFERENCE"); }
        let mut indegree = vec![0usize; v];
        let mut outdegree = vec![0usize; v];
        for edge in &self.edges { indegree[edge.target] += 1; outdegree[edge.source] += 1; }
        if indegree[self.root] != 0 || outdegree[self.root] != 2 { return Err("ROOT_DEGREES"); }
        let mut leaf_set = vec![false; v];
        for leaf in &self.leaves {
            if leaf_set[*leaf] || indegree[*leaf] != 1 || outdegree[*leaf] != 0 { return Err("LEAF_DEGREES"); }
            leaf_set[*leaf] = true;
        }
        let mut hybrid_set = vec![false; v];
        for hybrid in &self.hybrids {
            if hybrid.vertex >= v || hybrid_set[hybrid.vertex]
                || hybrid.incoming[0] == hybrid.incoming[1]
                || hybrid.incoming.iter().any(|e| *e >= self.edges.len()
                    || self.edges[*e].target != hybrid.vertex)
                || indegree[hybrid.vertex] != 2 || outdegree[hybrid.vertex] != 1 {
                return Err("HYBRID_REGISTRY");
            }
            hybrid_set[hybrid.vertex] = true;
        }
        for vertex in 0..v {
            if vertex == self.root || leaf_set[vertex] { continue; }
            let tree = indegree[vertex] == 1 && outdegree[vertex] == 2;
            let hybrid = indegree[vertex] == 2 && outdegree[vertex] == 1;
            if !(tree || hybrid) || hybrid != hybrid_set[vertex] { return Err("INTERNAL_DEGREES"); }
        }
        let mut remaining = indegree;
        let mut queue: VecDeque<_> = (0..v).filter(|i| remaining[*i] == 0).collect();
        let mut removed = 0;
        while let Some(vertex) = queue.pop_front() {
            removed += 1;
            for edge in &self.edges {
                if edge.source == vertex {
                    remaining[edge.target] -= 1;
                    if remaining[edge.target] == 0 { queue.push_back(edge.target); }
                }
            }
        }
        if removed != v { return Err("SOURCE_CYCLE"); }
        if self.reachable(None).iter().any(|visited| !visited) { return Err("SOURCE_ROOTED"); }
        // No nonroot original vertex dominates every original leaf.
        for blocked in 0..v {
            if blocked == self.root { continue; }
            let reachable = self.reachable(Some(blocked));
            if !self.leaves.iter().any(|leaf| reachable[*leaf]) { return Err("SOURCE_LEAST_STABLE"); }
        }
        Ok(())
    }
    pub fn dimension(&self) -> usize { self.vertices + self.edges.len() + 1 + self.hybrids.len() }
    pub fn population_index(&self, population: Population) -> usize {
        self.vertices + match population { Population::Edge(e) => e, Population::Ancestral => self.edges.len() }
    }
    pub fn coin_index(&self, hybrid: usize) -> usize { self.vertices + self.edges.len() + 1 + hybrid }
}

#[derive(Clone)]
struct Form { coefficients: Vec<Rational>, constant: Rational }
impl Form {
    fn constant(n: usize, value: Rational) -> Self { Self { coefficients: vec![q(0, 1); n], constant: value } }
    fn variable(n: usize, i: usize) -> Self {
        let mut result = Self::constant(n, q(0, 1)); result.coefficients[i] = q(1, 1); result
    }
    fn sub(&self, other: &Self) -> Self {
        Self { coefficients: self.coefficients.iter().zip(&other.coefficients).map(|(a, b)| a - b).collect(),
               constant: &self.constant - &other.constant }
    }
    fn scale(&self, by: &Rational) -> Self {
        Self { coefficients: self.coefficients.iter().map(|a| a * by).collect(), constant: &self.constant * by }
    }
}
fn comparison(rows: &mut Vec<Row>, kind: Comparison, a: &Form, b: &Form) {
    rows.push(Row { coefficients: a.coefficients.iter().zip(&b.coefficients).map(|(a, b)| a - b).collect(),
                    bound: &b.constant - &a.constant, strict: kind == Comparison::Strict });
    if kind == Comparison::Equal { comparison(rows, Comparison::Weak, b, a); }
}
fn scaled(rows: &mut Vec<Row>, interval: &Interval, duration: &Form, inverse: &Form) {
    if let Some(bound) = &interval.lower {
        comparison(rows, if bound.strict { Comparison::Strict } else { Comparison::Weak },
                   &inverse.scale(&bound.value), duration);
    }
    if let Some(bound) = &interval.upper {
        comparison(rows, if bound.strict { Comparison::Strict } else { Comparison::Weak },
                   duration, &inverse.scale(&bound.value));
    }
}
fn age(source: &Source, atom: &AgeAtom) -> Result<Form, &'static str> {
    match atom {
        AgeAtom::Node(i) if *i < source.vertices => Ok(Form::variable(source.dimension(), *i)),
        AgeAtom::Fixed(value) => Ok(Form::constant(source.dimension(), value.clone())),
        _ => Err("AGE_REFERENCE"),
    }
}

pub fn compile(chart: &Chart) -> Result<Compiled, &'static str> {
    let source = &chart.source;
    source.validate()?;
    if chart.coins.len() != source.hybrids.len() { return Err("COIN_REGISTRY"); }
    let n = source.dimension();
    if n > 32 || chart.cap > 4096 { return Err("CHART_DIMENSION"); }
    let zero = Form::constant(n, q(0, 1));
    let one = Form::constant(n, q(1, 1));
    let mut rows = Vec::new();
    // 1. Each original edge has strictly positive original duration.
    for edge in &source.edges {
        comparison(&mut rows, Comparison::Strict, &Form::variable(n, edge.target), &Form::variable(n, edge.source));
    }
    // 2. Every original labeled tip age is exactly zero.
    for leaf in &source.leaves { comparison(&mut rows, Comparison::Equal, &Form::variable(n, *leaf), &zero); }
    // 3. Distinct original edge rates then one ancestral continuation rate.
    for i in 0..=source.edges.len() {
        comparison(&mut rows, Comparison::Strict, &zero, &Form::variable(n, source.vertices + i));
    }
    // 4–5. One open physical coin per original hybrid.
    for h in 0..source.hybrids.len() {
        comparison(&mut rows, Comparison::Strict, &zero, &Form::variable(n, source.coin_index(h)));
    }
    for h in 0..source.hybrids.len() {
        comparison(&mut rows, Comparison::Strict, &Form::variable(n, source.coin_index(h)), &one);
    }
    // 6. Caller chronology remains joint on the same original age bank.
    for c in &chart.chronology { comparison(&mut rows, c.kind, &age(source, &c.left)?, &age(source, &c.right)?); }
    // 7. Interval hazards use duration / inverse-rate, through scaled rows.
    for exposure in &chart.exposures {
        if matches!(exposure.population, Population::Edge(i) if i >= source.edges.len()) { return Err("POPULATION_REFERENCE"); }
        let duration = age(source, &exposure.older)?.sub(&age(source, &exposure.younger)?);
        scaled(&mut rows, &exposure.interval, &duration, &Form::variable(n, source.population_index(exposure.population)));
    }
    // 8. Additional hybrid intervals, including absent saturation endpoints.
    for (h, interval) in chart.coins.iter().enumerate() {
        scaled(&mut rows, interval, &Form::variable(n, source.coin_index(h)), &one);
    }
    if rows.len() > 128 { return Err("CHART_ROWS"); }
    let bank_names = (0..source.vertices).map(|i| format!("AGE:{i}"))
        .chain((0..source.edges.len()).map(|i| format!("RATE:{i}")))
        .chain(std::iter::once("RATE:A".to_owned()))
        .chain((0..source.hybrids.len()).map(|i| format!("COIN:{i}"))).collect();
    Ok(Compiled { dimension: n, rows, bank_names })
}

/// Direct chart interpretation for a rational bank, independent of emitted
/// coefficient rows: explicit durations, positive reciprocal rates and coins.
pub fn check_bank(chart: &Chart, bank: &[Rational]) -> bool {
    let source = &chart.source;
    if source.validate().is_err() || chart.coins.len() != source.hybrids.len() || bank.len() != source.dimension() { return false; }
    let holds = |kind: Comparison, a: &Rational, b: &Rational| match kind {
        Comparison::Strict => a < b, Comparison::Weak => a <= b, Comparison::Equal => a == b,
    };
    let atom = |a: &AgeAtom| match a {
        AgeAtom::Node(i) => bank.get(*i).filter(|_| *i < source.vertices).cloned(),
        AgeAtom::Fixed(q) => Some(q.clone()),
    };
    let inside = |interval: &Interval, value: &Rational| {
        interval.lower.as_ref().is_none_or(|b| holds(if b.strict { Comparison::Strict } else { Comparison::Weak }, &b.value, value))
            && interval.upper.as_ref().is_none_or(|b| holds(if b.strict { Comparison::Strict } else { Comparison::Weak }, value, &b.value))
    };
    if source.edges.iter().any(|e| bank[e.target] >= bank[e.source])
        || source.leaves.iter().any(|i| bank[*i] != q(0, 1))
        || (0..=source.edges.len()).any(|i| bank[source.vertices + i] <= q(0, 1))
        || (0..source.hybrids.len()).any(|h| bank[source.coin_index(h)] <= q(0, 1) || bank[source.coin_index(h)] >= q(1, 1)) { return false; }
    for c in &chart.chronology {
        match (atom(&c.left), atom(&c.right)) {
            (Some(a), Some(b)) if holds(c.kind, &a, &b) => {}, _ => return false,
        }
    }
    for exposure in &chart.exposures {
        if matches!(exposure.population, Population::Edge(i) if i >= source.edges.len()) { return false; }
        match (atom(&exposure.older), atom(&exposure.younger)) {
            (Some(a), Some(b)) if inside(&exposure.interval, &((&a - &b) / &bank[source.population_index(exposure.population)])) => {},
            _ => return false,
        }
    }
    chart.coins.iter().enumerate().all(|(h, interval)| inside(interval, &bank[source.coin_index(h)]))
}
