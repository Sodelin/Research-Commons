//! Controlled original-ID words using the existing conditional-word engine.
//! SOURCE ONLY: uncompiled/unexecuted. No process, writer, dispatch or new kernel.
//!
//! The natural register mixture remains outside forced TRANSITION substitution,
//! matching G7ControlledWordPolynomial. Full selected views retain that register.
//! A supplied word still needs its actual calendar/source/readout interpretation.
#![forbid(unsafe_code)]

use parity_solver::{forest::Tree, polynomial::Polynomial, q, Rational,
    source_epoch::{self as epoch, Transition},
    source_population::{Location, Snapshot}, source_word as word};
use std::collections::{BTreeMap, btree_map::Entry};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub conditional_requests: usize,
    pub child_queries: usize,
    pub child_branches: usize,
    pub child_term_products: usize,
    pub polynomial_work: usize,
    pub destinations: usize,
    pub retained_terms: usize,
    pub rational_bits: u64,
}
impl Default for Limits {
    fn default() -> Self {
        Self { conditional_requests: 256, child_queries: 65_536,
            child_branches: 1_000_000, child_term_products: 4_000_000,
            polynomial_work: 10_000_000, destinations: 4096,
            retained_terms: 65_536, rational_bits: 65_536 }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage { Input, Initialization, Register(usize), Output }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitKind {
    InheritedProfile(&'static str), RegisterAssignments, InitialTerms, ConditionalRequests,
    ChildQueries, ChildBranches, ChildTermProducts, PolynomialWork,
    Destinations, RetainedTerms, RationalBits,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    /// None means checked machine count overflow; never source exclusion.
    Unknown { stage: Stage, kind: LimitKind, required: Option<usize>, cap: usize },
    ChildUnknown { register_index: usize, original_limit: word::Limit },
    ChildFailure { register_index: usize, original_error: word::Error },
    Internal(&'static str),
}
type Result<T> = std::result::Result<T, Error>;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Work {
    pub conditional_requests: usize,
    pub child_queries: usize,
    pub child_branches: usize,
    pub child_term_products: usize,
    pub polynomial_work: usize,
    pub retained_terms: usize,
    pub largest_destinations: usize,
    pub largest_retained_terms: usize,
}
/// Read-only association to the exact immutable supplied input objects. This
/// does not authenticate captured external bytes or prove native refinement.
#[derive(Debug)]
pub struct Table<'a> {
    original: &'a word::Request,
    mask: &'a [Option<bool>],
    variables: Vec<word::Variable>,
    transitions: Vec<Transition>,
    work: Work,
}
impl<'a> Table<'a> {
    pub fn original(&self) -> &word::Request { self.original }
    pub fn mask(&self) -> &[Option<bool>] { self.mask }
    pub fn variables(&self) -> &[word::Variable] { &self.variables }
    pub fn transitions(&self) -> &[Transition] { &self.transitions }
    pub fn work(&self) -> &Work { &self.work }
}

fn unknown(stage: Stage, kind: LimitKind, required: Option<usize>, cap: usize) -> Error {
    Error::Unknown { stage, kind, required, cap }
}
fn add(a: usize, b: usize, stage: Stage, kind: LimitKind, cap: usize) -> Result<usize> {
    let sum = a.checked_add(b).ok_or_else(|| unknown(stage, kind, None, cap))?;
    if sum > cap { return Err(unknown(stage, kind, Some(sum), cap)); }
    Ok(sum)
}
fn count_power(base: usize, exponent: usize, stage: Stage, kind: LimitKind, cap: usize)
    -> Result<usize> {
    let exponent = u32::try_from(exponent).map_err(|_| unknown(stage, kind, None, cap))?;
    let value = base.checked_pow(exponent).ok_or_else(|| unknown(stage, kind, None, cap))?;
    if value > cap { return Err(unknown(stage, kind, Some(value), cap)); }
    Ok(value)
}
struct Budget { limits: Limits, work: Work }
impl Budget {
    fn charge(&mut self, amount: usize, stage: Stage) -> Result<()> {
        self.work.polynomial_work = add(self.work.polynomial_work, amount, stage,
            LimitKind::PolynomialWork, self.limits.polynomial_work)?;
        Ok(())
    }
    fn coefficient(&self, value: &Rational, stage: Stage) -> Result<()> {
        if value.denom() <= q(0, 1).numer() {
            return Err(Error::Internal("CONTROLLED_WORD_DENOMINATOR"));
        }
        let bits = value.numer().bits().max(value.denom().bits());
        if bits > self.limits.rational_bits {
            return Err(unknown(stage, LimitKind::RationalBits,
                usize::try_from(bits).ok(), usize::try_from(self.limits.rational_bits).unwrap_or(usize::MAX)));
        }
        Ok(())
    }
    fn polynomial(&mut self, value: &Polynomial, dimension: usize, stage: Stage) -> Result<()> {
        if value.dimension != dimension || value.terms.keys().any(|powers| powers.len() != dimension) {
            return Err(Error::Internal("CONTROLLED_WORD_POLYNOMIAL_DIMENSION"));
        }
        if value.terms.len() > self.limits.retained_terms {
            return Err(unknown(stage, LimitKind::RetainedTerms,
                Some(value.terms.len()), self.limits.retained_terms));
        }
        for coefficient in value.terms.values() {
            if coefficient == &q(0, 1) {
                return Err(Error::Internal("CONTROLLED_WORD_ZERO_TERM"));
            }
            self.coefficient(coefficient, stage)?;
        }
        let cost = value.terms.len().checked_mul(dimension.checked_add(1)
            .ok_or_else(|| unknown(stage, LimitKind::PolynomialWork, None, self.limits.polynomial_work))?)
            .ok_or_else(|| unknown(stage, LimitKind::PolynomialWork, None, self.limits.polynomial_work))?;
        self.charge(cost, stage)
    }
    fn term(&mut self, output: &mut Polynomial, powers: Vec<usize>,
        coefficient: Rational, stage: Stage) -> Result<()> {
        if powers.len() != output.dimension {
            return Err(Error::Internal("CONTROLLED_WORD_EXPONENT_ARITY"));
        }
        self.charge(powers.len().checked_add(1).ok_or_else(||
            unknown(stage, LimitKind::PolynomialWork, None, self.limits.polynomial_work))?, stage)?;
        self.coefficient(&coefficient, stage)?;
        if coefficient == q(0, 1) { return Ok(()); }
        let length = output.terms.len();
        match output.terms.entry(powers) {
            Entry::Vacant(entry) => {
                if length >= self.limits.retained_terms {
                    return Err(unknown(stage, LimitKind::RetainedTerms,
                        length.checked_add(1), self.limits.retained_terms));
                }
                entry.insert(coefficient);
            }
            Entry::Occupied(mut entry) => {
                let sum = entry.get() + coefficient;
                self.coefficient(&sum, stage)?;
                if sum == q(0, 1) { entry.remove(); } else { *entry.get_mut() = sum; }
            }
        }
        Ok(())
    }
    fn multiply(&mut self, left: &Polynomial, right: &Polynomial, stage: Stage)
        -> Result<Polynomial> {
        if left.dimension != right.dimension {
            return Err(Error::Internal("CONTROLLED_WORD_PRODUCT_DIMENSION"));
        }
        let products = left.terms.len().checked_mul(right.terms.len())
            .and_then(|n| n.checked_mul(left.dimension.checked_add(1)?))
            .ok_or_else(|| unknown(stage, LimitKind::PolynomialWork, None, self.limits.polynomial_work))?;
        self.charge(products, stage)?;
        let product = left.multiply(right).map_err(Error::Internal)?;
        self.polynomial(&product, left.dimension, stage)?;
        Ok(product)
    }
}

/// Reject the inherited carrier profile as unavailable before its validator
/// allocates per-vertex data. Validate every supplied letter before soft limits.
/// This source mirror is not a proof of the original validator or a parser.
fn validate(request: &word::Request, mask: &[Option<bool>]) -> Result<usize> {
    let context = &request.context;
    let source = &context.source;
    let bank = source.vertices.checked_add(source.edges.len())
        .and_then(|n| n.checked_add(1)).and_then(|n| n.checked_add(source.hybrids.len()));
    for (name, required, cap) in [
        ("vertices", source.vertices, 32), ("edges", source.edges.len(), 32),
        ("taxa", source.leaves.len(), 32), ("hybrids", source.hybrids.len(), 32),
        ("sampled_copies", context.sample.len(), 4),
    ] {
        if required > cap {
            return Err(unknown(Stage::Input, LimitKind::InheritedProfile(name), Some(required), cap));
        }
    }
    if bank.is_none() || bank.is_some_and(|n| n > 32) {
        return Err(unknown(Stage::Input, LimitKind::InheritedProfile("full_bank"), bank, 32));
    }
    context.validate().map_err(Error::Invalid)?;
    if !matches!(&request.initial, word::Initial::Natural) {
        return Err(Error::Invalid("CONTROLLED_WORD_REQUIRES_NATURAL_INITIAL"));
    }
    if mask.len() != source.hybrids.len() || request.common.len() != source.hybrids.len() {
        return Err(Error::Invalid("CONTROLLED_WORD_REGISTRY_LENGTH"));
    }
    for (name, required, cap) in [("slots", request.slots, 16), ("word_length", request.word.len(), 32)] {
        if required > cap {
            return Err(unknown(Stage::Input, LimitKind::InheritedProfile(name), Some(required), cap));
        }
    }
    if context.global_labels.iter().any(|label| u64::try_from(*label).is_err()) {
        return Err(unknown(Stage::Input, LimitKind::InheritedProfile("global_label_u64"), None, usize::MAX));
    }
    let populations = source.edges.len().checked_add(1)
        .ok_or_else(|| unknown(Stage::Input, LimitKind::InheritedProfile("populations"), None, 32))?;
    let dimension = request.slots.checked_mul(populations)
        .and_then(|n| n.checked_add(source.hybrids.len()))
        .ok_or_else(|| unknown(Stage::Input, LimitKind::InheritedProfile("word_variable_bank"), None, 256))?;
    if populations > 32 || dimension > 256 {
        return Err(unknown(Stage::Input, LimitKind::InheritedProfile("word_variable_bank"), Some(dimension), 256));
    }
    for symbol in &request.word {
        match *symbol {
            word::Symbol::Interval(slot) if slot >= request.slots =>
                return Err(Error::Invalid("SOURCE_WORD_SLOT")),
            word::Symbol::Exit(edge) if edge >= source.edges.len() =>
                return Err(Error::Invalid("SOURCE_WORD_EDGE")),
            word::Symbol::Enter(vertex) => {
                if vertex >= source.vertices { return Err(Error::Invalid("SOURCE_WORD_VERTEX")); }
                if vertex != source.root && !source.hybrids.iter().any(|h| h.vertex == vertex)
                    && source.edges.iter().filter(|edge| edge.target == vertex).count() != 1 {
                    return Err(Error::Invalid("SOURCE_WORD_ORDINARY_DEGREE"));
                }
            }
            _ => {}
        }
    }
    if request.terminal == word::Terminal::AncestralComplete && context.sample.is_empty() {
        return Err(Error::Invalid("SOURCE_WORD_COMPLETION_EMPTY_COPY"));
    }
    Ok(dimension)
}

fn snapshot(request: &word::Request, register_index: usize) -> Result<Snapshot> {
    let source = &request.context.source;
    let hybrids = source.hybrids.len();
    let copies = request.context.sample.len();
    let mut register = vec![false; source.vertices];
    for (index, hybrid) in source.hybrids.iter().enumerate() {
        let shift = hybrids.checked_sub(index + 1)
            .ok_or(Error::Internal("CONTROLLED_WORD_REGISTER_INDEX"))?;
        let bit = 1usize.checked_shl(u32::try_from(shift)
            .map_err(|_| Error::Internal("CONTROLLED_WORD_REGISTER_INDEX"))?)
            .ok_or(Error::Internal("CONTROLLED_WORD_REGISTER_INDEX"))?;
        register[hybrid.vertex] = register_index & bit != 0;
    }
    let result = Snapshot { live: (0..copies).collect(), ancestor: (0..copies).collect(),
        genealogy: (0..copies).map(|copy| Some(Tree::Leaf(copy))).collect(),
        population: request.context.sample.iter().map(|taxon|
            Some(Location::Node(source.leaves[*taxon]))).collect(), register };
    request.context.validate_snapshot(&result).map_err(Error::Internal)?;
    Ok(result)
}

fn register_weight(request: &word::Request, snapshot: &Snapshot, dimension: usize,
    budget: &mut Budget, stage: Stage) -> Result<Polynomial> {
    let source = &request.context.source;
    let gamma_base = dimension.checked_sub(source.hybrids.len())
        .ok_or(Error::Internal("CONTROLLED_WORD_GAMMA_BANK"))?;
    let mut weight = Polynomial::one(dimension);
    for (index, hybrid) in source.hybrids.iter().enumerate() {
        let gamma = Polynomial::variable(dimension, gamma_base + index).map_err(Error::Internal)?;
        let factor = if snapshot.register[hybrid.vertex] { gamma }
            else { Polynomial::one(dimension).subtract(&gamma).map_err(Error::Internal)? };
        weight = budget.multiply(&weight, &factor, stage)?;
    }
    Ok(weight)
}

/// Only the conditional transition polynomial is specialized. Initialization
/// weights above retain all original natural gamma variables.
fn substitute_transition(value: &Polynomial, mask: &[Option<bool>],
    budget: &mut Budget, stage: Stage) -> Result<Polynomial> {
    let gamma_base = value.dimension.checked_sub(mask.len())
        .ok_or(Error::Internal("CONTROLLED_WORD_GAMMA_BANK"))?;
    let mut output = Polynomial::zero(value.dimension);
    for (powers, coefficient) in &value.terms {
        if powers.len() != value.dimension {
            return Err(Error::Internal("CONTROLLED_WORD_EXPONENT_ARITY"));
        }
        budget.charge(mask.len(), stage)?;
        if mask.iter().enumerate().any(|(h, forced)|
            *forced == Some(false) && powers[gamma_base + h] != 0) { continue; }
        let mut substituted = powers.clone();
        for (h, forced) in mask.iter().enumerate() {
            if forced.is_some() { substituted[gamma_base + h] = 0; }
        }
        budget.term(&mut output, substituted, coefficient.clone(), stage)?;
    }
    Ok(output)
}

fn accumulate(output: &mut BTreeMap<String, Transition>, candidate: Transition,
    budget: &mut Budget, stage: Stage) -> Result<()> {
    if candidate.polynomial.is_zero() { return Ok(()); }
    let key = epoch::selected_key(&candidate.view);
    let previous_terms = output.get(&key).map_or(0, |old| old.polynomial.terms.len());
    let result = if let Some(old) = output.get(&key) {
        if old.view != candidate.view || old.witness.register != candidate.witness.register {
            return Err(Error::Internal("CONTROLLED_WORD_SELECTED_KEY"));
        }
        let mut polynomial = old.polynomial.clone();
        for (powers, coefficient) in &candidate.polynomial.terms {
            budget.term(&mut polynomial, powers.clone(), coefficient.clone(), stage)?;
        }
        let witness = if parity_solver::source_population::snapshot_key(&old.witness)
            < parity_solver::source_population::snapshot_key(&candidate.witness) {
            old.witness.clone()
        } else { candidate.witness };
        Transition { view: candidate.view, witness, polynomial }
    } else {
        add(output.len(), 1, stage, LimitKind::Destinations, budget.limits.destinations)?;
        candidate
    };
    let without_previous = budget.work.retained_terms.checked_sub(previous_terms)
        .ok_or(Error::Internal("CONTROLLED_WORD_TERM_ACCOUNT"))?;
    budget.work.retained_terms = add(without_previous, result.polynomial.terms.len(),
        stage, LimitKind::RetainedTerms, budget.limits.retained_terms)?;
    if result.polynomial.is_zero() { output.remove(&key); } else { output.insert(key, result); }
    budget.work.largest_destinations = budget.work.largest_destinations.max(output.len());
    budget.work.largest_retained_terms = budget.work.largest_retained_terms.max(budget.work.retained_terms);
    Ok(())
}

/// Compose existing exact conditional rows with the unchanged natural register
/// mixture. Every failure returns no Table. Physical source/calendar admission,
/// actual readouts and the universal Rust/Lean correspondence remain separate.
pub fn controlled_word<'a>(request: &'a word::Request, mask: &'a [Option<bool>],
    limits: Limits) -> Result<Table<'a>> {
    let dimension = validate(request, mask)?;
    let assignments = count_power(2, mask.len(), Stage::Initialization,
        LimitKind::RegisterAssignments, request.limits.initial_assignments)?;
    count_power(3, mask.len(), Stage::Initialization,
        LimitKind::InitialTerms, request.limits.initial_terms)?;
    if assignments > limits.conditional_requests {
        return Err(unknown(Stage::Initialization, LimitKind::ConditionalRequests,
            Some(assignments), limits.conditional_requests));
    }
    let mut budget = Budget { limits, work: Work::default() };
    let populations = request.context.source.edges.len() + 1;
    let variables = (0..request.slots).flat_map(|slot|
        (0..request.context.source.edges.len()).map(move |edge|
            word::Variable::Survival { slot, population: Location::Edge(edge) })
        .chain(std::iter::once(word::Variable::Survival { slot,
            population: Location::Ancestral(request.context.source.root) })))
        .chain((0..mask.len()).map(word::Variable::OriginalGamma)).collect::<Vec<_>>();
    if variables.len() != dimension || populations > 32 {
        return Err(Error::Internal("CONTROLLED_WORD_VARIABLE_BANK"));
    }
    let mut output = BTreeMap::new();
    for register_index in 0..assignments {
        let stage = Stage::Register(register_index);
        let initial = snapshot(request, register_index)?;
        let weight = register_weight(request, &initial, dimension, &mut budget, stage)?;
        let mut child = request.clone();
        child.initial = word::Initial::Conditional(initial.clone());
        for (hybrid, forced) in mask.iter().enumerate() {
            if forced.is_some() { child.common[hybrid] = false; }
        }
        budget.work.conditional_requests = add(budget.work.conditional_requests, 1, stage,
            LimitKind::ConditionalRequests, budget.limits.conditional_requests)?;
        let table = match word::word_row(&child) {
            Ok(word::Decision::Table(table)) => table,
            Ok(word::Decision::Unknown(original_limit)) =>
                return Err(Error::ChildUnknown { register_index, original_limit }),
            Err(original_error) => return Err(Error::ChildFailure { register_index, original_error }),
        };
        if table.variables != variables { return Err(Error::Internal("CONTROLLED_WORD_CHILD_BANK")); }
        budget.work.child_queries = add(budget.work.child_queries, table.work.queries, stage,
            LimitKind::ChildQueries, budget.limits.child_queries)?;
        budget.work.child_branches = add(budget.work.child_branches, table.work.branches, stage,
            LimitKind::ChildBranches, budget.limits.child_branches)?;
        budget.work.child_term_products = add(budget.work.child_term_products, table.work.term_products,
            stage, LimitKind::ChildTermProducts, budget.limits.child_term_products)?;
        for transition in table.transitions {
            if transition.witness.register != initial.register || transition.view.register != initial.register
                || epoch::selected_view(&request.context, &transition.witness).map_err(Error::Internal)? != transition.view {
                return Err(Error::Internal("CONTROLLED_WORD_RANGE_REGISTER"));
            }
            budget.polynomial(&transition.polynomial, dimension, stage)?;
            let specialized = substitute_transition(&transition.polynomial, mask, &mut budget, stage)?;
            let polynomial = budget.multiply(&weight, &specialized, stage)?;
            accumulate(&mut output, Transition { view: transition.view,
                witness: transition.witness, polynomial }, &mut budget, stage)?;
        }
    }
    let mut mass = Polynomial::zero(dimension);
    for transition in output.values() {
        for (powers, coefficient) in &transition.polynomial.terms {
            budget.term(&mut mass, powers.clone(), coefficient.clone(), Stage::Output)?;
        }
    }
    if mass != Polynomial::one(dimension) {
        return Err(Error::Internal("CONTROLLED_WORD_FORMAL_MASS"));
    }
    Ok(Table { original: request, mask, variables,
        transitions: output.into_values().collect(), work: budget.work })
}
