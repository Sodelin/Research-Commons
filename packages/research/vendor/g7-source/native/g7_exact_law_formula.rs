//! Pure exact-real G7 winning-formula frontend; SOURCE ONLY, not compiled.
//!
//! Reuses parity_solver::polynomial::Polynomial and its exact Rational type.
//! No solver, process, filesystem, parser, transport or runtime-record writer.
//! Returned formulas are declarations about ONE SUPPLIED finite model family.
//! Source census/admission, effective coefficients, parser/executable refinement,
//! QE proof and history-relative algebraic policy selection remain separate.
//!
//! Quantifier order is H(h) OR exists action, forall response, W(h+response).
//! Each source copy has ONE parameter bank for the ENTIRE history. Different
//! competing source copies have distinct banks. Actions never see those banks.
//! The built-in PATH resource region is a finite union of downward rectangles
//! over executed calls and unions of positive original rows/touched original IDs.
//! Hence deletion preserves legality. The affine rank bound is D = rows * obs,
//! including varying stochastic channels. It is not the pooled-row k bound.
#![forbid(unsafe_code)]

use parity_solver::{q, Rational};
use parity_solver::polynomial::Polynomial;
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Relation { Equal, Nonnegative, Positive }

/// Rational-coefficient, quantifier-free predicate in a declared local scope.
/// The first C coordinates are the C declared algebraic constants; subsequent
/// coordinates are the local source parameters OR local action parameters.
#[derive(Clone, Debug)]
pub enum Predicate {
    Truth(bool),
    Atom(Relation, Polynomial),
    Not(Box<Predicate>),
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
}

#[derive(Clone, Debug)]
pub struct AlgebraicConstant {
    /// A univariate rational polynomial, not an assumed oracle root.
    pub polynomial: Polynomial,
    /// The selected root must be STRICTLY between these rational endpoints.
    pub lower: Rational,
    pub upper: Rational,
}

#[derive(Clone, Debug)]
pub struct SourceModel {
    pub parameter_count: usize,
    pub target: usize,
    pub domain: Predicate,
    /// Row-major [original row][base observation], exactly D polynomials.
    pub base: Vec<Polynomial>,
}

#[derive(Clone, Debug)]
pub enum Measurement {
    /// [original row][base observation][output]. Coefficients are DERIVED as
    /// weight(row) * channel(row,observation,output), with stochasticity guarded.
    StochasticChannels(Vec<Vec<Vec<Polynomial>>>),
    /// Separate normalized menu choice BEFORE biological observation.
    /// Base coordinates are [row][menu][menu outcome], not one pooled PMF.
    /// Original row support/cost remains determined by ActionCase.weights.
    StochasticMenuChannels {
        menu_outcomes: Vec<usize>,
        /// [original row][menu], nonnegative with each row's sum equal1.
        menu_weights: Vec<Vec<Polynomial>>,
        /// [original row][menu][menu outcome][output], stochastic in output.
        channels: Vec<Vec<Vec<Vec<Polynomial>>>>,
    },
    /// A declared affine response specification [output][base coordinate].
    /// This variant is NOT automatically an actual randomized source programme.
    /// The returned query records its case index as a mandatory semantic join.
    /// Coefficients on absent original support rows are guarded to be zero.
    SuppliedAffine {
        coefficients: Vec<Vec<Polynomial>>,
        offset: Vec<Polynomial>,
    },
}

#[derive(Clone, Debug)]
pub struct ActionCase {
    pub parameter_count: usize,
    pub output_count: usize,
    pub allowed: Predicate,
    /// Exact positive original-row support. Duplicate IDs are invalid.
    pub support: Vec<usize>,
    /// One polynomial for EVERY original row, including zeros outside support.
    pub weights: Vec<Polynomial>,
    pub measurement: Measurement,
}

#[derive(Clone, Debug)]
pub struct Problem {
    pub original_hybrid_count: usize,
    /// Literal deterministic forcing records in ORIGINAL row order. Every
    /// record has original_hybrid_count slots. No extra IDs for channel modes.
    /// Row IDs are positions. Equal masks at distinct positions retain their
    /// own channels and row costs; no mask-value quotient is performed.
    pub rows: Vec<Vec<Option<bool>>>,
    pub base_observations: usize,
    pub target_count: usize,
    pub constants: Vec<AlgebraicConstant>,
    pub models: Vec<SourceModel>,
    pub actions: Vec<ActionCase>,
}

/// One downward rectangle in the finite discrete PATH resource state.
/// A finite union of these is still deletion closed. Arbitrary finite downsets
/// of these row/site/call coordinates can be represented by their maximal states.
/// These are not unrestricted value-dependent or irreversible resource updates.
#[derive(Clone, Debug)]
pub struct ResourceCeiling {
    pub calls: usize,
    pub rows: usize,
    pub sites: usize,
    pub allowed_rows: Option<Vec<usize>>,
    pub allowed_sites: Option<Vec<usize>>,
}

#[derive(Clone, Debug)]
pub struct PathBudget {
    /// At least one region is required; every region contains the zero state.
    pub regions: Vec<ResourceCeiling>,
}

impl PathBudget {
    pub fn rectangular(calls: usize, rows: usize, sites: usize) -> Self {
        Self { regions: vec![ResourceCeiling {
            calls, rows, sites, allowed_rows: None, allowed_sites: None,
        }] }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub input_units: usize,
    pub ast_nodes: usize,
    pub symbols: usize,
    pub polynomial_terms: usize,
    pub exponent: usize,
    pub rational_bits: u64,
    pub recursion_depth: usize,
    pub rendered_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            input_units: 1_000_000, ast_nodes: 1_000_000, symbols: 100_000,
            polynomial_terms: 100_000, exponent: 1_000_000,
            rational_bits: 65_536, recursion_depth: 32,
            rendered_bytes: 16 * 1024 * 1024,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    /// An UNKNOWN/unavailable construction outcome, NEVER a losing budget.
    Limit(&'static str),
}

type Result<T> = std::result::Result<T, Error>;
type TermId = usize;
type FormulaId = usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Symbol(usize);

impl Symbol {
    pub fn index(self) -> usize { self.0 }
    /// Generated safe backend name. No caller text is evaluated as source.
    pub fn wolfram_name(self) -> String { format!("g7v{}", self.0) }
}

#[derive(Clone, Debug)]
enum Term {
    Number(Rational),
    Variable(Symbol),
    Sum(Vec<TermId>),
    Product(Vec<TermId>),
    Power(TermId, usize),
}

#[derive(Clone, Debug)]
enum Formula {
    Truth(bool),
    Compare(Relation, TermId, TermId),
    Not(FormulaId),
    And(Vec<FormulaId>),
    Or(Vec<FormulaId>),
    Exists(Vec<Symbol>, FormulaId),
    ForAll(Vec<Symbol>, FormulaId),
}

#[derive(Debug)]
struct Arena {
    limits: Limits,
    terms: Vec<Term>,
    formulas: Vec<Formula>,
    variable_terms: Vec<TermId>,
}

impl Arena {
    fn new(limits: Limits) -> Result<Self> {
        if limits.ast_nodes < 4 || limits.recursion_depth == 0 {
            return Err(Error::Limit("INITIAL_ARENA_OR_DEPTH"));
        }
        Ok(Self {
            limits,
            terms: vec![Term::Number(q(0,1)), Term::Number(q(1,1))],
            formulas: vec![Formula::Truth(true), Formula::Truth(false)],
            variable_terms: Vec::new(),
        })
    }
    fn room(&self) -> Result<()> {
        let n = self.terms.len().checked_add(self.formulas.len())
            .ok_or(Error::Limit("AST_SIZE_OVERFLOW"))?;
        if n >= self.limits.ast_nodes { Err(Error::Limit("AST_NODES")) } else { Ok(()) }
    }
    fn term(&mut self, node: Term) -> Result<TermId> {
        self.room()?;
        self.terms.try_reserve(1).map_err(|_| Error::Limit("TERM_ALLOCATION"))?;
        let id = self.terms.len(); self.terms.push(node); Ok(id)
    }
    fn formula(&mut self, node: Formula) -> Result<FormulaId> {
        self.room()?;
        self.formulas.try_reserve(1).map_err(|_| Error::Limit("FORMULA_ALLOCATION"))?;
        let id = self.formulas.len(); self.formulas.push(node); Ok(id)
    }
    fn fresh(&mut self, count: usize) -> Result<Vec<Symbol>> {
        let next = self.variable_terms.len().checked_add(count)
            .ok_or(Error::Limit("SYMBOL_COUNT_OVERFLOW"))?;
        if next > self.limits.symbols { return Err(Error::Limit("SYMBOLS")); }
        self.variable_terms.try_reserve(count).map_err(|_| Error::Limit("SYMBOL_ALLOCATION"))?;
        let mut out = Vec::new();
        out.try_reserve(count).map_err(|_| Error::Limit("SYMBOL_ALLOCATION"))?;
        for _ in 0..count {
            let symbol = Symbol(self.variable_terms.len());
            let id = self.term(Term::Variable(symbol))?;
            self.variable_terms.push(id); out.push(symbol);
        }
        Ok(out)
    }
    fn variable(&self, symbol: Symbol) -> TermId { self.variable_terms[symbol.0] }
    fn number(&mut self, value: &Rational) -> Result<TermId> {
        if value == &q(0,1) { Ok(0) }
        else if value == &q(1,1) { Ok(1) }
        else { self.term(Term::Number(value.clone())) }
    }
    fn sum(&mut self, values: Vec<TermId>) -> Result<TermId> {
        let mut xs: Vec<_> = values.into_iter().filter(|x| *x != 0).collect();
        if xs.is_empty() { Ok(0) } else if xs.len() == 1 { Ok(xs.remove(0)) }
        else { self.term(Term::Sum(xs)) }
    }
    fn product(&mut self, values: Vec<TermId>) -> Result<TermId> {
        if values.contains(&0) { return Ok(0); }
        let mut xs: Vec<_> = values.into_iter().filter(|x| *x != 1).collect();
        if xs.is_empty() { Ok(1) } else if xs.len() == 1 { Ok(xs.remove(0)) }
        else { self.term(Term::Product(xs)) }
    }
    fn power(&mut self, value: TermId, exponent: usize) -> Result<TermId> {
        if exponent == 0 { Ok(1) } else if exponent == 1 { Ok(value) }
        else { self.term(Term::Power(value, exponent)) }
    }
    fn compare(&mut self, relation: Relation, lhs: TermId, rhs: TermId) -> Result<FormulaId> {
        self.formula(Formula::Compare(relation,lhs,rhs))
    }
    fn not(&mut self, value: FormulaId) -> Result<FormulaId> {
        match &self.formulas[value] {
            Formula::Truth(b) => Ok(if *b {1} else {0}),
            Formula::Not(inner) => Ok(*inner),
            _ => self.formula(Formula::Not(value)),
        }
    }
    fn and(&mut self, values: Vec<FormulaId>) -> Result<FormulaId> {
        if values.contains(&1) { return Ok(1); }
        let mut xs: Vec<_> = values.into_iter().filter(|x| *x != 0).collect();
        if xs.is_empty() { Ok(0) } else if xs.len() == 1 { Ok(xs.remove(0)) }
        else { self.formula(Formula::And(xs)) }
    }
    fn or(&mut self, values: Vec<FormulaId>) -> Result<FormulaId> {
        if values.contains(&0) { return Ok(0); }
        let mut xs: Vec<_> = values.into_iter().filter(|x| *x != 1).collect();
        if xs.is_empty() { Ok(1) } else if xs.len() == 1 { Ok(xs.remove(0)) }
        else { self.formula(Formula::Or(xs)) }
    }
    fn exists(&mut self, vars: Vec<Symbol>, body: FormulaId) -> Result<FormulaId> {
        if vars.is_empty() { Ok(body) } else { self.formula(Formula::Exists(vars,body)) }
    }
    fn forall(&mut self, vars: Vec<Symbol>, body: FormulaId) -> Result<FormulaId> {
        if vars.is_empty() { Ok(body) } else { self.formula(Formula::ForAll(vars,body)) }
    }
    fn polynomial(&mut self, p: &Polynomial, env: &[Symbol]) -> Result<TermId> {
        if p.dimension != env.len() { return Err(Error::Invalid("INTERNAL_POLYNOMIAL_SCOPE")); }
        let mut summands = Vec::new();
        for (powers,coefficient) in &p.terms {
            if powers.len() != env.len() { return Err(Error::Invalid("POLYNOMIAL_ARITY")); }
            let mut factors = vec![self.number(coefficient)?];
            for (index,power) in powers.iter().enumerate() {
                if *power != 0 {
                    let value = self.variable(env[index]);
                    factors.push(self.power(value,*power)?);
                }
            }
            summands.push(self.product(factors)?);
        }
        self.sum(summands)
    }
    fn predicate(&mut self, p: &Predicate, env: &[Symbol]) -> Result<FormulaId> {
        match p {
            Predicate::Truth(b) => Ok(if *b {0} else {1}),
            Predicate::Atom(relation,poly) => {
                let lhs = self.polynomial(poly,env)?;
                self.compare(*relation,lhs,0)
            }
            Predicate::Not(inner) => {
                let value = self.predicate(inner,env)?; self.not(value)
            }
            Predicate::And(parts) | Predicate::Or(parts) => {
                let mut ids = Vec::new();
                for part in parts { ids.push(self.predicate(part,env)?); }
                if matches!(p,Predicate::And(_)) { self.and(ids) } else { self.or(ids) }
            }
        }
    }
}

struct Validation {
    limits: Limits,
    units: usize,
}

impl Validation {
    fn charge(&mut self, amount: usize) -> Result<()> {
        self.units = self.units.checked_add(amount).ok_or(Error::Limit("INPUT_SIZE_OVERFLOW"))?;
        if self.units > self.limits.input_units { Err(Error::Limit("INPUT_UNITS")) } else { Ok(()) }
    }
    fn rational(&mut self, value: &Rational) -> Result<()> {
        self.charge(1)?;
        if value.denom() <= q(0,1).numer() { return Err(Error::Invalid("RATIONAL_DENOMINATOR")); }
        if value.numer().bits().max(value.denom().bits()) > self.limits.rational_bits {
            return Err(Error::Limit("RATIONAL_BITS"));
        }
        Ok(())
    }
    fn polynomial(&mut self, p: &Polynomial, dimension: usize) -> Result<()> {
        self.charge(1)?;
        if p.dimension != dimension { return Err(Error::Invalid("POLYNOMIAL_DIMENSION")); }
        if p.terms.len() > self.limits.polynomial_terms { return Err(Error::Limit("POLYNOMIAL_TERMS")); }
        for (powers,coefficient) in &p.terms {
            self.charge(powers.len())?;
            if powers.len() != dimension { return Err(Error::Invalid("POLYNOMIAL_ARITY")); }
            if powers.iter().any(|x| *x > self.limits.exponent) {
                return Err(Error::Limit("POLYNOMIAL_EXPONENT"));
            }
            self.rational(coefficient)?;
        }
        Ok(())
    }
    fn predicate(&mut self, p: &Predicate, dimension: usize) -> Result<()> {
        let mut work = vec![(p,0usize)];
        while let Some((p,depth)) = work.pop() {
            self.charge(1)?;
            if depth >= self.limits.recursion_depth || depth >= 128 {
                return Err(Error::Limit("PREDICATE_DEPTH"));
            }
            match p {
                Predicate::Truth(_) => (),
                Predicate::Atom(_,poly) => self.polynomial(poly,dimension)?,
                Predicate::Not(inner) => work.push((inner,depth+1)),
                Predicate::And(xs) | Predicate::Or(xs) => {
                    self.charge(xs.len())?;
                    for x in xs { work.push((x,depth+1)); }
                }
            }
        }
        Ok(())
    }
    fn ids(&mut self, ids: &[usize], bound: usize) -> Result<()> {
        self.charge(ids.len())?;
        let mut seen = BTreeSet::new();
        for id in ids {
            if *id >= bound { return Err(Error::Invalid("RESOURCE_OR_SUPPORT_ID")); }
            if !seen.insert(*id) { return Err(Error::Invalid("DUPLICATE_RESOURCE_OR_SUPPORT_ID")); }
        }
        Ok(())
    }
}

fn validate(problem: &Problem, budget: &PathBudget, prefix: &[usize], limits: Limits)
    -> Result<usize> {
    if problem.target_count == 0 { return Err(Error::Invalid("EMPTY_TARGET_ALPHABET")); }
    if problem.base_observations == 0 { return Err(Error::Invalid("EMPTY_BASE_OBSERVATION_ALPHABET")); }
    if budget.regions.is_empty() { return Err(Error::Invalid("EMPTY_RESOURCE_REGION")); }
    let dimension = problem.rows.len().checked_mul(problem.base_observations)
        .ok_or(Error::Limit("BASE_DIMENSION_OVERFLOW"))?;
    let mut v = Validation {limits,units:0};
    v.charge(dimension)?;
    v.charge(problem.original_hybrid_count)?;
    v.charge(problem.rows.len())?;
    for row in &problem.rows {
        v.charge(row.len())?;
        if row.len() != problem.original_hybrid_count { return Err(Error::Invalid("ORIGINAL_ROW_ID_ARITY")); }
    }
    v.charge(problem.constants.len())?;
    for constant in &problem.constants {
        v.polynomial(&constant.polynomial,1)?;
        v.rational(&constant.lower)?; v.rational(&constant.upper)?;
        if constant.lower >= constant.upper { return Err(Error::Invalid("ROOT_INTERVAL_ORDER")); }
    }
    v.charge(problem.models.len())?;
    for model in &problem.models {
        v.charge(model.parameter_count)?;
        if model.target >= problem.target_count { return Err(Error::Invalid("MODEL_TARGET")); }
        let scope = problem.constants.len().checked_add(model.parameter_count)
            .ok_or(Error::Limit("SOURCE_SCOPE_OVERFLOW"))?;
        v.predicate(&model.domain,scope)?;
        if model.base.len() != dimension { return Err(Error::Invalid("MODEL_BASE_DIMENSION")); }
        for poly in &model.base { v.polynomial(poly,scope)?; }
    }
    v.charge(problem.actions.len())?;
    for action in &problem.actions {
        v.charge(action.parameter_count)?;
        v.charge(action.output_count)?;
        v.ids(&action.support,problem.rows.len())?;
        let scope = problem.constants.len().checked_add(action.parameter_count)
            .ok_or(Error::Limit("ACTION_SCOPE_OVERFLOW"))?;
        v.predicate(&action.allowed,scope)?;
        if action.weights.len() != problem.rows.len() { return Err(Error::Invalid("ACTION_WEIGHT_LENGTH")); }
        for poly in &action.weights { v.polynomial(poly,scope)?; }
        match &action.measurement {
            Measurement::StochasticChannels(channels) => {
                if channels.len() != problem.rows.len() { return Err(Error::Invalid("CHANNEL_ROW_LENGTH")); }
                for row in channels {
                    if row.len() != problem.base_observations { return Err(Error::Invalid("CHANNEL_OBSERVATION_LENGTH")); }
                    for observation in row {
                        if observation.len() != action.output_count { return Err(Error::Invalid("CHANNEL_OUTPUT_LENGTH")); }
                        for poly in observation { v.polynomial(poly,scope)?; }
                    }
                }
            }
            Measurement::StochasticMenuChannels {menu_outcomes,menu_weights,channels} => {
                v.charge(menu_outcomes.len())?;
                let mut observations = 0usize;
                for count in menu_outcomes {
                    if *count == 0 { return Err(Error::Invalid("MENU_EMPTY_OUTCOME_ALPHABET")); }
                    observations = observations.checked_add(*count)
                        .ok_or(Error::Limit("MENU_BASE_DIMENSION_OVERFLOW"))?;
                }
                if menu_outcomes.is_empty() || observations != problem.base_observations {
                    return Err(Error::Invalid("MENU_BASE_OBSERVATION_LENGTH"));
                }
                if menu_weights.len() != problem.rows.len() || channels.len() != problem.rows.len() {
                    return Err(Error::Invalid("MENU_CHANNEL_ROW_LENGTH"));
                }
                for (weights,menus) in menu_weights.iter().zip(channels) {
                    v.charge(weights.len())?;
                    v.charge(menus.len())?;
                    if weights.len() != menu_outcomes.len() || menus.len() != menu_outcomes.len() {
                        return Err(Error::Invalid("MENU_CHANNEL_MENU_LENGTH"));
                    }
                    for (menu,observations) in menus.iter().enumerate() {
                        v.polynomial(&weights[menu],scope)?;
                        v.charge(observations.len())?;
                        if observations.len() != menu_outcomes[menu] {
                            return Err(Error::Invalid("MENU_CHANNEL_OBSERVATION_LENGTH"));
                        }
                        for outputs in observations {
                            v.charge(outputs.len())?;
                            if outputs.len() != action.output_count {
                                return Err(Error::Invalid("MENU_CHANNEL_OUTPUT_LENGTH"));
                            }
                            for polynomial in outputs { v.polynomial(polynomial,scope)?; }
                        }
                    }
                }
            }
            Measurement::SuppliedAffine {coefficients,offset} => {
                if coefficients.len() != action.output_count || offset.len() != action.output_count {
                    return Err(Error::Invalid("AFFINE_OUTPUT_LENGTH"));
                }
                for row in coefficients {
                    if row.len() != dimension { return Err(Error::Invalid("AFFINE_BASE_DIMENSION")); }
                    for poly in row { v.polynomial(poly,scope)?; }
                }
                for poly in offset { v.polynomial(poly,scope)?; }
            }
        }
    }
    v.charge(budget.regions.len())?;
    for region in &budget.regions {
        if let Some(ids) = &region.allowed_rows { v.ids(ids,problem.rows.len())?; }
        if let Some(ids) = &region.allowed_sites { v.ids(ids,problem.original_hybrid_count)?; }
    }
    v.charge(prefix.len())?;
    if prefix.iter().any(|index| *index >= problem.actions.len()) {
        return Err(Error::Invalid("PREFIX_ACTION_CASE"));
    }
    Ok(dimension)
}

#[derive(Clone, Debug, Default)]
struct Resources {
    calls: usize,
    rows: BTreeSet<usize>,
    sites: BTreeSet<usize>,
}

impl Resources {
    fn extended(&self, problem: &Problem, action: &ActionCase) -> Result<Self> {
        let mut next = self.clone();
        next.calls = next.calls.checked_add(1).ok_or(Error::Limit("CALL_COUNT_OVERFLOW"))?;
        for row in &action.support {
            next.rows.insert(*row);
            for (id,bit) in problem.rows[*row].iter().enumerate() {
                if bit.is_some() { next.sites.insert(id); }
            }
        }
        Ok(next)
    }
    fn fits(&self, c: &ResourceCeiling) -> bool {
        self.calls <= c.calls && self.rows.len() <= c.rows && self.sites.len() <= c.sites
            && c.allowed_rows.as_ref().map_or(true, |ids| self.rows.iter().all(|id| ids.contains(id)))
            && c.allowed_sites.as_ref().map_or(true, |ids| self.sites.iter().all(|id| ids.contains(id)))
    }
    fn affordable(&self, budget: &PathBudget) -> bool {
        budget.regions.iter().any(|c| self.fits(c))
    }
    fn remaining(&self, budget: &PathBudget) -> usize {
        budget.regions.iter().filter(|c| self.fits(c))
            .map(|c| c.calls - self.calls).max().unwrap_or(0)
    }
}

#[derive(Clone, Debug)]
struct ActionValue {
    parameters: Vec<Symbol>,
    allowed: FormulaId,
    coefficients: Vec<Vec<TermId>>,
    offset: Vec<TermId>,
}

#[derive(Clone, Debug)]
struct Step {
    action: ActionValue,
    response: Vec<Symbol>,
}

#[derive(Clone, Debug)]
pub struct HistorySymbols {
    pub case_index: usize,
    pub action_parameters: Vec<Symbol>,
    pub response: Vec<Symbol>,
}

#[derive(Clone, Debug)]
pub struct ActionFibreSymbols {
    pub case_index: usize,
    pub action_parameters: Vec<Symbol>,
    /// Backend relation of these FREE action coordinates to all free history
    /// coordinates. This is not an algebraic selector or executable next action.
    pub affordable: bool,
    pub enabled_in_retained_horizon: bool,
}

#[derive(Debug)]
struct ActionFibre {
    symbols: ActionFibreSymbols,
    formula: FormulaId,
}

#[derive(Clone, Copy, Debug)]
pub enum QueryKind {
    /// Must be TRUE before interpreting ANY other query. False means invalid
    /// algebraic-constant specification, not a negative design/budget result.
    ConstantsWellDefined,
    LegalHistory,
    ReachableHistory,
    HomogeneousHistory,
    WinningContinuation,
    /// Index into action_fibres(), not a caller-supplied backend identifier.
    WinningAction(usize),
}

/// This object immutably borrows BOTH the complete problem and budget. A caller
/// must separately authenticate external bytes/origin; a Rust borrow is not an
/// origin receipt. No mathematical success/NO is returned by this component.
#[derive(Debug)]
pub struct Compiled<'a> {
    problem: &'a Problem,
    budget: &'a PathBudget,
    arena: Arena,
    constants_valid: FormulaId,
    legal_history: FormulaId,
    reachable_history: FormulaId,
    homogeneous_history: FormulaId,
    /// For each original model: valid root tuple implies NO local bank fits
    /// the ENTIRE history. Each predicate closes its constant variables.
    /// Entries retain the exact Problem.models order.
    excluded_models: Vec<FormulaId>,
    winning: FormulaId,
    fibres: Vec<ActionFibre>,
    history_symbols: Vec<HistorySymbols>,
    constant_symbols: Vec<Symbol>,
    retained_horizon: usize,
    supplied_affine_cases: Vec<usize>,
}

impl<'a> Compiled<'a> {
    pub fn source_input(&self) -> &'a Problem { self.problem }
    pub fn path_budget(&self) -> &'a PathBudget { self.budget }
    pub fn history_symbols(&self) -> &[HistorySymbols] { &self.history_symbols }
    pub fn constant_symbols(&self) -> &[Symbol] { &self.constant_symbols }
    pub fn retained_horizon(&self) -> usize { self.retained_horizon }
    /// Every listed case still needs the actual-programme affine identity, not
    /// a caller Boolean or dictionary hash. Stochastic maps are derived directly.
    pub fn supplied_affine_cases(&self) -> &[usize] { &self.supplied_affine_cases }
    pub fn action_fibres(&self) -> Vec<&ActionFibreSymbols> {
        self.fibres.iter().map(|f| &f.symbols).collect()
    }
    pub fn ast_size(&self) -> (usize,usize) { (self.arena.terms.len(),self.arena.formulas.len()) }
    pub fn wolfram_query(&self, kind: QueryKind) -> Result<String> {
        let formula = match kind {
            QueryKind::ConstantsWellDefined => self.constants_valid,
            QueryKind::LegalHistory => self.legal_history,
            QueryKind::ReachableHistory => self.reachable_history,
            QueryKind::HomogeneousHistory => self.homogeneous_history,
            QueryKind::WinningContinuation => self.winning,
            QueryKind::WinningAction(index) => self.fibres.get(index)
                .ok_or(Error::Invalid("ACTION_FIBRE_INDEX"))?.formula,
        };
        self.arena.render(formula)
    }
}


/// The requested mathematical assertion, rather than an interpretation of
/// FALSE from an unguarded/vacuous conditional query. A positive losing
/// assertion negates WinningContinuation only INSIDE the prerequisite guards.
#[derive(Clone, Copy, Debug)]
pub enum AssertionKind {
    HomogeneousHistory,
    /// Every consistent supplied source piece has this target code.
    /// At an unreachable history this is vacuous; Reachable is required for an
    /// actual identifying leaf. This descriptor neither selects nor proves it.
    IdentifiedTarget(usize),
    WinningContinuation,
    LosingContinuation,
    WinningAction(usize),
}

/// Reachable adds mathematical source consistency at this exact free history.
/// Neither variant authenticates a physical transcript or native result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssertionHistory {
    Legal,
    Reachable,
}

/// Generated query bound in-process to its exact immutable problem, PATH budget,
/// finite case path and free history/action symbol order. This is NOT a proof,
/// backend result, physical-origin receipt or selected policy/action.
#[derive(Debug)]
pub struct IssuedAssertion<'q, 'a> {
    compiled: &'q Compiled<'a>,
    kind: AssertionKind,
    history: AssertionHistory,
    document: String,
    actual_free: Vec<Symbol>,
}

impl<'q, 'a> IssuedAssertion<'q, 'a> {
    pub fn compiled(&self) -> &'q Compiled<'a> { self.compiled }
    pub fn kind(&self) -> AssertionKind { self.kind }
    pub fn history_scope(&self) -> AssertionHistory { self.history }
    pub fn document(&self) -> &str { &self.document }
    /// Exact syntactic free variables found in the generated guarded AST.
    pub fn actual_free_symbols(&self) -> &[Symbol] { &self.actual_free }
    /// Declared context can include symbols absent after Boolean simplification.
    /// TRUE/FALSE must not be mistaken for a result at an unrelated free point.
    pub fn has_free_context(&self) -> bool {
        self.compiled.history_symbols.iter().any(|h|
            !h.action_parameters.is_empty() || !h.response.is_empty())
            || self.candidate_action().is_some_and(|a| !a.action_parameters.is_empty())
    }
    pub fn candidate_action(&self) -> Option<&ActionFibreSymbols> {
        match self.kind {
            AssertionKind::WinningAction(index) =>
                self.compiled.fibres.get(index).map(|f| &f.symbols),
            _ => None,
        }
    }
}

impl<'a> Compiled<'a> {
    /// Render ConstantsWellDefined AND LegalHistory AND requested assertion;
    /// Reachable additionally conjoins ReachableHistory. All FREE history and
    /// candidate-action coordinates remain FREE, including transcendental ones.
    ///
    /// A TRUE losing assertion therefore includes valid constants and legal
    /// history; it cannot arise solely from an illegal prefix or missing roots.
    /// FALSE is inconclusive for this interface, never the opposite assertion,
    /// a budget-NO or an execution failure. A disabled action fibre stays FALSE.
    ///
    /// IdentifiedTarget(t) excludes EVERY consistent model with a different
    /// target. It does not identify one parameter point. Use Reachable to
    /// exclude a vacuous label on an impossible history; a Legal-only assertion
    /// remains merely universal over any consistent supplied pieces. Even with
    /// Reachable, actual transcript/result origin and source/target transport
    /// remain separate. No algebraic selector is supplied by rendering a claim.
    ///
    /// This adds no backend, result parser, QE/AST proof, history specialization,
    /// executable selector, source admission or runtime record writer.
    pub fn wolfram_assertion<'q>(
        &'q self, kind: AssertionKind, history: AssertionHistory,
    ) -> Result<IssuedAssertion<'q, 'a>> {
        fn append(out: &mut String, text: &str, limit: usize) -> Result<()> {
            let next = out.len().checked_add(text.len())
                .ok_or(Error::Limit("ASSERTION_RENDER_SIZE_OVERFLOW"))?;
            if next > limit { return Err(Error::Limit("ASSERTION_RENDER_BYTES")); }
            out.try_reserve(text.len())
                .map_err(|_| Error::Limit("ASSERTION_RENDER_ALLOCATION"))?;
            out.push_str(text);
            Ok(())
        }
        fn body(document: &str) -> Result<&str> {
            document.strip_prefix("Resolve[")
                .and_then(|s| s.strip_suffix(",Reals]"))
                .ok_or(Error::Invalid("INTERNAL_QUERY_DOCUMENT"))
        }
        let (claims, negate) = match kind {
            AssertionKind::HomogeneousHistory => (vec![self.homogeneous_history], false),
            AssertionKind::WinningContinuation => (vec![self.winning], false),
            AssertionKind::LosingContinuation => (vec![self.winning], true),
            AssertionKind::WinningAction(index) => (
                vec![self.fibres.get(index)
                    .ok_or(Error::Invalid("ACTION_FIBRE_INDEX"))?.formula], false),
            AssertionKind::IdentifiedTarget(target) => {
                if target >= self.problem.target_count {
                    return Err(Error::Invalid("ASSERTION_TARGET_ID"));
                }
                if self.excluded_models.len() != self.problem.models.len() {
                    return Err(Error::Invalid("INTERNAL_MODEL_POSSIBILITY_ORDER"));
                }
                let mut exclusions = Vec::new();
                exclusions.try_reserve(self.problem.models.len())
                    .map_err(|_| Error::Limit("TARGET_ASSERTION_ALLOCATION"))?;
                for (model,excluded) in self.problem.models.iter().zip(&self.excluded_models) {
                    if model.target != target { exclusions.push(*excluded); }
                }
                // Every DIFFERENT-target model must be excluded at the
                // declared root tuple. Equal-response/different-target pieces
                // remain separate. No target_count-sized loop or allocation.
                (exclusions, false)
            }
        };
        let mut declared = Vec::new();
        let mut context_count = 0usize;
        for h in &self.history_symbols {
            context_count = context_count.checked_add(h.action_parameters.len())
                .and_then(|n| n.checked_add(h.response.len()))
                .ok_or(Error::Limit("QUERY_CONTEXT_SIZE"))?;
        }
        if let AssertionKind::WinningAction(index) = kind {
            context_count = context_count.checked_add(self.fibres[index].symbols.action_parameters.len())
                .ok_or(Error::Limit("QUERY_CONTEXT_SIZE"))?;
        }
        declared.try_reserve(context_count)
            .map_err(|_| Error::Limit("QUERY_CONTEXT_ALLOCATION"))?;
        for h in &self.history_symbols {
            declared.extend_from_slice(&h.action_parameters);
            declared.extend_from_slice(&h.response);
        }
        if let AssertionKind::WinningAction(index) = kind {
            declared.extend_from_slice(&self.fibres[index].symbols.action_parameters);
        }
        let mut roots = if history == AssertionHistory::Reachable {
            vec![self.constants_valid,self.legal_history,self.reachable_history]
        } else {
            vec![self.constants_valid,self.legal_history]
        };
        roots.try_reserve(claims.len())
            .map_err(|_| Error::Limit("ASSERTION_SCOPE_ROOT_ALLOCATION"))?;
        roots.extend_from_slice(&claims);
        let actual_free = self.arena.query_free_symbols(&roots,&declared)?;
        let limit = self.arena.limits.rendered_bytes;
        let mut document = String::new();
        append(&mut document, "Resolve[And[", limit)?;
        // Render one child at a time; temporary documents never reach a writer.
        // Each child and the complete combined document obey rendered_bytes.
        for guard in [self.constants_valid, self.legal_history] {
            let child = self.arena.render(guard)?;
            append(&mut document, body(&child)?, limit)?;
            append(&mut document, ",", limit)?;
        }
        if history == AssertionHistory::Reachable {
            let child = self.arena.render(self.reachable_history)?;
            append(&mut document, body(&child)?, limit)?;
            append(&mut document, ",", limit)?;
        }
        if claims.is_empty() { append(&mut document, "True", limit)?; }
        for (index,claim) in claims.iter().enumerate() {
            if index != 0 { append(&mut document, ",", limit)?; }
            if negate { append(&mut document, "Not[", limit)?; }
            let child = self.arena.render(*claim)?;
            append(&mut document, body(&child)?, limit)?;
            if negate { append(&mut document, "]", limit)?; }
        }
        append(&mut document, "],Reals]", limit)?;
        Ok(IssuedAssertion {compiled:self,kind,history,document,actual_free})
    }
}


/// Free-variable audit of the generated AST. This is an implementation check,
/// not a Lean/AST proof or backend decision. It uses the existing construction
/// and rendering ceilings; shared DAGs are traversed with explicit bounded work.
impl Arena {
    fn query_free_symbols(
        &self, roots: &[FormulaId], declared: &[Symbol],
    ) -> Result<Vec<Symbol>> {
        enum Task<'s> {
            Formula(FormulaId),
            Term(TermId),
            Enter(&'s [Symbol]),
            Exit(&'s [Symbol]),
        }
        fn charge(fuel: &mut usize) -> Result<()> {
            *fuel = fuel.checked_sub(1).ok_or(Error::Limit("QUERY_SCOPE_AUDIT_WORK"))?;
            Ok(())
        }
        fn room<'s>(work: &mut Vec<Task<'s>>, count: usize, fuel: usize) -> Result<()> {
            let next = work.len().checked_add(count)
                .ok_or(Error::Limit("QUERY_SCOPE_STACK_OVERFLOW"))?;
            if next > fuel { return Err(Error::Limit("QUERY_SCOPE_AUDIT_WORK")); }
            work.try_reserve(count).map_err(|_| Error::Limit("QUERY_SCOPE_STACK_ALLOCATION"))
        }
        let mut fuel = self.limits.ast_nodes.checked_add(self.limits.symbols)
            .and_then(|n| n.checked_add(self.limits.rendered_bytes))
            .ok_or(Error::Limit("QUERY_SCOPE_LIMIT_OVERFLOW"))?;
        let count = self.variable_terms.len();
        let mut bound = Vec::new();
        bound.try_reserve_exact(count)
            .map_err(|_| Error::Limit("QUERY_SCOPE_BINDER_ALLOCATION"))?;
        bound.resize(count, false);
        let mut allowed = BTreeSet::new();
        for symbol in declared {
            charge(&mut fuel)?;
            if symbol.0 >= count { return Err(Error::Invalid("QUERY_CONTEXT_SYMBOL")); }
            if !allowed.insert(symbol.0) {
                return Err(Error::Invalid("REUSED_QUERY_CONTEXT_SYMBOL"));
            }
        }
        let mut free = BTreeSet::new();
        let mut work = Vec::new();
        room(&mut work, roots.len(), fuel)?;
        for id in roots.iter().rev() { work.push(Task::Formula(*id)); }
        while let Some(task) = work.pop() {
            charge(&mut fuel)?;
            match task {
                Task::Formula(id) => match self.formulas.get(id)
                    .ok_or(Error::Invalid("QUERY_FORMULA_ID"))? {
                    Formula::Truth(_) => (),
                    Formula::Compare(_,lhs,rhs) => {
                        room(&mut work, 2, fuel)?;
                        work.push(Task::Term(*rhs)); work.push(Task::Term(*lhs));
                    }
                    Formula::Not(body) => {
                        room(&mut work, 1, fuel)?; work.push(Task::Formula(*body));
                    }
                    Formula::And(ids) | Formula::Or(ids) => {
                        room(&mut work, ids.len(), fuel)?;
                        for id in ids.iter().rev() { work.push(Task::Formula(*id)); }
                    }
                    Formula::Exists(symbols,body) | Formula::ForAll(symbols,body) => {
                        room(&mut work, 3, fuel)?;
                        work.push(Task::Exit(symbols));
                        work.push(Task::Formula(*body));
                        work.push(Task::Enter(symbols));
                    }
                },
                Task::Term(id) => match self.terms.get(id)
                    .ok_or(Error::Invalid("QUERY_TERM_ID"))? {
                    Term::Number(_) => (),
                    Term::Variable(symbol) => {
                        let is_bound = *bound.get(symbol.0)
                            .ok_or(Error::Invalid("QUERY_VARIABLE_ID"))?;
                        if !is_bound {
                            if !allowed.contains(&symbol.0) {
                                return Err(Error::Invalid("UNBOUND_QUERY_SYMBOL"));
                            }
                            free.insert(symbol.0);
                        }
                    }
                    Term::Sum(ids) | Term::Product(ids) => {
                        room(&mut work, ids.len(), fuel)?;
                        for id in ids.iter().rev() { work.push(Task::Term(*id)); }
                    }
                    Term::Power(value,_) => {
                        room(&mut work, 1, fuel)?; work.push(Task::Term(*value));
                    }
                },
                Task::Enter(symbols) => for symbol in symbols {
                    charge(&mut fuel)?;
                    if allowed.contains(&symbol.0) {
                        return Err(Error::Invalid("BOUND_QUERY_CONTEXT_SYMBOL"));
                    }
                    let slot = bound.get_mut(symbol.0)
                        .ok_or(Error::Invalid("QUERY_BINDER_ID"))?;
                    if *slot { return Err(Error::Invalid("REUSED_QUERY_BINDER_SYMBOL")); }
                    *slot = true;
                },
                Task::Exit(symbols) => for symbol in symbols {
                    charge(&mut fuel)?;
                    let slot = bound.get_mut(symbol.0)
                        .ok_or(Error::Invalid("QUERY_BINDER_ID"))?;
                    if !*slot { return Err(Error::Invalid("QUERY_BINDER_SCOPE")); }
                    *slot = false;
                },
            }
        }
        if bound.iter().any(|b| *b) { return Err(Error::Invalid("QUERY_BINDER_SCOPE")); }
        let mut result = Vec::new();
        result.try_reserve(free.len())
            .map_err(|_| Error::Limit("QUERY_SCOPE_RESULT_ALLOCATION"))?;
        result.extend(free.into_iter().map(Symbol));
        Ok(result)
    }
}

struct Compiler<'a> {
    problem: &'a Problem,
    budget: &'a PathBudget,
    arena: Arena,
    constants: Vec<Symbol>,
    dimension: usize,
}

impl<'a> Compiler<'a> {
    fn environment(&self, local: &[Symbol]) -> Vec<Symbol> {
        self.constants.iter().copied().chain(local.iter().copied()).collect()
    }
    fn constant_roots(&mut self, symbols: &[Symbol]) -> Result<FormulaId> {
        let problem = self.problem;
        let mut all = Vec::new();
        for (constant,symbol) in problem.constants.iter().zip(symbols) {
            let p = self.arena.polynomial(&constant.polynomial,&[*symbol])?;
            all.push(self.arena.compare(Relation::Equal,p,0)?);
            let x = self.arena.variable(*symbol);
            let lower = self.arena.number(&constant.lower)?;
            let upper = self.arena.number(&constant.upper)?;
            all.push(self.arena.compare(Relation::Positive,x,lower)?);
            all.push(self.arena.compare(Relation::Positive,upper,x)?);
        }
        self.arena.and(all)
    }
    fn constants_validity(&mut self) -> Result<FormulaId> {
        let symbols = self.constants.clone();
        let roots = self.constant_roots(&symbols)?;
        let exists = self.arena.exists(symbols.clone(),roots)?;
        let other = self.arena.fresh(symbols.len())?;
        let other_roots = self.constant_roots(&other)?;
        let both = self.arena.and(vec![roots,other_roots])?;
        let no_both = self.arena.not(both)?;
        let mut equalities = Vec::new();
        for (a,b) in symbols.iter().zip(&other) {
            let lhs = self.arena.variable(*a); let rhs = self.arena.variable(*b);
            equalities.push(self.arena.compare(Relation::Equal,lhs,rhs)?);
        }
        let equal = self.arena.and(equalities)?;
        let implies = self.arena.or(vec![no_both,equal])?;
        let variables = symbols.into_iter().chain(other).collect();
        let unique = self.arena.forall(variables,implies)?;
        self.arena.and(vec![exists,unique])
    }
    /// For a valid unique constant tuple this is exactly body. If roots are
    /// missing the implication can be vacuous: the separate prerequisite is
    /// therefore MANDATORY, never a losing-budget or automatic-YES fallback.
    fn conditional_on_constants(&mut self, body: FormulaId) -> Result<FormulaId> {
        let symbols = self.constants.clone();
        let roots = self.constant_roots(&symbols)?;
        let not_roots = self.arena.not(roots)?;
        let implies = self.arena.or(vec![not_roots,body])?;
        self.arena.forall(symbols,implies)
    }
    fn action(&mut self, case_index: usize) -> Result<ActionValue> {
        let problem = self.problem;
        let action = &problem.actions[case_index];
        let parameters = self.arena.fresh(action.parameter_count)?;
        let env = self.environment(&parameters);
        let mut constraints = vec![self.arena.predicate(&action.allowed,&env)?];
        let mut weights = Vec::new();
        for (row,poly) in action.weights.iter().enumerate() {
            let value = self.arena.polynomial(poly,&env)?;
            let rel = if action.support.contains(&row) {Relation::Positive} else {Relation::Equal};
            constraints.push(self.arena.compare(rel,value,0)?);
            weights.push(value);
        }
        let total = self.arena.sum(weights.clone())?;
        constraints.push(self.arena.compare(Relation::Equal,total,1)?);
        let mut coefficients = vec![vec![0;self.dimension];action.output_count];
        let mut offset = vec![0;action.output_count];
        match &action.measurement {
            Measurement::StochasticChannels(channels) => {
                for (row,observations) in channels.iter().enumerate() {
                    for (observation,outputs) in observations.iter().enumerate() {
                        let mut probability_sum = Vec::new();
                        for (output,poly) in outputs.iter().enumerate() {
                            let probability = self.arena.polynomial(poly,&env)?;
                            constraints.push(self.arena.compare(Relation::Nonnegative,probability,0)?);
                            probability_sum.push(probability);
                            let index = row * problem.base_observations + observation;
                            coefficients[output][index] = self.arena.product(vec![weights[row],probability])?;
                        }
                        let total = self.arena.sum(probability_sum)?;
                        constraints.push(self.arena.compare(Relation::Equal,total,1)?);
                    }
                }
            }
            Measurement::StochasticMenuChannels {menu_outcomes,menu_weights,channels} => {
                for (row,menus) in channels.iter().enumerate() {
                    let mut menu_terms = Vec::new();
                    for polynomial in &menu_weights[row] {
                        let probability = self.arena.polynomial(polynomial,&env)?;
                        constraints.push(self.arena.compare(Relation::Nonnegative,probability,0)?);
                        menu_terms.push(probability);
                    }
                    let total = self.arena.sum(menu_terms.clone())?;
                    constraints.push(self.arena.compare(Relation::Equal,total,1)?);
                    let mut start = 0usize;
                    for (menu,observations) in menus.iter().enumerate() {
                        for (observation,outputs) in observations.iter().enumerate() {
                            let mut probability_sum = Vec::new();
                            for (output,polynomial) in outputs.iter().enumerate() {
                                let probability = self.arena.polynomial(polynomial,&env)?;
                                constraints.push(self.arena.compare(Relation::Nonnegative,probability,0)?);
                                probability_sum.push(probability);
                                let index = row * problem.base_observations + start + observation;
                                coefficients[output][index] = self.arena.product(
                                    vec![weights[row],menu_terms[menu],probability])?;
                            }
                            let total = self.arena.sum(probability_sum)?;
                            constraints.push(self.arena.compare(Relation::Equal,total,1)?);
                        }
                        start += menu_outcomes[menu];
                    }
                }
            }
            Measurement::SuppliedAffine {coefficients:polys,offset:constants} => {
                for (output,polys) in polys.iter().enumerate() {
                    for (index,poly) in polys.iter().enumerate() {
                        let value = self.arena.polynomial(poly,&env)?;
                        coefficients[output][index] = value;
                        // No unsupported source row may be read at zero cost.
                        let row = index / problem.base_observations;
                        if !action.support.contains(&row) {
                            constraints.push(self.arena.compare(Relation::Equal,value,0)?);
                        }
                    }
                }
                for (index,poly) in constants.iter().enumerate() {
                    offset[index] = self.arena.polynomial(poly,&env)?;
                }
            }
        }
        let allowed = self.arena.and(constraints)?;
        Ok(ActionValue {parameters,allowed,coefficients,offset})
    }
    fn consistent(&mut self, model_index: usize, history: &[Step])
        -> Result<(Vec<Symbol>,FormulaId)> {
        let problem = self.problem;
        let model = &problem.models[model_index];
        let parameters = self.arena.fresh(model.parameter_count)?;
        let env = self.environment(&parameters);
        let mut conditions = vec![self.arena.predicate(&model.domain,&env)?];
        let mut base = Vec::new();
        for poly in &model.base { base.push(self.arena.polynomial(poly,&env)?); }
        // ONE env/base is reused for EVERY record in the history.
        for step in history {
            for (output,response) in step.response.iter().enumerate() {
                let mut summands = vec![step.action.offset[output]];
                for (coefficient,value) in step.action.coefficients[output].iter().zip(&base) {
                    summands.push(self.arena.product(vec![*coefficient,*value])?);
                }
                let lhs = self.arena.sum(summands)?;
                let rhs = self.arena.variable(*response);
                conditions.push(self.arena.compare(Relation::Equal,lhs,rhs)?);
            }
        }
        let formula = self.arena.and(conditions)?;
        Ok((parameters,formula))
    }
    fn homogeneous(&mut self, history: &[Step]) -> Result<FormulaId> {
        let problem = self.problem;
        let mut exclusions = Vec::new();
        for i in 0..problem.models.len() {
            for j in i+1..problem.models.len() {
                if problem.models[i].target == problem.models[j].target { continue; }
                let (a,ca) = self.consistent(i,history)?;
                let (b,cb) = self.consistent(j,history)?;
                let both = self.arena.and(vec![ca,cb])?;
                let variables = a.into_iter().chain(b).collect();
                let possible_pair = self.arena.exists(variables,both)?;
                exclusions.push(self.arena.not(possible_pair)?);
            }
        }
        self.arena.and(exclusions)
    }
    fn reachable(&mut self, history: &[Step]) -> Result<(Vec<FormulaId>,FormulaId)> {
        let mut alternatives = Vec::new();
        alternatives.try_reserve_exact(self.problem.models.len())
            .map_err(|_| Error::Limit("MODEL_POSSIBILITY_ALLOCATION"))?;
        for model in 0..self.problem.models.len() {
            let (variables,consistent) = self.consistent(model,history)?;
            alternatives.push(self.arena.exists(variables,consistent)?);
        }
        // Reuse the very SAME quantified whole-history predicates in the
        // terminal-target assertions. No new source bank or model evaluator.
        let mut retained = Vec::new();
        retained.try_reserve_exact(alternatives.len())
            .map_err(|_| Error::Limit("MODEL_POSSIBILITY_ALLOCATION"))?;
        retained.extend_from_slice(&alternatives);
        let reachable = self.arena.or(alternatives)?;
        Ok((retained,reachable))
    }
    fn win(&mut self, history: &mut Vec<Step>, state: &Resources, depth: usize)
        -> Result<FormulaId> {
        let terminal = self.homogeneous(history)?;
        if depth == 0 || terminal == 0 { return Ok(terminal); }
        let problem = self.problem;
        let mut choices = vec![terminal];
        for index in 0..problem.actions.len() {
            let next = state.extended(problem,&problem.actions[index])?;
            if !next.affordable(self.budget) { continue; }
            let action = self.action(index)?;
            let response = self.arena.fresh(problem.actions[index].output_count)?;
            let allowed = action.allowed;
            let parameters = action.parameters.clone();
            history.push(Step {action,response:response.clone()});
            let recursive = self.win(history,&next,depth-1)?;
            history.pop();
            let all_responses = self.arena.forall(response,recursive)?;
            let legal_win = self.arena.and(vec![allowed,all_responses])?;
            choices.push(self.arena.exists(parameters,legal_win)?);
        }
        self.arena.or(choices)
    }
}

/// Compile an initial game (empty prefix) or an OPEN exact-history continuation.
///
/// prefix_case_ids fixes only the finite case path; action coordinates and
/// responses remain FREE real symbols in the returned queries. This represents
/// transcendental responses without converting them to rationals. A backend
/// must preserve those free variables when eliminating quantifiers.
///
/// emit_action_fibres additionally emits unquantified next-action relations
/// for a later verified algebraic selector. It never returns an action oracle.
///
/// Constant validity is a separate MANDATORY prerequisite. Nonempty finite
/// downset PATH regions make action legality deletion closed, and every response
/// is explicitly affine in D fixed base coordinates, so retained_horizon is
/// min(D, affordable remaining calls). The per-construction depth cap is an
/// engineering UNKNOWN, not a new scientific horizon or negative decision.
pub fn compile<'a>(
    problem: &'a Problem,
    budget: &'a PathBudget,
    prefix_case_ids: &[usize],
    emit_action_fibres: bool,
    limits: Limits,
) -> Result<Compiled<'a>> {
    let dimension = validate(problem,budget,prefix_case_ids,limits)?;
    let mut arena = Arena::new(limits)?;
    let constants = arena.fresh(problem.constants.len())?;
    let mut c = Compiler {problem,budget,arena,constants,dimension};
    let constants_valid = c.constants_validity()?;
    let mut history = Vec::new();
    let mut history_symbols = Vec::new();
    let mut guards = Vec::new();
    let mut state = Resources::default();
    for index in prefix_case_ids {
        state = state.extended(problem,&problem.actions[*index])?;
        if !state.affordable(budget) { return Err(Error::Invalid("PREFIX_RESOURCE_STATE")); }
        let action = c.action(*index)?;
        let response = c.arena.fresh(problem.actions[*index].output_count)?;
        guards.push(action.allowed);
        history_symbols.push(HistorySymbols {
            case_index:*index, action_parameters:action.parameters.clone(),
            response:response.clone(),
        });
        history.push(Step {action,response});
    }
    let prefix_legal = c.arena.and(guards)?;
    let retained_horizon = dimension.min(state.remaining(budget));
    if retained_horizon > limits.recursion_depth || retained_horizon > 128 {
        return Err(Error::Limit("WINNING_RECURSION_DEPTH"));
    }
    let homogeneous = c.homogeneous(&history)?;
    let winning_raw = c.win(&mut history,&state,retained_horizon)?;
    let legal_win = c.arena.and(vec![prefix_legal,winning_raw])?;
    let winning = c.conditional_on_constants(legal_win)?;
    let legal_history = c.conditional_on_constants(prefix_legal)?;
    let homogeneous_history = c.conditional_on_constants(homogeneous)?;
    let (possible_models,reachable) = c.reachable(&history)?;
    let mut excluded_models = Vec::new();
    excluded_models.try_reserve_exact(possible_models.len())
        .map_err(|_| Error::Limit("MODEL_EXCLUSION_ALLOCATION"))?;
    for possible in possible_models {
        let excluded = c.arena.not(possible)?;
        // Do NOT expose constant symbols as unbound history coordinates.
        // This is forall C, constant_roots(C) -> not exists source bank ...
        excluded_models.push(c.conditional_on_constants(excluded)?);
    }
    let root_symbols = c.constants.clone();
    let roots = c.constant_roots(&root_symbols)?;
    let legal_reachable = c.arena.and(vec![roots,prefix_legal,reachable])?;
    let reachable_history = c.arena.exists(c.constants.clone(),legal_reachable)?;
    let mut fibres = Vec::new();
    if emit_action_fibres {
        for index in 0..problem.actions.len() {
            let next = state.extended(problem,&problem.actions[index])?;
            let affordable = next.affordable(budget);
            if !affordable || retained_horizon == 0 {
                fibres.push(ActionFibre {
                    symbols:ActionFibreSymbols {
                        case_index:index,action_parameters:Vec::new(),affordable,
                        enabled_in_retained_horizon:false,
                    },
                    formula:1,
                });
                continue;
            }
            let action = c.action(index)?;
            let parameters = action.parameters.clone();
            let allowed = action.allowed;
            let response = c.arena.fresh(problem.actions[index].output_count)?;
            history.push(Step {action,response:response.clone()});
            let remaining = c.win(&mut history,&next,retained_horizon-1)?;
            history.pop();
            let every_response = c.arena.forall(response,remaining)?;
            let fibre = c.arena.and(vec![prefix_legal,allowed,every_response])?;
            let formula = c.conditional_on_constants(fibre)?;
            fibres.push(ActionFibre {
                symbols:ActionFibreSymbols {
                    case_index:index,action_parameters:parameters,affordable,
                    enabled_in_retained_horizon:true,
                },
                formula,
            });
        }
    }
    let supplied_affine_cases = problem.actions.iter().enumerate()
        .filter_map(|(i,a)| matches!(&a.measurement,Measurement::SuppliedAffine {..}).then_some(i))
        .collect();
    Ok(Compiled {
        problem,budget,arena:c.arena,constants_valid,legal_history,reachable_history,
        homogeneous_history,excluded_models,winning,fibres,history_symbols,
        constant_symbols:c.constants,retained_horizon,supplied_affine_cases,
    })
}

/// Iterative renderer: DAG sharing may expand in backend text, so a separate
/// byte budget is checked before every append. All backend names/heads are
/// generated here; no caller string is executable source.
impl Arena {
    fn render(&self, root: FormulaId) -> Result<String> {
        enum Task {
            Text(&'static str),
            Owned(String),
            Symbol(Symbol),
            Term(TermId),
            Formula(FormulaId),
        }
        fn append(out: &mut String, s: &str, limit: usize) -> Result<()> {
            let next = out.len().checked_add(s.len()).ok_or(Error::Limit("RENDER_SIZE_OVERFLOW"))?;
            if next > limit { return Err(Error::Limit("RENDER_BYTES")); }
            out.try_reserve(s.len()).map_err(|_| Error::Limit("RENDER_ALLOCATION"))?;
            out.push_str(s); Ok(())
        }
        let mut out = String::new();
        append(&mut out,"Resolve[",self.limits.rendered_bytes)?;
        let mut work = vec![Task::Text(",Reals]"),Task::Formula(root)];
        while let Some(task) = work.pop() {
            match task {
                Task::Text(s) => append(&mut out,s,self.limits.rendered_bytes)?,
                Task::Owned(s) => append(&mut out,&s,self.limits.rendered_bytes)?,
                Task::Symbol(s) => append(&mut out,&s.wolfram_name(),self.limits.rendered_bytes)?,
                Task::Term(id) => match &self.terms[id] {
                    Term::Number(value) => {
                        // bits bounds decimal digits conservatively, before allocating text.
                        let bound = value.numer().bits().checked_add(value.denom().bits())
                            .and_then(|n| n.checked_add(16)).ok_or(Error::Limit("RATIONAL_RENDER_SIZE"))?;
                        if bound > self.limits.rendered_bytes as u64 {
                            return Err(Error::Limit("RATIONAL_RENDER_BOUND"));
                        }
                        let s = format!("Rational[{},{}]",value.numer(),value.denom());
                        append(&mut out,&s,self.limits.rendered_bytes)?;
                    }
                    Term::Variable(symbol) => work.push(Task::Symbol(*symbol)),
                    Term::Sum(ids) | Term::Product(ids) => {
                        work.push(Task::Text("]"));
                        for (index,id) in ids.iter().enumerate().rev() {
                            work.push(Task::Term(*id));
                            if index != 0 { work.push(Task::Text(",")); }
                        }
                        work.push(Task::Text(if matches!(&self.terms[id],Term::Sum(_)) {"Plus["} else {"Times["}));
                    }
                    Term::Power(value,exponent) => {
                        work.push(Task::Text("]"));
                        work.push(Task::Owned(exponent.to_string()));
                        work.push(Task::Text(","));
                        work.push(Task::Term(*value));
                        work.push(Task::Text("Power["));
                    }
                },
                Task::Formula(id) => match &self.formulas[id] {
                    Formula::Truth(value) => work.push(Task::Text(if *value {"True"} else {"False"})),
                    Formula::Compare(relation,lhs,rhs) => {
                        work.push(Task::Text("]")); work.push(Task::Term(*rhs));
                        work.push(Task::Text(",")); work.push(Task::Term(*lhs));
                        work.push(Task::Text(match relation {
                            Relation::Equal => "Equal[",
                            Relation::Nonnegative => "GreaterEqual[",
                            Relation::Positive => "Greater[",
                        }));
                    }
                    Formula::Not(body) => {
                        work.push(Task::Text("]"));work.push(Task::Formula(*body));
                        work.push(Task::Text("Not["));
                    }
                    Formula::And(ids) | Formula::Or(ids) => {
                        work.push(Task::Text("]"));
                        for (index,id) in ids.iter().enumerate().rev() {
                            work.push(Task::Formula(*id));
                            if index != 0 { work.push(Task::Text(",")); }
                        }
                        work.push(Task::Text(if matches!(&self.formulas[id],Formula::And(_)) {"And["} else {"Or["}));
                    }
                    Formula::Exists(symbols,body) | Formula::ForAll(symbols,body) => {
                        work.push(Task::Text("]"));work.push(Task::Formula(*body));
                        work.push(Task::Text("},"));
                        for (index,symbol) in symbols.iter().enumerate().rev() {
                            work.push(Task::Symbol(*symbol));
                            if index != 0 { work.push(Task::Text(",")); }
                        }
                        work.push(Task::Text("{"));
                        work.push(Task::Text(if matches!(&self.formulas[id],Formula::Exists(..)) {"Exists["} else {"ForAll["}));
                    }
                },
            }
        }
        Ok(out)
    }
}

/// Existing bounded joint-LAW supplier, with source and menu bindings retained.
#[path = "g7_law_table_inlet.rs"]
pub mod law_table_inlet;

/// Controlled full-word composition; natural register and forced pulses stay distinct.
#[path = "g7_controlled_word.rs"]
pub mod controlled_word;

/// Original supplied-cell rows and vector to one existing calendar/word bank.
#[path = "cell_row_export.rs"]
pub mod cell_rows;
#[path = "g7_cell_calendar.rs"]
pub mod cell_calendar;

/// Explicit completed unranked menus on the same captured cell/word bank.
#[path = "g7_word_readout.rs"]
pub mod word_readout;


/// Correlated fixed-calendar survival coordinates; no physical coverage assumed.
#[path = "g7_correlated_survival.rs"]
pub mod correlated_survival;

#[path = "g7_population_certificate.rs"]
pub mod population_certificate;

#[path = "g7_supplied_family.rs"]
pub mod supplied_family;
