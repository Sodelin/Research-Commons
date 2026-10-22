//! Bounded original LAW-table inlet for the pure G7 formula frontend.
//! SOURCE ONLY: uncompiled/unexecuted. No writer, process, new solver or grammar.
//!
//! Reuses law::compile ONCE per supplied source/model/menu, then exactly specializes
//! that SAME joint table for all ORIGINAL forcing rows. It is not a complete
//! census/admission provider, parser proof, physical readout or all-finite LAW
//! replacement. No failed/over-budget model or outcome is silently omitted.
#![forbid(unsafe_code)]

use crate::{ActionCase, AlgebraicConstant, Predicate, Problem, Relation, SourceModel};
use parity_solver::{law, polynomial::Polynomial, q, Rational};
use std::collections::{BTreeMap, BTreeSet, btree_map::Entry};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReadoutBasis { Rooted, Unrooted }

#[derive(Clone, Debug)]
pub struct Readout {
    pub basis: ReadoutBasis,
    pub outcome_count: usize,
    /// Original native canonical terminal signature -> declared finite outcome.
    /// Every terminal occurring in ANY supplied table must be mapped.
    /// Extra keys are allowed: another source may have different support.
    pub terminal_to_outcome: BTreeMap<String,usize>,
}

#[derive(Clone, Debug)]
pub struct TaggedRequest {
    pub request: law::Request,
    /// Constant on this finite source/model piece, in the declared target set.
    pub target: usize,
}

#[derive(Clone, Debug)]
pub struct ReadoutMenu {
    pub sample_taxa: Vec<usize>,
    pub readout: Readout,
}

#[derive(Clone, Debug)]
pub struct FamilyInput {
    pub taxon_count: usize,
    pub original_hybrid_count: usize,
    /// Each menu retains its exact Copy-position -> ORIGINAL taxon index map.
    /// The model request is the first menu's exact source/mechanism/budget
    /// template; other menus reuse that SAME source and parameter positions.
    pub menus: Vec<ReadoutMenu>,
    pub original_rows: Vec<Vec<Option<bool>>>,
    pub models: Vec<TaggedRequest>,
}

#[derive(Clone, Copy, Debug)]
pub struct InletLimits {
    pub models: usize,
    pub menus: usize,
    pub native_tables: usize,
    pub rows: usize,
    pub outcomes: usize,
    pub cells: usize,
    pub polynomial_terms: usize,
    pub retained_terms: usize,
    pub operations: usize,
    pub rational_bits: u64,
    pub scope: usize,
    pub terminal_key_bytes: usize,
}

impl Default for InletLimits {
    fn default() -> Self {
        Self {
            models:256, menus:256, native_tables:1024,
            rows:65_536, outcomes:65_536, cells:1_000_000,
            polynomial_terms:65_536, retained_terms:1_000_000,
            operations:10_000_000, rational_bits:65_536, scope:4096,
            terminal_key_bytes:1_000_000,
        }
    }
}

#[derive(Clone, Debug)]
pub enum InletError {
    Invalid(&'static str),
    /// An unavailable construction, NEVER an absent source or budget NO.
    Unknown {
        reason: &'static str,
        model_index: Option<usize>,
        menu_index: Option<usize>,
        original_native_limit: Option<law::Limit>,
    },
    /// Retains original validator/internal error without treating it as a
    /// mathematical all-source exclusion or skipping the failed model.
    NativeFailure { model_index:usize, menu_index:usize, reason:&'static str },
}

type Result<T> = std::result::Result<T,InletError>;

#[derive(Clone, Debug, Default)]
pub struct PreparationStats {
    pub original_law_tables: usize,
    pub specialized_rows: usize,
    pub retained_cells: usize,
    pub retained_terms: usize,
    pub charged_operations: usize,
}

/// This borrow binds a declared input object, not its authenticated external
/// bytes or source-class completeness. Keep it with the resulting Problem.
#[derive(Clone, Debug)]
pub struct SupplierBinding<'a> {
    pub original_input: &'a FamilyInput,
    pub algebraic_constant_count: usize,
    /// Starts with0, then each menu's end offset within ONE original row.
    pub menu_offsets: Vec<usize>,
    pub native_parent0_probability_convention: &'static str,
}

#[derive(Debug)]
pub struct PreparedFamily<'a> {
    models: Vec<SourceModel>,
    binding: SupplierBinding<'a>,
    stats: PreparationStats,
}

#[derive(Debug)]
pub struct BoundProblem<'a> {
    problem: Problem,
    binding: SupplierBinding<'a>,
    stats: PreparationStats,
}

impl<'a> PreparedFamily<'a> {
    pub fn models(&self) -> &[SourceModel] { &self.models }
    pub fn binding(&self) -> &SupplierBinding<'a> { &self.binding }
    pub fn stats(&self) -> &PreparationStats { &self.stats }

    /// Preserve the original input binding rather than silently detach it.
    /// A downstream controller must still authenticate original bytes/results.
    pub fn into_problem(self, target_count:usize,
        constants:Vec<AlgebraicConstant>, actions:Vec<ActionCase>)
        -> Result<BoundProblem<'a>> {
        if constants.len() != self.binding.algebraic_constant_count {
            return Err(InletError::Invalid("ALGEBRAIC_CONSTANT_SCOPE"));
        }
        if target_count == 0 || self.models.iter().any(|m| m.target >= target_count) {
            return Err(InletError::Invalid("MODEL_TARGET_ALPHABET"));
        }
        let input = self.binding.original_input;
        if input.menus.len() > 1 && actions.iter().any(|a|
            matches!(&a.measurement,crate::Measurement::StochasticChannels(_))) {
            return Err(InletError::Invalid("CONCATENATED_MENUS_REQUIRE_EXPLICIT_AFFINE_PROGRAMME"));
        }
        let observations = self.binding.menu_offsets.last().copied()
            .ok_or(InletError::Invalid("MENU_COORDINATE_OFFSETS"))?;
        let problem = Problem {
            original_hybrid_count:input.original_hybrid_count,
            rows:input.original_rows.clone(),
            base_observations:observations,
            target_count,constants,models:self.models,actions,
        };
        Ok(BoundProblem {problem,binding:self.binding,stats:self.stats})
    }
}

impl<'a> BoundProblem<'a> {
    pub fn problem(&self) -> &Problem { &self.problem }
    pub fn binding(&self) -> &SupplierBinding<'a> { &self.binding }
    pub fn stats(&self) -> &PreparationStats { &self.stats }
    /// Detachment is explicit and returns the required provenance alongside it.
    pub fn into_parts(self) -> (Problem,SupplierBinding<'a>,PreparationStats) {
        (self.problem,self.binding,self.stats)
    }
}

struct Work {
    limits: InletLimits,
    stats: PreparationStats,
}

impl Work {
    fn unknown(&self, reason:&'static str) -> InletError {
        InletError::Unknown {reason,model_index:None,menu_index:None,original_native_limit:None}
    }
    fn charge(&mut self, amount:usize) -> Result<()> {
        self.stats.charged_operations = self.stats.charged_operations.checked_add(amount)
            .ok_or_else(|| self.unknown("INLET_OPERATION_OVERFLOW"))?;
        if self.stats.charged_operations > self.limits.operations {
            return Err(self.unknown("INLET_OPERATIONS"));
        }
        Ok(())
    }
    fn rational(&self, qv:&Rational) -> Result<()> {
        if qv.denom() <= q(0,1).numer() {
            return Err(InletError::Invalid("INLET_RATIONAL_DENOMINATOR"));
        }
        if qv.numer().bits().max(qv.denom().bits()) > self.limits.rational_bits {
            return Err(self.unknown("INLET_RATIONAL_BITS"));
        }
        Ok(())
    }
    fn check_poly(&mut self, p:&Polynomial, dimension:usize) -> Result<()> {
        if p.dimension != dimension || p.terms.keys().any(|powers| powers.len() != dimension) {
            return Err(InletError::Invalid("NATIVE_POLYNOMIAL_DIMENSION"));
        }
        if p.terms.len() > self.limits.polynomial_terms {
            return Err(self.unknown("INLET_POLYNOMIAL_TERMS"));
        }
        for coefficient in p.terms.values() { self.rational(coefficient)?; }
        let cost = p.terms.len().checked_mul(dimension.checked_add(1)
            .ok_or_else(|| self.unknown("INLET_SCOPE_OVERFLOW"))?)
            .ok_or_else(|| self.unknown("INLET_OPERATION_OVERFLOW"))?;
        self.charge(cost)
    }
    fn add_term(&mut self, into:&mut Polynomial, powers:Vec<usize>, coefficient:&Rational)
        -> Result<()> {
        self.charge(powers.len().checked_add(1).ok_or_else(|| self.unknown("INLET_SCOPE_OVERFLOW"))?)?;
        self.rational(coefficient)?;
        if coefficient == &q(0,1) { return Ok(()); }
        let length = into.terms.len();
        match into.terms.entry(powers) {
            Entry::Vacant(slot) => {
                if length >= self.limits.polynomial_terms {
                    return Err(InletError::Unknown {reason:"INLET_POLYNOMIAL_TERMS",
                        model_index:None,menu_index:None,original_native_limit:None});
                }
                slot.insert(coefficient.clone());
            }
            Entry::Occupied(mut slot) => {
                let sum = slot.get() + coefficient;
                self.rational(&sum)?;
                if sum == q(0,1) { slot.remove(); } else { *slot.get_mut() = sum; }
            }
        }
        Ok(())
    }
    fn add_poly(&mut self, into:&mut Polynomial, value:&Polynomial) -> Result<()> {
        if into.dimension != value.dimension { return Err(InletError::Invalid("INLET_SUM_DIMENSION")); }
        for (powers,coefficient) in &value.terms {
            self.add_term(into,powers.clone(),coefficient)?;
        }
        Ok(())
    }
    fn retain(&mut self, p:&Polynomial) -> Result<()> {
        self.stats.retained_cells = self.stats.retained_cells.checked_add(1)
            .ok_or_else(|| self.unknown("INLET_CELL_OVERFLOW"))?;
        self.stats.retained_terms = self.stats.retained_terms.checked_add(p.terms.len())
            .ok_or_else(|| self.unknown("INLET_TERM_OVERFLOW"))?;
        if self.stats.retained_cells > self.limits.cells
            || self.stats.retained_terms > self.limits.retained_terms {
            return Err(self.unknown("INLET_RETAINED_OUTPUT"));
        }
        Ok(())
    }
}

/// Check fixed original bounds BEFORE Request.validate allocates per-vertex
/// graph arrays. The original request/compiler and their caps are not edited.
fn preflight(request:&law::Request, model_index:usize) -> Result<()> {
    let source = &request.source;
    let unavailable = |reason:&'static str| InletError::Unknown {
        reason,model_index:Some(model_index),menu_index:None,original_native_limit:None,
    };
    if source.vertices > 32 || source.edges.len() > 32 {
        return Err(unavailable("ORIGINAL_LAW_SOURCE_LIMIT"));
    }
    let bank = source.vertices.checked_add(source.edges.len())
        .and_then(|x| x.checked_add(1)).and_then(|x| x.checked_add(source.hybrids.len()))
        .ok_or_else(|| unavailable("ORIGINAL_LAW_BANK_OVERFLOW"))?;
    if bank > 32 { return Err(unavailable("ORIGINAL_LAW_BANK_LIMIT")); }
    if request.samples.len() > 4 { return Err(unavailable("ORIGINAL_LAW_SAMPLE_LIMIT")); }
    if request.budgets.states > 4096 || request.budgets.terms > 65_536
        || request.budgets.histories > 4096 {
        return Err(unavailable("ORIGINAL_LAW_BUDGET_LIMIT"));
    }
    if source.vertices < 3 || source.edges.len() < 2 || source.leaves.len() > source.vertices
        || request.samples.is_empty()
        || request.samples.iter().any(|x| *x >= source.leaves.len()) {
        return Err(InletError::Invalid("ORIGINAL_LAW_REQUEST_STRUCTURE"));
    }
    Ok(())
}

fn validate_family(input:&FamilyInput, constant_count:usize, work:&mut Work) -> Result<Vec<usize>> {
    if input.taxon_count < 2 || input.menus.is_empty() {
        return Err(InletError::Invalid("FAMILY_TAXON_OR_MENU_ALPHABET"));
    }
    if input.models.len() > work.limits.models || input.menus.len() > work.limits.menus
        || input.original_rows.len() > work.limits.rows || constant_count > work.limits.scope {
        return Err(work.unknown("INLET_DIMENSIONS"));
    }
    let tables = input.models.len().checked_mul(input.menus.len())
        .ok_or_else(|| work.unknown("INLET_TABLE_COUNT_OVERFLOW"))?;
    if tables > work.limits.native_tables { return Err(work.unknown("INLET_NATIVE_TABLES")); }
    let mut offsets = vec![0usize];
    let mut observations = 0usize;
    let mut key_bytes = 0usize;
    for menu in &input.menus {
        if menu.readout.outcome_count == 0 || menu.sample_taxa.is_empty()
            || menu.sample_taxa.iter().any(|x| *x >= input.taxon_count) {
            return Err(InletError::Invalid("FAMILY_SAMPLE_OR_OUTCOME_ALPHABET"));
        }
        if menu.sample_taxa.len() > 4 { return Err(work.unknown("ORIGINAL_LAW_SAMPLE_LIMIT")); }
        observations = observations.checked_add(menu.readout.outcome_count)
            .ok_or_else(|| work.unknown("MENU_COORDINATE_OVERFLOW"))?;
        if observations > work.limits.outcomes { return Err(work.unknown("INLET_OUTCOMES")); }
        offsets.push(observations);
        for (key,outcome) in &menu.readout.terminal_to_outcome {
            key_bytes = key_bytes.checked_add(key.len()).ok_or_else(|| work.unknown("READOUT_KEY_OVERFLOW"))?;
            if key_bytes > work.limits.terminal_key_bytes { return Err(work.unknown("READOUT_KEYS")); }
            if *outcome >= menu.readout.outcome_count { return Err(InletError::Invalid("READOUT_OUTCOME_ID")); }
            work.charge(key.len().checked_add(1).ok_or_else(|| work.unknown("READOUT_KEY_OVERFLOW"))?)?;
        }
    }
    let cells = input.models.len().checked_mul(input.original_rows.len())
        .and_then(|n| n.checked_mul(observations))
        .ok_or_else(|| work.unknown("INLET_CELL_OVERFLOW"))?;
    if cells > work.limits.cells { return Err(work.unknown("INLET_CELLS")); }
    let mut seen = BTreeSet::new();
    for row in &input.original_rows {
        work.charge(row.len())?;
        if row.len() != input.original_hybrid_count {
            return Err(InletError::Invalid("ORIGINAL_ROW_REGISTRY_LENGTH"));
        }
        if !seen.insert(row.clone()) { return Err(InletError::Invalid("ORIGINAL_ROW_ALIAS")); }
    }
    for (index,model) in input.models.iter().enumerate() {
        preflight(&model.request,index)?;
        if model.request.source.leaves.len() != input.taxon_count
            || model.request.source.hybrids.len() != input.original_hybrid_count
            || model.request.samples != input.menus[0].sample_taxa {
            return Err(InletError::Invalid("SOURCE_REGISTRY_TAXON_OR_SAMPLE_ORDER"));
        }
        let dimension = model.request.source.edges.len().checked_add(input.original_hybrid_count)
            .and_then(|n| n.checked_add(constant_count)).ok_or_else(|| work.unknown("INLET_SCOPE_OVERFLOW"))?;
        if dimension > work.limits.scope { return Err(work.unknown("INLET_SCOPE")); }
    }
    Ok(offsets)
}

fn project(table:&law::Table, readout:&Readout, work:&mut Work) -> Result<Vec<Polynomial>> {
    let mut projected = vec![Polynomial::zero(table.dimension);readout.outcome_count];
    let terms: Vec<(&String,&Polynomial)> = match readout.basis {
        ReadoutBasis::Rooted => table.rooted.iter().map(|(key,(_,p))| (key,p)).collect(),
        ReadoutBasis::Unrooted => table.unrooted.iter().collect(),
    };
    for (key,p) in terms {
        work.check_poly(p,table.dimension)?;
        let outcome = *readout.terminal_to_outcome.get(key)
            .ok_or(InletError::Invalid("READOUT_MISSING_NATIVE_TERMINAL"))?;
        work.add_poly(&mut projected[outcome],p)?;
    }
    let mut total = Polynomial::zero(table.dimension);
    for p in &projected { work.add_poly(&mut total,p)?; }
    if total != Polynomial::one(table.dimension) {
        return Err(InletError::Invalid("PROJECTED_FORMAL_MASS_NOT_ONE"));
    }
    Ok(projected)
}

/// G_h is native incoming[0] probability. Forcing parent0/false sets G_h=1;
/// parent1/true sets G_h=0. Natural G variables keep their original coordinates.
/// Prefixing constants changes scope only; all law coefficients remain rational.
fn specialize(
    polynomial:&Polynomial, edges:usize, row:&[Option<bool>],
    constant_count:usize, work:&mut Work,
) -> Result<Polynomial> {
    let native_dimension = edges.checked_add(row.len()).ok_or_else(|| work.unknown("INLET_SCOPE_OVERFLOW"))?;
    if polynomial.dimension != native_dimension { return Err(InletError::Invalid("LAW_ORIGINAL_G_COORDINATES")); }
    let dimension = constant_count.checked_add(native_dimension).ok_or_else(|| work.unknown("INLET_SCOPE_OVERFLOW"))?;
    let mut output = Polynomial::zero(dimension);
    for (powers,coefficient) in &polynomial.terms {
        work.charge(native_dimension.checked_add(1).ok_or_else(|| work.unknown("INLET_SCOPE_OVERFLOW"))?)?;
        if powers.len() != native_dimension { return Err(InletError::Invalid("LAW_EXPONENT_ARITY")); }
        let mut keep = true;
        for (h,forced) in row.iter().enumerate() {
            if *forced == Some(true) && powers[edges+h] != 0 { keep = false; break; }
        }
        if !keep { continue; }
        let mut lifted = vec![0;constant_count];
        lifted.extend_from_slice(powers);
        for (h,forced) in row.iter().enumerate() {
            if forced.is_some() { lifted[constant_count+edges+h] = 0; }
        }
        work.add_term(&mut output,lifted,coefficient)?;
    }
    Ok(output)
}

fn natural_domain(dimension:usize, constant_count:usize) -> Result<Predicate> {
    let scope = constant_count.checked_add(dimension)
        .ok_or(InletError::Unknown {reason:"INLET_SCOPE_OVERFLOW",model_index:None,menu_index:None,original_native_limit:None})?;
    let mut conditions = Vec::new();
    for index in 0..dimension {
        let variable = Polynomial::variable(scope,constant_count+index)
            .map_err(InletError::Invalid)?;
        let complement = Polynomial::one(scope).subtract(&variable).map_err(InletError::Invalid)?;
        conditions.push(Predicate::Atom(Relation::Positive,variable));
        conditions.push(Predicate::Atom(Relation::Positive,complement));
    }
    Ok(Predicate::And(conditions))
}

/// Once admitted by the REAL external controller, this function would call the
/// existing pure LAW engine once per model/menu. It is not invoked by loading.
/// All menus/forcing rows stay in ONE model with ONE source parameter bank.
/// All errors abort the family: no truncated census/menu/readout is returned.
pub fn prepare<'a>(input:&'a FamilyInput, constant_count:usize, limits:InletLimits)
    -> Result<PreparedFamily<'a>> {
    let mut work = Work {limits,stats:PreparationStats::default()};
    let menu_offsets = validate_family(input,constant_count,&mut work)?;
    let mut models = Vec::new();
    for (index,model) in input.models.iter().enumerate() {
        let expected_dimension = model.request.source.edges.len().checked_add(input.original_hybrid_count)
            .ok_or_else(|| work.unknown("INLET_SCOPE_OVERFLOW"))?;
        let mut projected_menus = Vec::new();
        for (menu_index,menu) in input.menus.iter().enumerate() {
            let request = law::Request {
                source:model.request.source.clone(),samples:menu.sample_taxa.clone(),
                mechanism:model.request.mechanism,budgets:model.request.budgets,
            };
            let table = match law::compile(&request) {
                Ok(law::Decision::Table(table)) => table,
                Ok(law::Decision::Unknown(limit)) => return Err(InletError::Unknown {
                    reason:"ORIGINAL_LAW_LIMIT",model_index:Some(index),menu_index:Some(menu_index),original_native_limit:Some(limit),
                }),
                Err("LAW_LIMIT") => return Err(InletError::Unknown {
                    reason:"ORIGINAL_LAW_UNSUPPORTED",model_index:Some(index),menu_index:Some(menu_index),original_native_limit:None,
                }),
                Err(reason) => return Err(InletError::NativeFailure {model_index:index,menu_index,reason}),
            };
            if table.dimension != expected_dimension {
                return Err(InletError::Invalid("ORIGINAL_LAW_TABLE_DIMENSION"));
            }
            work.stats.original_law_tables = work.stats.original_law_tables.checked_add(1)
                .ok_or_else(|| work.unknown("INLET_TABLE_COUNT_OVERFLOW"))?;
            projected_menus.push(project(&table,&menu.readout,&mut work)?);
        }
        let scope = constant_count.checked_add(expected_dimension).ok_or_else(|| work.unknown("INLET_SCOPE_OVERFLOW"))?;
        let mut base = Vec::new();
        for row in &input.original_rows {
            for projected in &projected_menus {
                let mut total = Polynomial::zero(scope);
                for p in projected {
                    let specialized = specialize(p,model.request.source.edges.len(),row,constant_count,&mut work)?;
                    work.add_poly(&mut total,&specialized)?;
                    work.retain(&specialized)?;
                    base.push(specialized);
                }
                // EACH menu is a law. Concatenating menus is not ONE PMF.
                if total != Polynomial::one(scope) {
                    return Err(InletError::Invalid("CONTROLLED_FORMAL_MENU_MASS_NOT_ONE"));
                }
            }
            work.stats.specialized_rows = work.stats.specialized_rows.checked_add(1)
                .ok_or_else(|| work.unknown("INLET_ROW_COUNT_OVERFLOW"))?;
        }
        models.push(SourceModel {
            parameter_count:expected_dimension,target:model.target,
            domain:natural_domain(expected_dimension,constant_count)?,base,
        });
    }
    Ok(PreparedFamily {
        models,
        binding:SupplierBinding {
            original_input:input,algebraic_constant_count:constant_count,menu_offsets,
            native_parent0_probability_convention:"G_h=P(incoming[0]); false->G_h=1, true->G_h=0; unforced G_h remains shared",
        },
        stats:work.stats,
    })
}
