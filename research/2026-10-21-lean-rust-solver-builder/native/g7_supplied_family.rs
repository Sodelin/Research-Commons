//! SOURCE-ONLY composition of retained fixed-calendar row/menu values into
//! the EXISTING exact-real Problem. No physical admission/coverage is inferred.
//! No solver, backend, process, filesystem, transport or runtime writer.
#![forbid(unsafe_code)]

use crate::{ActionCase, AlgebraicConstant, Compiled, Error, Limits, Measurement,
    PathBudget, Predicate, Problem, SourceModel, Validation};
use crate::correlated_survival::BoundFamilyRows;
use crate::word_readout::Menu;

/// A SUPPLIED target-labelled mathematical piece. The restriction is conjoined
/// with the original correlated domain; it never replaces or weakens it.
/// This is data, not a proof of original-source admission or either coverage
/// direction. Different targets may deliberately have identical responses.
#[derive(Debug)]
pub struct Piece<'b, 'p, 'a> {
    pub source: &'b BoundFamilyRows<'p, 'a>,
    pub target: usize,
    pub restriction: Predicate,
}

/// Explicit common carriers also represent zero pieces or zero original rows.
/// Each actual piece must use this SAME positional row/menu order and C prefix.
#[derive(Debug)]
pub struct Input<'b, 'p, 'a> {
    pub original_hybrid_count: usize,
    pub rows: &'b [Vec<Option<bool>>],
    pub menus: &'b [Menu],
    pub constants: Vec<AlgebraicConstant>,
    pub target_count: usize,
    pub pieces: Vec<Piece<'b, 'p, 'a>>,
    pub actions: Vec<ActionCase>,
    pub budget: &'b PathBudget,
}

/// In-process association of the exact supplied family and PATH budget.
/// This does not authenticate an external request/result or physical source.
/// Compile through this immutable value to retain the original suppliers.
#[derive(Debug)]
pub struct Prepared<'b, 'p, 'a> {
    problem: Problem,
    budget: &'b PathBudget,
    rows: &'b [Vec<Option<bool>>],
    menus: &'b [Menu],
    sources: Vec<&'b BoundFamilyRows<'p, 'a>>,
}
impl<'b, 'p, 'a> Prepared<'b, 'p, 'a> {
    pub fn problem(&self) -> &Problem { &self.problem }
    pub fn budget(&self) -> &'b PathBudget { self.budget }
    pub fn original_rows(&self) -> &'b [Vec<Option<bool>>] { self.rows }
    pub fn menus(&self) -> &'b [Menu] { self.menus }
    pub fn source_inputs(&self) -> &[&'b BoundFamilyRows<'p, 'a>] { &self.sources }

    /// Returns only the existing formula/query representation. There is no
    /// backend run, effective selector or physical YES/NO conversion here.
    pub fn compile<'q>(&'q self, prefix_case_ids: &[usize],
        emit_action_fibres: bool, limits: Limits) -> crate::Result<Compiled<'q>> {
        crate::compile(&self.problem,self.budget,prefix_case_ids,emit_action_fibres,limits)
    }
}

fn reserve<T>(out: &mut Vec<T>, count: usize) -> crate::Result<()> {
    out.try_reserve_exact(count).map_err(|_| Error::Limit("SUPPLIED_FAMILY_ALLOCATION"))
}
fn add(a: usize, b: usize) -> crate::Result<usize> {
    a.checked_add(b).ok_or(Error::Limit("SUPPLIED_FAMILY_SIZE_OVERFLOW"))
}

/// Assemble ONE shared-bank source model per supplied piece, preserving every
/// row/menu/outcome position. It reuses the parent's bounded input validator.
/// All new Rust remains uncompiled/unexecuted until the existing execution hold
/// is lifted by the actual native first-writer/controller owner.
pub fn prepare<'b, 'p, 'a>(input: Input<'b, 'p, 'a>, limits: Limits)
    -> crate::Result<Prepared<'b, 'p, 'a>> {
    let Input { original_hybrid_count, rows, menus, constants, target_count,
        pieces, actions, budget } = input;
    let mut validation = Validation { limits, units: 0 };
    validation.charge(original_hybrid_count)?;
    validation.charge(rows.len())?;
    validation.charge(menus.len())?;
    validation.charge(constants.len())?;
    validation.charge(pieces.len())?;
    validation.charge(actions.len())?;
    if target_count == 0 { return Err(Error::Invalid("SUPPLIED_EMPTY_TARGETS")); }
    for row in rows {
        validation.charge(row.len())?;
        if row.len() != original_hybrid_count {
            return Err(Error::Invalid("SUPPLIED_ORIGINAL_ROW_ARITY"));
        }
    }
    let mut observations = 0usize;
    for menu in menus {
        if menu.readout.outcome_count == 0 {
            return Err(Error::Invalid("SUPPLIED_EMPTY_MENU_OUTCOMES"));
        }
        observations = add(observations,menu.readout.outcome_count)?;
    }
    if observations == 0 { return Err(Error::Invalid("SUPPLIED_EMPTY_BASE_OBSERVATIONS")); }
    validation.charge(observations)?;
    let matrix_size = rows.len().checked_mul(observations)
        .ok_or(Error::Limit("SUPPLIED_BASE_DIMENSION"))?;
    validation.charge(matrix_size)?;

    // Menus are alternative PMFs. They cannot be treated as one normalized
    // stochastic base. Keep the original inlet's menu-shape guard.
    for action in &actions {
        match &action.measurement {
            Measurement::StochasticChannels(_) if menus.len() > 1 =>
                return Err(Error::Invalid("SUPPLIED_CONCATENATED_MENU_CHANNEL")),
            Measurement::StochasticMenuChannels { menu_outcomes, .. } =>
                if menu_outcomes.len() != menus.len()
                    || menu_outcomes.iter().zip(menus).any(|(n,m)| *n != m.readout.outcome_count) {
                    return Err(Error::Invalid("SUPPLIED_MENU_CHANNEL_ORDER"));
                },
            _ => (),
        }
    }

    // Before cloning, bound the entire supplied domain/base data with the
    // SAME original validator. Account for the outer And domain at depth0.
    for piece in &pieces {
        let source = piece.source;
        let plan = source.plan();
        if piece.target >= target_count { return Err(Error::Invalid("SUPPLIED_TARGET_ID")); }
        if source.rows() != rows || !std::ptr::eq(source.menus(),menus)
            || source.base_observations() != observations
            || source.readouts().len() != rows.len()
            || plan.constant_count() != constants.len()
            || plan.dimension() != add(constants.len(),plan.parameter_count())?
            || plan.calendar().calendar_request().context.source.hybrids.len()
                != original_hybrid_count {
            return Err(Error::Invalid("SUPPLIED_FAMILY_CARRIER_OR_BANK"));
        }
        validation.charge(plan.parameter_count())?;
        validation.charge(matrix_size)?;
        let depth = validation.limits.recursion_depth;
        validation.limits.recursion_depth = depth.min(128).checked_sub(1)
            .ok_or(Error::Limit("SUPPLIED_DOMAIN_DEPTH"))?;
        validation.charge(3)?;
        validation.predicate(plan.domain(),plan.dimension())?;
        validation.predicate(&piece.restriction,plan.dimension())?;
        validation.limits.recursion_depth = depth;
        for row in source.readouts() {
            if row.blocks().len() != menus.len() {
                return Err(Error::Invalid("SUPPLIED_MENU_BLOCK_COUNT"));
            }
            for (block, menu) in row.blocks().iter().zip(menus) {
                if block.len() != menu.readout.outcome_count {
                    return Err(Error::Invalid("SUPPLIED_MENU_OUTCOME_COUNT"));
                }
                for polynomial in block { validation.polynomial(polynomial,plan.dimension())?; }
            }
        }
    }

    let mut owned_rows = Vec::new();
    reserve(&mut owned_rows,rows.len())?;
    for row in rows {
        let mut owned = Vec::new();
        reserve(&mut owned,row.len())?;
        owned.extend_from_slice(row);
        owned_rows.push(owned);
    }
    let mut sources = Vec::new();
    let mut models = Vec::new();
    reserve(&mut sources,pieces.len())?;
    reserve(&mut models,pieces.len())?;
    for piece in pieces {
        let source = piece.source;
        let plan = source.plan();
        let mut base = Vec::new();
        reserve(&mut base,matrix_size)?;
        for row in source.readouts() {
            for block in row.blocks() {
                for polynomial in block { base.push(polynomial.clone()); }
            }
        }
        // One model bank supplies ALL positions of ALL rows and menus.
        models.push(SourceModel {
            parameter_count: plan.parameter_count(),
            target: piece.target,
            domain: Predicate::And(vec![plan.domain().clone(),piece.restriction]),
            base,
        });
        sources.push(source);
    }
    let problem = Problem { original_hybrid_count, rows: owned_rows,
        base_observations: observations, target_count, constants, models, actions };
    // Validate the complete moved constants/actions/domains and actual budget
    // with the existing implementation. No AST/QE/model run occurs here.
    crate::validate(&problem,budget,&[],limits)?;
    Ok(Prepared { problem, budget, rows, menus, sources })
}
