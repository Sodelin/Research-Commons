//! Explicit completed unranked readouts of ONE bound original cell/word.
//! SOURCE ONLY: uncompiled/unexecuted. Reuses original canonical forest and
//! local splitter. Global splits use the supplied Copy-label universe.
//! No new law engine, scalar evaluation, source admission or runtime dispatch.
#![forbid(unsafe_code)]

use crate::{cell_calendar::WordTable, law_table_inlet::{Readout, ReadoutBasis}};
use parity_solver::{forest::Tree, law, polynomial::Polynomial, q, Rational,
    source_population::{self as population, Context, Location}, source_word};
use std::collections::{BTreeSet, btree_map::Entry};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Labels { LocalCopyPositions, OriginalGlobalCopyLabels }
#[derive(Clone, Debug)]
pub struct Menu {
    pub labels: Labels,
    /// The same explicit finite map type used by the original LAW inlet.
    /// Keys use THIS menu's declared label mode, not an implicit relabelling.
    pub readout: Readout,
}
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub menus: usize,
    pub cells: usize,
    pub dictionary_bytes: usize,
    pub coefficient_work: usize,
    pub retained_terms: usize,
    pub rational_bits: u64,
}
impl Default for Limits {
    fn default() -> Self {
        Self { menus: 256, cells: 1_000_000, dictionary_bytes: 1_000_000,
            coefficient_work: 10_000_000, retained_terms: 1_000_000,
            rational_bits: 65_536 }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(&'static str),
    MissingTerminal { menu_index: usize, key: String },
    Unknown { field: &'static str, required: Option<usize>, cap: usize },
    Internal(&'static str),
}
type Result<T> = std::result::Result<T, Error>;
#[derive(Clone, Debug, Default)]
pub struct Work { pub coefficient_work: usize, pub retained_terms: usize }

/// Owns the unchanged full word result; all menus are projected from that same
/// table, mask and physical bank. Each output block is separately mass1.
/// Their concatenation is not one PMF or automatically an authorized action.
#[derive(Debug)]
pub struct Batch<'a> {
    word: WordTable<'a>,
    menus: &'a [Menu],
    blocks: Vec<Vec<Polynomial>>,
    work: Work,
}
impl<'a> Batch<'a> {
    pub fn word(&self) -> &WordTable<'a> { &self.word }
    pub fn menus(&self) -> &[Menu] { self.menus }
    pub fn blocks(&self) -> &[Vec<Polynomial>] { &self.blocks }
    pub fn work(&self) -> &Work { &self.work }
}

fn unknown(field: &'static str, required: Option<usize>, cap: usize) -> Error {
    Error::Unknown { field, required, cap }
}
fn add(a: usize, b: usize, field: &'static str, cap: usize) -> Result<usize> {
    let n = a.checked_add(b).ok_or_else(|| unknown(field, None, cap))?;
    if n > cap { return Err(unknown(field, Some(n), cap)); }
    Ok(n)
}
fn rational(value: &Rational, limits: Limits) -> Result<()> {
    if value.denom() <= q(0, 1).numer() {
        return Err(Error::Internal("WORD_READOUT_DENOMINATOR"));
    }
    let bits = value.numer().bits().max(value.denom().bits());
    if bits > limits.rational_bits {
        return Err(unknown("rational_bits", usize::try_from(bits).ok(),
            usize::try_from(limits.rational_bits).unwrap_or(usize::MAX)));
    }
    Ok(())
}
fn sum_into(output: &mut Polynomial, value: &Polynomial, limits: Limits,
    work: &mut Work) -> Result<()> {
    if output.dimension != value.dimension {
        return Err(Error::Internal("WORD_READOUT_POLYNOMIAL_DIMENSION"));
    }
    for (powers, coefficient) in &value.terms {
        if powers.len() != value.dimension {
            return Err(Error::Internal("WORD_READOUT_EXPONENT_ARITY"));
        }
        let cost = powers.len().checked_add(1)
            .ok_or_else(|| unknown("coefficient_work", None, limits.coefficient_work))?;
        work.coefficient_work = add(work.coefficient_work, cost, "coefficient_work", limits.coefficient_work)?;
        rational(coefficient, limits)?;
        if coefficient == &q(0, 1) { continue; }
        match output.terms.entry(powers.clone()) {
            Entry::Vacant(entry) => {
                work.retained_terms = add(work.retained_terms, 1, "retained_terms", limits.retained_terms)?;
                entry.insert(coefficient.clone());
            }
            Entry::Occupied(mut entry) => {
                let sum = entry.get() + coefficient;
                rational(&sum, limits)?;
                if sum == q(0, 1) {
                    entry.remove();
                    work.retained_terms = work.retained_terms.checked_sub(1)
                        .ok_or(Error::Internal("WORD_READOUT_TERM_ACCOUNT"))?;
                } else { *entry.get_mut() = sum; }
            }
        }
    }
    Ok(())
}

/// Original split definition with the ACTUAL global Copy universe replacing
/// 0..m. Labels need not be consecutive or in sample order. This does not
/// identify arbitrary integers with local positions or parse a split string.
fn global_split_string(tree: &Tree, universe: &[usize]) -> Result<String> {
    type Cut = (Vec<usize>, Vec<usize>);
    fn visit(tree: &Tree, universe: &[usize], cuts: &mut BTreeSet<Cut>) -> Vec<usize> {
        let mut side = match tree {
            Tree::Leaf(label) => vec![*label],
            Tree::Node(a, b) => {
                let mut side = visit(a, universe, cuts);
                side.extend(visit(b, universe, cuts));
                side
            }
        };
        side.sort_unstable();
        let other = universe.iter().copied().filter(|label| !side.contains(label)).collect::<Vec<_>>();
        if side.len() >= 2 && other.len() >= 2 {
            cuts.insert(if side < other { (side.clone(), other) } else { (other, side.clone()) });
        }
        side
    }
    let mut cuts = BTreeSet::new();
    let observed = visit(tree, universe, &mut cuts);
    if observed.as_slice() != universe { return Err(Error::Internal("WORD_READOUT_COPY_UNIVERSE")); }
    let side = |v: &Vec<usize>| format!("[{}]", v.iter().map(usize::to_string).collect::<Vec<_>>().join(","));
    Ok(format!("[{}]", cuts.iter().map(|(a,b)| format!("{}|{}", side(a),side(b)))
        .collect::<Vec<_>>().join(";")))
}
fn complete_tree(context: &Context, witness: &population::Snapshot) -> Result<Tree> {
    context.validate_snapshot(witness).map_err(Error::Internal)?;
    if witness.live.len() != 1 || witness.live.iter().any(|copy|
        witness.population[*copy] != Some(Location::Ancestral(context.source.root))) {
        return Err(Error::Internal("WORD_READOUT_INCOMPLETE_GENEALOGY"));
    }
    let mut forest = population::unordered_forest(context, witness).map_err(Error::Internal)?;
    if forest.len() != 1 { return Err(Error::Internal("WORD_READOUT_INCOMPLETE_FOREST")); }
    forest.pop().ok_or(Error::Internal("WORD_READOUT_EMPTY_FOREST"))
}

/// Explicit post-completion fibre sums. Input/full-table binding is retained;
/// a missing menu outcome, arithmetic limit or bad terminal aborts the whole
/// Batch. This function neither changes the programme nor runs a generator.
pub fn project_completed<'a>(word: WordTable<'a>, menus: &'a [Menu],
    limits: Limits) -> Result<Batch<'a>> {
    let context = &word.table().original().context;
    if word.table().original().terminal != source_word::Terminal::AncestralComplete
        || context.sample.is_empty() {
        return Err(Error::Invalid("WORD_READOUT_REQUIRES_NONEMPTY_COMPLETED_WORD"));
    }
    if menus.is_empty() { return Err(Error::Invalid("WORD_READOUT_EMPTY_MENUS")); }
    if menus.len() > limits.menus { return Err(unknown("menus", Some(menus.len()), limits.menus)); }
    let mut cells = 0usize;
    let mut key_bytes = 0usize;
    for menu in menus {
        if menu.readout.outcome_count == 0 {
            return Err(Error::Invalid("WORD_READOUT_EMPTY_OUTCOME_ALPHABET"));
        }
        cells = add(cells, menu.readout.outcome_count, "cells", limits.cells)?;
        for (key, outcome) in &menu.readout.terminal_to_outcome {
            key_bytes = add(key_bytes, key.len(), "dictionary_bytes", limits.dictionary_bytes)?;
            if *outcome >= menu.readout.outcome_count {
                return Err(Error::Invalid("WORD_READOUT_OUTCOME_INDEX"));
            }
        }
    }
    let dimension = word.table().variables().len();
    let mut local_context = context.clone();
    local_context.global_labels = (0..context.sample.len()).collect();
    let mut global_universe = context.global_labels.clone();
    global_universe.sort_unstable();
    let mut blocks = menus.iter().map(|menu|
        vec![Polynomial::zero(dimension); menu.readout.outcome_count]).collect::<Vec<_>>();
    let mut work = Work::default();
    for row in word.table().transitions() {
        if parity_solver::source_epoch::selected_view(context, &row.witness).map_err(Error::Internal)? != row.view {
            return Err(Error::Internal("WORD_READOUT_RANGE_WITNESS"));
        }
        if row.polynomial.dimension != dimension {
            return Err(Error::Internal("WORD_READOUT_WORD_BANK"));
        }
        // Context relabelling occurs only in this explicit final observer.
        // Every original word row, witness and bank remains stored unchanged.
        let local = complete_tree(&local_context, &row.witness)?;
        let global = complete_tree(context, &row.witness)?;
        for (menu_index, menu) in menus.iter().enumerate() {
            let key = match (menu.labels, menu.readout.basis) {
                (Labels::LocalCopyPositions, ReadoutBasis::Rooted) => law::tree_string(&local),
                (Labels::LocalCopyPositions, ReadoutBasis::Unrooted) =>
                    law::split_string(&local, context.sample.len()),
                (Labels::OriginalGlobalCopyLabels, ReadoutBasis::Rooted) => law::tree_string(&global),
                (Labels::OriginalGlobalCopyLabels, ReadoutBasis::Unrooted) =>
                    global_split_string(&global, &global_universe)?,
            };
            let outcome = *menu.readout.terminal_to_outcome.get(&key)
                .ok_or(Error::MissingTerminal { menu_index, key })?;
            sum_into(&mut blocks[menu_index][outcome], &row.polynomial, limits, &mut work)?;
        }
    }
    // Each menu is a law. A temporary exact total is checked separately from
    // retained output accounting, with the remaining work budget preserved.
    for block in &blocks {
        let mut mass = Polynomial::zero(dimension);
        let mut sum_work = Work { coefficient_work: work.coefficient_work, retained_terms: 0 };
        for outcome in block { sum_into(&mut mass, outcome, limits, &mut sum_work)?; }
        work.coefficient_work = sum_work.coefficient_work;
        if mass != Polynomial::one(dimension) {
            return Err(Error::Internal("WORD_READOUT_FORMAL_MENU_MASS"));
        }
    }
    Ok(Batch { word, menus, blocks, work })
}
