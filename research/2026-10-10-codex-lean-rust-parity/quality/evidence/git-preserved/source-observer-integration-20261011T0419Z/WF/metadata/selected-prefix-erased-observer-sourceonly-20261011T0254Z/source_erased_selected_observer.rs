//! PRIVATE SOURCE-ONLY proposal over frozen source_selected_prefix 46172afa.
//! An observation pushforward, not a second law, initializer or clock engine.
//! Old is the entire erased Selected vector through an explicit past cut.
//! Arbitrary erased literal-Code Old, native refinement and independence are
//! not supplied. Source/typed encoding, order and forest-quotient lemmas remain.
use crate::source_selected_prefix as prefix;
use parity_solver::{forest::Forest, polynomial::Polynomial, q, Rational,
    source_epoch::{self as epoch, SelectedView}, source_population as population,
    source_word as word};
use num_integer::Integer;
use num_traits::{Signed, Zero};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StateId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PathId(pub u32);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub input_states: usize, pub input_nodes: usize, pub input_rows: usize,
    pub input_terms: usize, pub states: usize, pub nodes: usize,
    pub joint_rows: usize, pub term_slots: usize, pub exponent_cells: usize,
    pub arithmetic_steps: usize, pub rational_bits: usize,
}
impl Default for Limits {
    fn default() -> Self { Self { input_states: 8192, input_nodes: 65_536,
        input_rows: 4096, input_terms: 65_536, states: 8192, nodes: 65_536,
        joint_rows: 4096, term_slots: 131_072, exponent_cells: 8_388_608,
        arithmetic_steps: 1_000_000, rational_bits: 4096 } }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Spec {
    pub original_hybrid: usize,
    /// Retains entering view and EVERY endpoint of these first letters. This
    /// must end before the named private COMMON entry. The latent table may
    /// extend later; its endpoint supplies the paired full forest/register.
    pub old_prefix_len: usize,
    pub limits: Limits,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage { Preflight, States, OldPaths, JointFibres, Mass }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind { InputStates, InputNodes, InputRows, InputTerms, States, Nodes,
    JointRows, TermSlots, ExponentCells, ArithmeticSteps, RationalBits }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limit { pub stage: Stage, pub kind: Kind, pub required: usize, pub cap: usize }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error { InvalidInput(&'static str), Internal(&'static str) }
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Work {
    pub input_states: usize, pub input_nodes: usize, pub input_rows: usize,
    pub input_terms: usize, pub forest_helper_calls: usize,
    pub projected_states: usize, pub projected_nodes: usize, pub joint_rows: usize,
    pub output_terms: usize, pub arithmetic_steps: usize, pub largest_term_slots: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Unknown { pub limit: Limit, pub observed: Work }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForestRegister {
    /// FULL original V register: exactly h.vertex is reset; no other slot.
    pub register: Vec<bool>,
    /// Existing Forest type, ALL carried components, canonical global Copy IDs.
    pub forest: Forest,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservedState {
    /// Ordered per-local-Copy tree and original population remain in Old.
    pub erased_selected: SelectedView,
    pub erased_forest_register: ForestRegister,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HistoryNode { pub parent: Option<PathId>, pub state: StateId, pub depth: usize }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointRow {
    pub old_leaf: PathId,
    pub final_forest_register: ForestRegister,
    /// SAME entire input slot/gamma bank; private gamma is not set to zero.
    pub polynomial: Polynomial,
}
#[derive(Debug)]
pub struct Table<'table, 'bank> {
    input: &'table prefix::Table<'bank>, spec: Spec, site: prefix::PrivateSite,
    states: Vec<ObservedState>, nodes: Vec<HistoryNode>, rows: Vec<JointRow>, work: Work,
}
impl<'table, 'bank> Table<'table, 'bank> {
    pub fn input(&self) -> &'table prefix::Table<'bank> { self.input }
    pub fn spec(&self) -> &Spec { &self.spec }
    pub fn site(&self) -> prefix::PrivateSite { self.site }
    pub fn variables(&self) -> &[word::Variable] { self.input.variables() }
    pub fn states(&self) -> &[ObservedState] { &self.states }
    pub fn nodes(&self) -> &[HistoryNode] { &self.nodes }
    pub fn rows(&self) -> &[JointRow] { &self.rows }
    pub fn work(&self) -> &Work { &self.work }
    pub fn record_views(&self, leaf: PathId) -> Result<Vec<&SelectedView>, Error> {
        if self.nodes.get(leaf.0 as usize).ok_or(Error::InvalidInput("ERASED_OLD_PATH_ID"))?.depth
            != self.spec.old_prefix_len {
            return Err(Error::InvalidInput("ERASED_OLD_LEAF_DEPTH"));
        }
        let mut result = Vec::new(); let mut cursor = Some(leaf);
        while let Some(id) = cursor {
            if result.len() > self.spec.old_prefix_len {
                return Err(Error::Internal("ERASED_OLD_PATH_DEPTH"));
            }
            let node = self.nodes.get(id.0 as usize).ok_or(Error::InvalidInput("ERASED_OLD_PATH_ID"))?;
            let state = self.states.get(node.state.0 as usize).ok_or(Error::Internal("ERASED_OLD_STATE_ID"))?;
            result.push(&state.erased_selected);
            match node.parent {
                Some(parent) => {
                    let previous = self.nodes.get(parent.0 as usize).ok_or(Error::Internal("ERASED_OLD_PARENT"))?;
                    if parent.0 >= id.0 || previous.depth.checked_add(1) != Some(node.depth) {
                        return Err(Error::Internal("ERASED_OLD_PARENT_DEPTH"));
                    }
                }
                None if node.depth != 0 => return Err(Error::Internal("ERASED_OLD_ROOT_DEPTH")),
                None => (),
            }
            cursor = node.parent;
        }
        result.reverse(); Ok(result)
    }
    pub fn child_law_queries_added(&self) -> usize { 0 }
    pub fn literal_code_old_supported(&self) -> bool { false }
    pub fn compiler_literal_order_bound(&self) -> bool { false }
    pub fn no_private_word_read_source_verified(&self) -> bool { false }
    pub fn native_refinement_verified(&self) -> bool { false }
    pub fn source_admission_verified(&self) -> bool { false }
    pub fn timed_history_supported(&self) -> bool { false }
    pub fn independence_verified(&self) -> bool { false }
    pub fn common_factorization_verified(&self) -> bool { false }
}
#[derive(Debug)]
pub enum Decision<'table, 'bank> { Table(Table<'table, 'bank>), Unknown(Unknown) }
#[derive(Debug)]
enum Failure { Limit(Limit), Error(Error) }
impl From<Error> for Failure { fn from(e: Error) -> Self { Self::Error(e) } }
fn add(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_add(b).ok_or(Error::Internal("ERASED_OBSERVER_COUNT_OVERFLOW"))
}
fn product(a: usize, b: usize) -> Result<usize, Error> {
    a.checked_mul(b).ok_or(Error::Internal("ERASED_OBSERVER_COUNT_OVERFLOW"))
}
fn check(stage: Stage, kind: Kind, required: usize, cap: usize) -> Result<(), Failure> {
    if required > cap { Err(Failure::Limit(Limit { stage, kind, required, cap })) } else { Ok(()) }
}
fn validate_limits(l: Limits) -> Result<(), Error> {
    let h = Limits { rational_bits: 65_536, ..Limits::default() };
    if [(l.input_states,h.input_states),(l.input_nodes,h.input_nodes),(l.input_rows,h.input_rows),
        (l.input_terms,h.input_terms),(l.states,h.states),(l.nodes,h.nodes),
        (l.joint_rows,h.joint_rows),(l.term_slots,h.term_slots),(l.exponent_cells,h.exponent_cells),
        (l.arithmetic_steps,h.arithmetic_steps),(l.rational_bits,h.rational_bits)]
        .iter().any(|(v,c)| v > c) { return Err(Error::InvalidInput("ERASED_OBSERVER_LIMIT_HARD_MAX")); }
    Ok(())
}
struct Arithmetic { limits: Limits, dimension: usize, steps: usize,
    stored_terms: usize, largest_terms: usize }
impl Arithmetic {
    fn value(&self, stage: Stage, value: &Rational) -> Result<(), Failure> {
        let bits = usize::try_from(value.numer().bits().max(value.denom().bits()))
            .map_err(|_| Error::Internal("ERASED_OBSERVER_BIT_COUNT"))?;
        check(stage,Kind::RationalBits,bits,self.limits.rational_bits)?;
        if !value.denom().is_positive() || &value.numer().gcd(value.denom()) != q(1,1).numer() {
            return Err(Error::Internal("ERASED_OBSERVER_NONCANONICAL_RATIONAL").into());
        }
        Ok(())
    }
    fn polynomial(&self, p: &Polynomial) -> Result<(), Failure> {
        if p.dimension != self.dimension || p.is_zero() {
            return Err(Error::Internal("ERASED_OBSERVER_INPUT_POLYNOMIAL" ).into());
        }
        for (powers,c) in &p.terms {
            if powers.len() != self.dimension || c.is_zero() || powers.iter().any(|e| *e > 4096) {
                return Err(Error::Internal("ERASED_OBSERVER_INPUT_TERM" ).into());
            }
            self.value(Stage::Preflight,c)?;
        }
        Ok(())
    }
    fn term(&mut self, stage: Stage, p: &mut Polynomial, powers: &[usize], c: &Rational)
        -> Result<(), Failure> {
        if p.dimension != self.dimension || powers.len() != self.dimension {
            return Err(Error::Internal("ERASED_OBSERVER_TERM_BANK" ).into());
        }
        self.value(stage,c)?;
        if c.is_zero() { return Ok(()); }
        if let Some(old) = p.terms.get(powers) {
            self.value(stage,old)?;
            let steps = add(self.steps,1)?;
            check(stage,Kind::ArithmeticSteps,steps,self.limits.arithmetic_steps)?;
            self.steps = steps;
            // Both bounded operands are checked before exact Ratio addition;
            // cross-products need at most 2B bits (+1 for numerator addition).
            let sum = old + c; self.value(stage,&sum)?;
            if sum.is_zero() {
                p.terms.remove(powers); self.stored_terms = self.stored_terms.checked_sub(1)
                    .ok_or(Error::Internal("ERASED_OBSERVER_TERM_ACCOUNTING"))?;
            } else { *p.terms.get_mut(powers).ok_or(Error::Internal("ERASED_OBSERVER_TERM_KEY"))? = sum; }
        } else {
            let required = add(self.stored_terms,1)?;
            check(stage,Kind::TermSlots,required,self.limits.term_slots)?;
            check(stage,Kind::ExponentCells,product(required,self.dimension)?,self.limits.exponent_cells)?;
            p.terms.insert(powers.to_vec(),c.clone()); self.stored_terms = required;
            self.largest_terms = self.largest_terms.max(required);
        }
        Ok(())
    }
    fn sum_into(&mut self, stage: Stage, to: &mut Polynomial, from: &Polynomial) -> Result<(), Failure> {
        for (powers,c) in &from.terms { self.term(stage,to,powers,c)?; } Ok(())
    }
}
struct Builder<'table, 'bank> {
    input: &'table prefix::Table<'bank>, spec: Spec, site: prefix::PrivateSite,
    arithmetic: Arithmetic, work: Work,
}
impl<'table, 'bank> Builder<'table, 'bank> {
    fn build(&mut self) -> Result<(Vec<ObservedState>,Vec<HistoryNode>,Vec<JointRow>), Failure> {
        let input = self.input; let l = self.spec.limits;
        // Resource checks precede state/key/mapping clones or moment-free sums.
        self.work.input_states = input.states().len(); self.work.input_nodes = input.nodes().len();
        self.work.input_rows = input.rows().len();
        check(Stage::Preflight,Kind::InputStates,self.work.input_states,l.input_states)?;
        check(Stage::Preflight,Kind::InputNodes,self.work.input_nodes,l.input_nodes)?;
        check(Stage::Preflight,Kind::InputRows,self.work.input_rows,l.input_rows)?;
        self.arithmetic.value(Stage::Preflight,&q(1,1))?;
        for row in input.rows() {
            self.work.input_terms = add(self.work.input_terms,row.polynomial.terms.len())?;
            check(Stage::Preflight,Kind::InputTerms,self.work.input_terms,l.input_terms)?;
            self.arithmetic.polynomial(&row.polynomial)?;
        }
        let context = &input.bank().symbolic_word().context;
        let mut states: Vec<ObservedState> = Vec::new(); let mut state_index: BTreeMap<String,StateId> = BTreeMap::new();
        let mut state_map: Vec<StateId> = Vec::with_capacity(input.states().len());
        for source in input.states() {
            let actual = epoch::selected_view(context,&source.conditional_range_witness)
                .map_err(|_| Error::Internal("ERASED_OBSERVER_RANGE_WITNESS"))?;
            if actual != source.view { return Err(Error::Internal("ERASED_OBSERVER_RANGE_VIEW" ).into()); }
            let mut erased = source.view.clone();
            let bit = erased.register.get_mut(self.site.original_vertex)
                .ok_or(Error::Internal("ERASED_OBSERVER_REGISTER"))?; *bit = false;
            // Reuse the existing full unranked Forest observer, not completed
            // one-tree readout and not a per-copy multiplicity rescaling.
            let forest = population::unordered_forest(context,&source.conditional_range_witness)
                .map_err(|_| Error::Internal("ERASED_OBSERVER_FOREST_WITNESS"))?;
            self.work.forest_helper_calls = add(self.work.forest_helper_calls,1)?;
            let observed = ObservedState { erased_forest_register: ForestRegister {
                register: erased.register.clone(), forest }, erased_selected: erased };
            let key = epoch::selected_key(&observed.erased_selected);
            let id = if let Some(id) = state_index.get(&key) {
                if states[id.0 as usize] != observed {
                    return Err(Error::Internal("ERASED_OBSERVER_VIEW_FOREST_INVARIANCE" ).into());
                } *id
            } else {
                check(Stage::States,Kind::States,add(states.len(),1)?,l.states)?;
                let id = StateId(u32::try_from(states.len()).map_err(|_| Error::Internal("ERASED_OBSERVER_STATE_ID"))?);
                states.push(observed); state_index.insert(key,id); id
            };
            state_map.push(id); self.work.projected_states = states.len();
        }
        let mut nodes: Vec<HistoryNode> = Vec::new();
        let mut node_index: BTreeMap<(Option<PathId>,StateId),PathId> = BTreeMap::new();
        let mut path_map: Vec<PathId> = Vec::with_capacity(input.nodes().len());
        for (source_id,node) in input.nodes().iter().enumerate() {
            let state = *state_map.get(node.state.0 as usize).ok_or(Error::Internal("ERASED_OBSERVER_SOURCE_STATE_ID"))?;
            let parent = match node.parent {
                Some(parent) => {
                    if parent.0 as usize >= source_id { return Err(Error::Internal("ERASED_OBSERVER_SOURCE_PARENT_ORDER" ).into()); }
                    let prior = &input.nodes()[parent.0 as usize];
                    if prior.depth.checked_add(1) != Some(node.depth)
                        || input.states()[prior.state.0 as usize].view.register != input.states()[node.state.0 as usize].view.register {
                        return Err(Error::Internal("ERASED_OBSERVER_SOURCE_DEPTH_OR_LATENT_REGISTER" ).into());
                    }
                    Some(path_map[parent.0 as usize])
                }
                None if node.depth != 0 => return Err(Error::Internal("ERASED_OBSERVER_SOURCE_ROOT_DEPTH" ).into()),
                None => None,
            };
            if node.depth > input.prefix_len() { return Err(Error::Internal("ERASED_OBSERVER_SOURCE_DEPTH" ).into()); }
            let id = if node.depth > self.spec.old_prefix_len {
                parent.ok_or(Error::Internal("ERASED_OBSERVER_OLD_CUT_PARENT"))?
            } else {
                let key = (parent,state);
                if let Some(id) = node_index.get(&key) { *id } else {
                    check(Stage::OldPaths,Kind::Nodes,add(nodes.len(),1)?,l.nodes)?;
                    let id = PathId(u32::try_from(nodes.len()).map_err(|_| Error::Internal("ERASED_OBSERVER_NODE_ID"))?);
                    nodes.push(HistoryNode { parent, state, depth: node.depth }); node_index.insert(key,id); id
                }
            };
            path_map.push(id); self.work.projected_nodes = nodes.len();
        }
        let mut joint: BTreeMap<(PathId,String),JointRow> = BTreeMap::new();
        for row in input.rows() {
            let source = input.nodes().get(row.leaf.0 as usize).ok_or(Error::Internal("ERASED_OBSERVER_SOURCE_LEAF"))?;
            if source.depth != input.prefix_len() { return Err(Error::Internal("ERASED_OBSERVER_SOURCE_LEAF_DEPTH" ).into()); }
            let old_leaf = *path_map.get(row.leaf.0 as usize).ok_or(Error::Internal("ERASED_OBSERVER_PATH_MAP"))?;
            if nodes[old_leaf.0 as usize].depth != self.spec.old_prefix_len {
                return Err(Error::Internal("ERASED_OBSERVER_OLD_LEAF_DEPTH" ).into());
            }
            let final_fr = &states[state_map[source.state.0 as usize].0 as usize].erased_forest_register;
            let register: String = final_fr.register.iter().map(|b|if *b {'1'}else{'0'}).collect();
            let key = (old_leaf,format!("REGISTER[{register}]FOREST{}",population::forest_key(&final_fr.forest)));
            if !joint.contains_key(&key) {
                check(Stage::JointFibres,Kind::JointRows,add(joint.len(),1)?,l.joint_rows)?;
                joint.insert(key.clone(),JointRow { old_leaf, final_forest_register: final_fr.clone(),
                    polynomial: Polynomial::zero(self.arithmetic.dimension) });
            }
            let destination = joint.get_mut(&key).ok_or(Error::Internal("ERASED_OBSERVER_JOINT_KEY"))?;
            if destination.final_forest_register != *final_fr {
                return Err(Error::Internal("ERASED_OBSERVER_FOREST_KEY_COLLISION" ).into());
            }
            self.arithmetic.sum_into(Stage::JointFibres,&mut destination.polynomial,&row.polynomial)?;
            if destination.polynomial.is_zero() { joint.remove(&key); }
            self.work.joint_rows = joint.len();
        }
        let mut mass = Polynomial::zero(self.arithmetic.dimension);
        for row in joint.values() { self.arithmetic.sum_into(Stage::Mass,&mut mass,&row.polynomial)?; }
        if mass != Polynomial::one(self.arithmetic.dimension) {
            return Err(Error::Internal("ERASED_OBSERVER_MASS_IDENTITY" ).into());
        }
        self.arithmetic.stored_terms = self.arithmetic.stored_terms.checked_sub(mass.terms.len())
            .ok_or(Error::Internal("ERASED_OBSERVER_FINAL_TERM_ACCOUNTING"))?;
        self.work.output_terms = self.arithmetic.stored_terms;
        Ok((states,nodes,joint.into_values().collect()))
    }
}

/// No word_row call, initializer, gamma substitution or latent state mutation.
pub fn observe<'table, 'bank>(input: &'table prefix::Table<'bank>, spec: &Spec)
    -> Result<Decision<'table, 'bank>, Error> {
    validate_limits(spec.limits)?;
    let context = &input.bank().symbolic_word().context;
    context.validate().map_err(|_| Error::Internal("ERASED_OBSERVER_INPUT_CONTEXT"))?;
    let h = input.bank().hybrids().get(spec.original_hybrid)
        .ok_or(Error::InvalidInput("ERASED_OBSERVER_HYBRID_ID"))?;
    if input.bank().symbolic_word().common.get(spec.original_hybrid) != Some(&true) {
        return Err(Error::InvalidInput("ERASED_OBSERVER_REQUIRES_COMMON"));
    }
    let entry = input.exact_order().iter().position(|letter| *letter == word::Symbol::Enter(h.vertex))
        .ok_or(Error::Internal("ERASED_OBSERVER_PRIVATE_ENTRY"))?;
    if spec.old_prefix_len > input.prefix_len() || spec.old_prefix_len > entry {
        return Err(Error::InvalidInput("ERASED_OBSERVER_OLD_CUT_AFTER_PRIVATE_READ"));
    }
    if input.prefix_len() > 32 || input.variables().len() > 256 || input.work().initializer_calls != 1 {
        return Err(Error::Internal("ERASED_OBSERVER_INPUT_SCOPE"));
    }
    let variables = input.bank().coordinates().iter().map(|c|c.variable).collect::<Vec<_>>();
    if variables.as_slice() != input.variables() { return Err(Error::Internal("ERASED_OBSERVER_VARIABLE_BANK")); }
    let site = prefix::PrivateSite { original_hybrid: spec.original_hybrid, original_vertex: h.vertex };
    let mut b = Builder { input, spec: *spec, site, work: Work::default(),
        arithmetic: Arithmetic { limits: spec.limits, dimension: variables.len(),
            steps: 0, stored_terms: 0, largest_terms: 0 } };
    let result = b.build(); b.work.arithmetic_steps = b.arithmetic.steps;
    b.work.largest_term_slots = b.arithmetic.largest_terms;
    match result {
        Ok((states,nodes,rows)) => Ok(Decision::Table(Table { input, spec: *spec, site,
            states,nodes,rows,work: b.work })),
        Err(Failure::Limit(limit)) => Ok(Decision::Unknown(Unknown { limit, observed: b.work })),
        Err(Failure::Error(error)) => Err(error),
    }
}
