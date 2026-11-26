//! PRIVATE SOURCE-ONLY selected-prefix recorder candidate; no compilation claim.
//! Uses the unchanged parity_solver public word_row, not a second law engine.
//! Historical source providers: d009 step projection; 19924449 finite history;
//! b122 initialized history; 8bba once-drawn natural private seed/history product.
//! Exact native/typed carrier, conditional row and compiler-order binding remain
//! separate. Range witnesses are not asserted literal Code path endpoints.
use parity_solver::{polynomial::Polynomial, q, Rational,
    source_calendar::{Origin,Phase}, source_epoch::{self as epoch,SelectedView,Transition},
    source_fit_bank::Bank, source_population::Snapshot, source_word as word};
use num_integer::Integer;
use num_traits::{One,Signed,Zero};
use std::collections::{BTreeMap,BTreeSet};

#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub struct StateId(pub u32);
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub struct PathId(pub u32);
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Order {
    NativeAgenda,
    /// Original cohort Exit and Enter permutations are retained literally.
    /// This is supplied order, not authenticated Lean Finset.toList order.
    SuppliedCohortOrder(Vec<word::Symbol>),
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum End { After(usize), BeforeCommon(usize) }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Limits {
    pub queries:usize, pub branches:usize, pub term_products:usize,
    pub frontier_paths:usize, pub states:usize, pub nodes:usize,
    pub cached_destinations:usize, pub term_slots:usize, pub exponent_cells:usize,
    pub arithmetic_steps:usize, pub rational_bits:usize, pub power_exponent:usize,
}
impl Default for Limits {
    fn default()->Self {Self {queries:4096,branches:65_536,term_products:262_144,
        frontier_paths:4096,states:8192,nodes:65_536,cached_destinations:4096,
        term_slots:65_536,exponent_cells:4_194_304,arithmetic_steps:1_000_000,
        rational_bits:4096,power_exponent:4096}}
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Spec {
    pub order:Order, pub end:End, pub limits:Limits,
    /// Separate limits for the unchanged natural/one-letter child calls.
    pub child_word_limits:word::Limits, pub provider_limits:word::ProviderLimits,
}
impl Default for Spec {
    fn default()->Self {Self {order:Order::NativeAgenda,end:End::After(0),
        limits:Limits::default(),child_word_limits:word::Limits::default(),
        provider_limits:word::ProviderLimits::default()}}
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Stage {Initialization,Letter(usize),FinalMass}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum LimitKind {Queries,Branches,TermProducts,FrontierPaths,States,Nodes,
    CachedDestinations,ReservedTermSlots,ExponentCells,ArithmeticSteps,RationalBits,PowerExponent}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Limit {pub stage:Stage,pub kind:LimitKind,pub required:usize,pub cap:usize}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum UnknownCause {
    Recorder(Limit),
    /// Child stage/kind/population/counts stay unchanged. outer_stage binds
    /// a one-letter child stage to its position in the longer prefix.
    Child {outer_stage:Stage,entering:Option<StateId>,limit:word::Limit},
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Unknown {pub cause:UnknownCause,pub observed:Work}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Error {InvalidInput(&'static str),Internal(&'static str),
    Child {outer_stage:Stage,error:word::Error}}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum OrderRelation {NativeAscendingIds,SuppliedCohortOrder}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct PrivateSite {pub original_hybrid:usize,pub original_vertex:usize}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct SelectedState {
    pub view:SelectedView,
    /// Stable first deterministic arrival; only conditional range metadata.
    pub conditional_range_witness:Snapshot,
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct HistoryNode {pub parent:Option<PathId>,pub state:StateId,pub depth:usize}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct RecordRow {pub leaf:PathId,pub polynomial:Polynomial}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct QueryReceipt {pub stage:Stage,pub entering:Option<StateId>,
    pub destinations:usize,pub terms:usize,pub child_work:word::Work}
#[derive(Clone,Debug,PartialEq,Eq,Default)]
pub struct Work {
    pub initializer_calls:usize,pub conditional_calls:usize,pub branches:usize,
    pub term_products:usize,pub arithmetic_steps:usize,pub states:usize,pub nodes:usize,
    pub largest_frontier:usize,pub largest_frontier_terms:usize,
    pub largest_reserved_term_slots:usize,pub completed_queries:Vec<QueryReceipt>,
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct Table<'a> {
    bank:&'a Bank,spec:Spec,variables:Vec<word::Variable>,exact_order:Vec<word::Symbol>,
    origins:Vec<Origin>,prefix_len:usize,private_site:Option<PrivateSite>,relation:OrderRelation,
    states:Vec<SelectedState>,nodes:Vec<HistoryNode>,rows:Vec<RecordRow>,work:Work,
}
impl<'a> Table<'a> {
    pub fn bank(&self)->&'a Bank {self.bank}
    pub fn spec(&self)->&Spec {&self.spec}
    pub fn variables(&self)->&[word::Variable] {&self.variables}
    pub fn exact_order(&self)->&[word::Symbol] {&self.exact_order}
    pub fn origins(&self)->&[Origin] {&self.origins}
    pub fn prefix_len(&self)->usize {self.prefix_len}
    pub fn private_site(&self)->Option<PrivateSite> {self.private_site}
    pub fn order_relation(&self)->OrderRelation {self.relation}
    pub fn states(&self)->&[SelectedState] {&self.states}
    pub fn nodes(&self)->&[HistoryNode] {&self.nodes}
    pub fn rows(&self)->&[RecordRow] {&self.rows}
    pub fn work(&self)->&Work {&self.work}
    pub fn compiler_literal_order_bound(&self)->bool {false}
    pub fn literal_code_history_verified(&self)->bool {false}
    pub fn native_refinement_verified(&self)->bool {false}
    pub fn source_admission_verified(&self)->bool {false}
    pub fn timed_history_supported(&self)->bool {false}
    /// Entering complete SELECTED view followed by every selected endpoint.
    pub fn record_views(&self,leaf:PathId)->Result<Vec<&SelectedView>,Error> {
        let mut result=Vec::new();let mut cursor=Some(leaf);
        while let Some(id)=cursor {
            if result.len()>self.prefix_len {return Err(Error::Internal("PREFIX_DAG_DEPTH"));}
            let node=self.nodes.get(id.0 as usize).ok_or(Error::InvalidInput("PREFIX_PATH_ID"))?;
            let state=self.states.get(node.state.0 as usize).ok_or(Error::Internal("PREFIX_STATE_ID"))?;
            result.push(&state.view);
            if let Some(parent)=node.parent {
                let previous=self.nodes.get(parent.0 as usize).ok_or(Error::Internal("PREFIX_PARENT"))?;
                if previous.depth.checked_add(1)!=Some(node.depth)||parent.0>=id.0 {
                    return Err(Error::Internal("PREFIX_PARENT_DEPTH"));
                }
            } else if node.depth!=0 {return Err(Error::Internal("PREFIX_ROOT_DEPTH"));}
            cursor=node.parent;
        }
        result.reverse();Ok(result)
    }
    /// Original initialized bit, not another coin or independence assertion.
    pub fn stored_seed(&self,leaf:PathId,hid:usize)->Result<bool,Error> {
        let hybrid=self.bank.hybrids().get(hid).ok_or(Error::InvalidInput("PREFIX_HYBRID_ID"))?;
        let views=self.record_views(leaf)?;
        let entering=views.first().ok_or(Error::Internal("PREFIX_EMPTY_RECORD"))?;
        let bit=*entering.register.get(hybrid.vertex).ok_or(Error::Internal("PREFIX_REGISTER"))?;
        if views.iter().any(|view|view.register!=entering.register) {
            return Err(Error::Internal("PREFIX_REGISTER_CHANGED"));
        }
        Ok(bit)
    }
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Decision<'a> {Table(Table<'a>),Unknown(Unknown)}
#[derive(Debug)]
enum Failure {Unknown(UnknownCause),Error(Error)}
impl From<Error> for Failure {fn from(value:Error)->Self {Self::Error(value)}}
fn add(a:usize,b:usize)->Result<usize,Error> {
    a.checked_add(b).ok_or(Error::Internal("PREFIX_COUNT_OVERFLOW"))
}
fn multiply(a:usize,b:usize)->Result<usize,Error> {
    a.checked_mul(b).ok_or(Error::Internal("PREFIX_COUNT_OVERFLOW"))
}
fn check(stage:Stage,kind:LimitKind,required:usize,cap:usize)->Result<(),Failure> {
    if required>cap {Err(Failure::Unknown(UnknownCause::Recorder(Limit {stage,kind,required,cap})))}
    else {Ok(())}
}
fn validate_limits(spec:&Spec)->Result<(),Error> {
    let l=spec.limits;let h=Limits {rational_bits:65_536,..Limits::default()};
    let recorder=[(l.queries,h.queries),(l.branches,h.branches),(l.term_products,h.term_products),
        (l.frontier_paths,h.frontier_paths),(l.states,h.states),(l.nodes,h.nodes),
        (l.cached_destinations,h.cached_destinations),(l.term_slots,h.term_slots),
        (l.exponent_cells,h.exponent_cells),(l.arithmetic_steps,h.arithmetic_steps),
        (l.rational_bits,h.rational_bits),(l.power_exponent,h.power_exponent)];
    let w=spec.child_word_limits;let wd=word::Limits::default();
    let child=[(w.initial_assignments,wd.initial_assignments),(w.initial_terms,wd.initial_terms),
        (w.queries,wd.queries),(w.branches,wd.branches),(w.term_products,wd.term_products),
        (w.destinations,wd.destinations),(w.terms,wd.terms)];
    let p=spec.provider_limits;let pd=word::ProviderLimits::default();
    let provider=[(p.epoch.calls,pd.epoch.calls),(p.epoch.destinations,pd.epoch.destinations),
        (p.epoch.lifted_terms,pd.epoch.lifted_terms),(p.epoch.branches,pd.epoch.branches),
        (p.epoch.term_products,pd.epoch.term_products),(p.boundary.assignments,pd.boundary.assignments),
        (p.boundary.destinations,pd.boundary.destinations),(p.boundary.term_contributions,pd.boundary.term_contributions),
        (p.completion.calls,pd.completion.calls),(p.completion.destinations,pd.completion.destinations),
        (p.completion.lifted_terms,pd.completion.lifted_terms)];
    if recorder.iter().chain(child.iter()).chain(provider.iter()).any(|(value,cap)|value>cap) {
        return Err(Error::InvalidInput("PREFIX_LIMIT_HARD_MAX"));
    }
    Ok(())
}
struct Prepared {order:Vec<word::Symbol>,origins:Vec<Origin>,prefix_len:usize,
    private_site:Option<PrivateSite>,relation:OrderRelation,variables:Vec<word::Variable>}
fn prepare(bank:&Bank,spec:&Spec)->Result<Prepared,Error> {
    validate_limits(spec)?;let base=bank.symbolic_word();
    if !matches!(&base.initial,word::Initial::Natural)||base.word.len()>32
        ||base.slots>16||bank.coordinates().len()>256 {
        return Err(Error::Internal("PREFIX_BANK_SCOPE"));
    }
    let (order,relation)=match &spec.order {
        Order::NativeAgenda=>(base.word.clone(),OrderRelation::NativeAscendingIds),
        Order::SuppliedCohortOrder(letters)=>{
            if letters.len()>32 {return Err(Error::InvalidInput("PREFIX_ORDER_CAP"));}
            (letters.clone(),OrderRelation::SuppliedCohortOrder)
        }
    };
    if order.len()!=base.word.len() {return Err(Error::InvalidInput("PREFIX_ORDER_LENGTH"));}
    let agenda=bank.agenda();
    if agenda.cohorts.len()!=agenda.dates.len()||agenda.origins.len()!=order.len()
        ||agenda.slots.len()!=base.slots {return Err(Error::Internal("PREFIX_BANK_AGENDA"));}
    let mut origins=Vec::with_capacity(order.len());let mut position=0;
    for cohort in &agenda.cohorts {
        let mut exits=BTreeSet::new();
        for _ in &cohort.exits {
            let edge=match order.get(position) {Some(word::Symbol::Exit(e))=>*e,
                _=>return Err(Error::InvalidInput("PREFIX_EXIT_PHASE"))};
            if !cohort.exits.contains(&edge)||!exits.insert(edge) {
                return Err(Error::InvalidInput("PREFIX_EXIT_OCCURRENCE"));
            }
            origins.push(Origin {date_index:cohort.date_index,phase:Phase::Exit,index:edge});position=add(position,1)?;
        }
        let mut nodes=BTreeSet::new();
        for _ in &cohort.vertices {
            let vertex=match order.get(position) {Some(word::Symbol::Enter(v))=>*v,
                _=>return Err(Error::InvalidInput("PREFIX_ENTER_PHASE"))};
            if !cohort.vertices.contains(&vertex)||!nodes.insert(vertex) {
                return Err(Error::InvalidInput("PREFIX_NODE_OCCURRENCE"));
            }
            origins.push(Origin {date_index:cohort.date_index,phase:Phase::Enter,index:vertex});position=add(position,1)?;
        }
        if add(cohort.date_index,1)?<agenda.cohorts.len() {
            let slot=cohort.date_index;
            if order.get(position)!=Some(&word::Symbol::Interval(slot)) {
                return Err(Error::InvalidInput("PREFIX_INTERVAL_ORDER"));
            }
            let declared=agenda.slots.get(slot).ok_or(Error::Internal("PREFIX_SLOT"))?;
            if declared.slot!=slot||declared.duration<=q(0,1) {
                return Err(Error::Internal("PREFIX_SLOT_DURATION"));
            }
            origins.push(Origin {date_index:cohort.date_index,phase:Phase::Interval,index:slot});position=add(position,1)?;
        }
    }
    if position!=order.len() {return Err(Error::InvalidInput("PREFIX_ORDER_TRAILING"));}
    let (prefix_len,private_site)=match spec.end {
        End::After(count)=>{
            if count>order.len() {return Err(Error::InvalidInput("PREFIX_END_RANGE"));}(count,None)
        }
        End::BeforeCommon(hid)=>{
            let hybrid=base.context.source.hybrids.get(hid).ok_or(Error::InvalidInput("PREFIX_HYBRID_ID"))?;
            if base.common.get(hid)!=Some(&true) {return Err(Error::InvalidInput("PREFIX_REQUIRES_COMMON"));}
            let index=order.iter().position(|symbol|*symbol==word::Symbol::Enter(hybrid.vertex))
                .ok_or(Error::Internal("PREFIX_MISSING_SITE"))?;
            (index,Some(PrivateSite {original_hybrid:hid,original_vertex:hybrid.vertex}))
        }
    };
    let variables=bank.coordinates().iter().map(|c|c.variable).collect();
    Ok(Prepared {order,origins,prefix_len,private_site,relation,variables})
}

/// Capped exact sparse rational arithmetic only. No initializer, stochastic
/// transition, routing, calendar, or clock recurrence is implemented here.
struct Arithmetic {limits:Limits,steps:usize}
impl Arithmetic {
    fn value(&self,stage:Stage,value:&Rational)->Result<(),Failure> {
        let bits=usize::try_from(value.numer().bits().max(value.denom().bits()))
            .map_err(|_|Error::Internal("PREFIX_BIT_COUNT"))?;
        check(stage,LimitKind::RationalBits,bits,self.limits.rational_bits)?;
        if !value.denom().is_positive()||value.numer().gcd(value.denom())!=num_bigint::BigInt::one() {
            return Err(Error::Internal("PREFIX_NONCANONICAL_COEFFICIENT").into());
        }
        Ok(())
    }
    fn step(&mut self,stage:Stage)->Result<(),Failure> {
        let required=add(self.steps,1)?;
        check(stage,LimitKind::ArithmeticSteps,required,self.limits.arithmetic_steps)?;self.steps=required;Ok(())
    }
    fn scalar_add(&mut self,stage:Stage,a:&Rational,b:&Rational)->Result<Rational,Failure> {
        self.value(stage,a)?;self.value(stage,b)?;self.step(stage)?;
        let result=a+b;self.value(stage,&result)?;Ok(result)
    }
    fn scalar_multiply(&mut self,stage:Stage,a:&Rational,b:&Rational)->Result<Rational,Failure> {
        self.value(stage,a)?;self.value(stage,b)?;self.step(stage)?;
        let result=a*b;self.value(stage,&result)?;Ok(result)
    }
    fn polynomial(&self,stage:Stage,p:&Polynomial,dimension:usize)->Result<(),Failure> {
        if p.dimension!=dimension {return Err(Error::Internal("PREFIX_POLYNOMIAL_BANK").into());}
        for (powers,coefficient) in &p.terms {
            if powers.len()!=dimension||coefficient.is_zero() {
                return Err(Error::Internal("PREFIX_NONCANONICAL_POLYNOMIAL").into());
            }
            self.value(stage,coefficient)?;
            for power in powers {check(stage,LimitKind::PowerExponent,*power,self.limits.power_exponent)?;}
        }
        Ok(())
    }
    fn term(&mut self,stage:Stage,p:&mut Polynomial,powers:Vec<usize>,coefficient:Rational)->Result<(),Failure> {
        if coefficient.is_zero() {return Ok(());}
        self.value(stage,&coefficient)?;
        let value=match p.terms.get(&powers) {Some(old)=>self.scalar_add(stage,old,&coefficient)?,None=>coefficient};
        if value.is_zero() {p.terms.remove(&powers);} else {p.terms.insert(powers,value);}Ok(())
    }
    fn sum_into(&mut self,stage:Stage,p:&mut Polynomial,other:Polynomial)->Result<(),Failure> {
        if p.dimension!=other.dimension {return Err(Error::Internal("PREFIX_POLYNOMIAL_BANK").into());}
        for (powers,coefficient) in other.terms {self.term(stage,p,powers,coefficient)?;}Ok(())
    }
    fn product(&mut self,stage:Stage,a:&Polynomial,b:&Polynomial)->Result<Polynomial,Failure> {
        if a.dimension!=b.dimension {return Err(Error::Internal("PREFIX_POLYNOMIAL_BANK").into());}
        let mut result=Polynomial::zero(a.dimension);
        for (pa,ca) in &a.terms {for (pb,cb) in &b.terms {
            let mut powers=Vec::with_capacity(a.dimension);
            for (x,y) in pa.iter().zip(pb) {
                let power=add(*x,*y)?;check(stage,LimitKind::PowerExponent,power,self.limits.power_exponent)?;powers.push(power);
            }
            let coefficient=self.scalar_multiply(stage,ca,cb)?;self.term(stage,&mut result,powers,coefficient)?;
        }}Ok(result)
    }
}
fn row_terms(row:&BTreeMap<PathId,Polynomial>)->Result<usize,Error> {
    row.values().try_fold(0,|sum,p|add(sum,p.terms.len()))
}
fn transition_terms(row:&[Transition])->Result<usize,Error> {
    row.iter().try_fold(0,|sum,t|add(sum,t.polynomial.terms.len()))
}
struct Builder<'a> {
    bank:&'a Bank,spec:Spec,prepared:Prepared,
    states:Vec<SelectedState>,state_index:BTreeMap<String,StateId>,
    nodes:Vec<HistoryNode>,node_index:BTreeMap<(Option<PathId>,StateId),PathId>,
    arithmetic:Arithmetic,work:Work,
}
impl<'a> Builder<'a> {
    fn reserve(&mut self,stage:Stage,terms:usize)->Result<(),Failure> {
        check(stage,LimitKind::ReservedTermSlots,terms,self.spec.limits.term_slots)?;
        check(stage,LimitKind::ExponentCells,multiply(terms,self.prepared.variables.len())?,self.spec.limits.exponent_cells)?;
        self.work.largest_reserved_term_slots=self.work.largest_reserved_term_slots.max(terms);Ok(())
    }
    fn child_request(&self,initial:word::Initial,letters:Vec<word::Symbol>)->word::Request {
        let mut request=self.bank.symbolic_word().clone();
        request.initial=initial;request.word=letters;request.terminal=word::Terminal::FullView;
        request.limits=self.spec.child_word_limits;request.provider_limits=self.spec.provider_limits;request
    }
    fn child(&mut self,stage:Stage,entering:Option<StateId>,request:&word::Request)->Result<word::Table,Failure> {
        match entering {None=>self.work.initializer_calls=add(self.work.initializer_calls,1)?,
            Some(_)=>self.work.conditional_calls=add(self.work.conditional_calls,1)?}
        let decision=word::word_row(request).map_err(|error|Error::Child {outer_stage:stage,error})?;
        let table=match decision {word::Decision::Table(t)=>t,
            word::Decision::Unknown(limit)=>return Err(Failure::Unknown(UnknownCause::Child {outer_stage:stage,entering,limit}))};
        if table.variables!=self.prepared.variables {return Err(Error::Internal("PREFIX_CHILD_VARIABLE_BANK").into());}
        if entering.is_some()&&(table.work.initial_assignments!=1||table.work.initial_term_contributions!=1||table.work.queries!=1) {
            return Err(Error::Internal("PREFIX_CONDITIONAL_QUERY_NOT_SINGLE_STEP").into());
        }
        if entering.is_none()&&table.work.queries!=0 {return Err(Error::Internal("PREFIX_INITIALIZER_NOT_EMPTY_WORD").into());}
        Ok(table)
    }
    fn validate_row(&mut self,stage:Stage,row:&[Transition],register:Option<&[bool]>)->Result<(),Failure> {
        let mut mass=Polynomial::zero(self.prepared.variables.len());
        for t in row {
            let actual=epoch::selected_view(&self.bank.symbolic_word().context,&t.witness)
                .map_err(|_|Error::Internal("PREFIX_RANGE_WITNESS"))?;
            if actual!=t.view||register.is_some_and(|r|r!=t.view.register.as_slice()) {
                return Err(Error::Internal("PREFIX_RANGE_OR_REGISTER_CHANGED").into());
            }
            self.arithmetic.polynomial(stage,&t.polynomial,self.prepared.variables.len())?;
            self.arithmetic.sum_into(stage,&mut mass,t.polynomial.clone())?;
        }
        if mass!=Polynomial::one(self.prepared.variables.len()) {return Err(Error::Internal("PREFIX_CHILD_MASS_IDENTITY").into());}Ok(())
    }
    fn intern_state(&mut self,stage:Stage,t:&Transition)->Result<StateId,Failure> {
        let key=epoch::selected_key(&t.view);
        if let Some(id)=self.state_index.get(&key) {
            if self.states[id.0 as usize].view!=t.view {return Err(Error::Internal("PREFIX_STATE_KEY_COLLISION").into());}return Ok(*id);
        }
        check(stage,LimitKind::States,add(self.states.len(),1)?,self.spec.limits.states)?;
        let id=StateId(u32::try_from(self.states.len()).map_err(|_|Error::Internal("PREFIX_STATE_ID"))?);
        self.states.push(SelectedState {view:t.view.clone(),conditional_range_witness:t.witness.clone()});
        self.state_index.insert(key,id);self.work.states=self.states.len();Ok(id)
    }
    fn intern_node(&mut self,stage:Stage,parent:Option<PathId>,state:StateId)->Result<PathId,Failure> {
        let key=(parent,state);if let Some(id)=self.node_index.get(&key) {return Ok(*id);}
        check(stage,LimitKind::Nodes,add(self.nodes.len(),1)?,self.spec.limits.nodes)?;
        let depth=match parent {None=>0,Some(id)=>add(self.nodes.get(id.0 as usize).ok_or(Error::Internal("PREFIX_PARENT"))?.depth,1)?};
        let expected=match stage {Stage::Initialization=>0,Stage::Letter(i)=>add(i,1)?,
            Stage::FinalMass=>return Err(Error::Internal("PREFIX_FINAL_NODE").into())};
        if depth!=expected {return Err(Error::Internal("PREFIX_NODE_STAGE").into());}
        let id=PathId(u32::try_from(self.nodes.len()).map_err(|_|Error::Internal("PREFIX_PATH_ID"))?);
        self.nodes.push(HistoryNode {parent,state,depth});self.node_index.insert(key,id);self.work.nodes=self.nodes.len();Ok(id)
    }
    fn stage_frontier(&mut self,stage:Stage,row:&BTreeMap<PathId,Polynomial>)->Result<(),Failure> {
        check(stage,LimitKind::FrontierPaths,row.len(),self.spec.limits.frontier_paths)?;
        let terms=row_terms(row)?;self.reserve(stage,terms)?;
        self.work.largest_frontier=self.work.largest_frontier.max(row.len());
        self.work.largest_frontier_terms=self.work.largest_frontier_terms.max(terms);Ok(())
    }
    fn compose(&mut self)->Result<BTreeMap<PathId,Polynomial>,Failure> {
        // prepare() validates full input/order before any resource refusal.
        self.arithmetic.value(Stage::Initialization,&q(1,1))?;
        let initial_request=self.child_request(word::Initial::Natural,Vec::new());
        let initial=self.child(Stage::Initialization,None,&initial_request)?;
        let initial_terms=transition_terms(&initial.transitions)?;
        self.reserve(Stage::Initialization,multiply(2,initial_terms)?)?;
        check(Stage::Initialization,LimitKind::FrontierPaths,initial.transitions.len(),self.spec.limits.frontier_paths)?;
        self.validate_row(Stage::Initialization,&initial.transitions,None)?;
        self.work.completed_queries.push(QueryReceipt {stage:Stage::Initialization,entering:None,
            destinations:initial.transitions.len(),terms:initial_terms,child_work:initial.work});
        let mut current:BTreeMap<PathId,Polynomial>=BTreeMap::new();
        for t in initial.transitions {
            let state=self.intern_state(Stage::Initialization,&t)?;
            let leaf=self.intern_node(Stage::Initialization,None,state)?;
            if current.insert(leaf,t.polynomial).is_some() {return Err(Error::Internal("PREFIX_DUPLICATE_INITIAL_RECORD").into());}
        }
        self.stage_frontier(Stage::Initialization,&current)?;
        for index in 0..self.prepared.prefix_len {
            let stage=Stage::Letter(index);let letter=self.prepared.order[index];
            let entering=current.keys().map(|id|self.nodes[id.0 as usize].state).collect::<BTreeSet<_>>();
            check(stage,LimitKind::Queries,add(self.work.conditional_calls,entering.len())?,self.spec.limits.queries)?;
            let current_terms=row_terms(&current)?;
            // Cache one conditional row per selected current state at this
            // stage, without combining their distinct parent-history masses.
            let mut conditional:BTreeMap<StateId,Vec<Transition>>=BTreeMap::new();
            let mut cached_rows=0;let mut cached_terms=0;
            for state in entering {
                let witness=self.states[state.0 as usize].conditional_range_witness.clone();let register=witness.register.clone();
                let request=self.child_request(word::Initial::Conditional(witness),vec![letter]);
                let result=self.child(stage,Some(state),&request)?;
                let terms=transition_terms(&result.transitions)?;let rows=add(cached_rows,result.transitions.len())?;
                check(stage,LimitKind::CachedDestinations,rows,self.spec.limits.cached_destinations)?;
                self.reserve(stage,add(add(current_terms,cached_terms)?,multiply(2,terms)?)?)?;
                self.validate_row(stage,&result.transitions,Some(&register))?;
                cached_rows=rows;cached_terms=add(cached_terms,terms)?;
                self.work.completed_queries.push(QueryReceipt {stage,entering:Some(state),destinations:result.transitions.len(),terms,child_work:result.work});
                conditional.insert(state,result.transitions);
            }
            let mut stage_branches=0;let mut stage_products=0;
            for (parent,p) in &current {
                let destinations=conditional.get(&self.nodes[parent.0 as usize].state).ok_or(Error::Internal("PREFIX_CACHE_ENTRY"))?;
                stage_branches=add(stage_branches,destinations.len())?;
                stage_products=add(stage_products,multiply(p.terms.len(),transition_terms(destinations)?)?)?;
            }
            let branches=add(self.work.branches,stage_branches)?;let products=add(self.work.term_products,stage_products)?;
            check(stage,LimitKind::Branches,branches,self.spec.limits.branches)?;
            check(stage,LimitKind::TermProducts,products,self.spec.limits.term_products)?;
            self.work.branches=branches;self.work.term_products=products;
            let mut next:BTreeMap<PathId,Polynomial>=BTreeMap::new();let mut next_terms=0;
            for (parent,p) in &current {
                let destinations=conditional.get(&self.nodes[parent.0 as usize].state).ok_or(Error::Internal("PREFIX_CACHE_ENTRY"))?;
                for destination in destinations {
                    let raw=multiply(p.terms.len(),destination.polynomial.terms.len())?;
                    self.reserve(stage,add(add(add(current_terms,cached_terms)?,next_terms)?,raw)?)?;
                    let product=self.arithmetic.product(stage,p,&destination.polynomial)?;
                    if product.is_zero() {continue;}
                    let state=self.intern_state(stage,destination)?;let key=(Some(*parent),state);
                    let existing=self.node_index.get(&key).copied();
                    if existing.is_none_or(|id|!next.contains_key(&id)) {
                        check(stage,LimitKind::FrontierPaths,add(next.len(),1)?,self.spec.limits.frontier_paths)?;
                    }
                    // Crucial: parent PathId, not merely the parent selected
                    // state, remains part of the next complete record key.
                    let leaf=self.intern_node(stage,Some(*parent),state)?;
                    if let Some(old)=next.get_mut(&leaf) {
                        let before=old.terms.len();self.arithmetic.sum_into(stage,old,product)?;
                        next_terms=add(next_terms.checked_sub(before).ok_or(Error::Internal("PREFIX_TERM_COUNT"))?,old.terms.len())?;
                        if old.is_zero() {next.remove(&leaf);}
                    } else {next_terms=add(next_terms,product.terms.len())?;next.insert(leaf,product);}
                }
            }
            self.stage_frontier(stage,&next)?;current=next;
        }
        let terms=row_terms(&current)?;self.reserve(Stage::FinalMass,multiply(2,terms)?)?;
        let mut mass=Polynomial::zero(self.prepared.variables.len());
        for p in current.values() {self.arithmetic.sum_into(Stage::FinalMass,&mut mass,p.clone())?;}
        if mass!=Polynomial::one(self.prepared.variables.len()) {return Err(Error::Internal("PREFIX_RECORD_MASS_IDENTITY").into());}
        Ok(current)
    }
}
/// No public serializer/command or source/native refinement is supplied.
/// Success describes the explicitly complete selected endpoint-vector observer.
pub fn selected_prefix_record<'a>(bank:&'a Bank,spec:&Spec)->Result<Decision<'a>,Error> {
    let prepared=prepare(bank,spec)?;
    let mut b=Builder {bank,spec:spec.clone(),prepared,states:Vec::new(),state_index:BTreeMap::new(),
        nodes:Vec::new(),node_index:BTreeMap::new(),arithmetic:Arithmetic {limits:spec.limits,steps:0},work:Work::default()};
    let outcome=b.compose();b.work.arithmetic_steps=b.arithmetic.steps;
    match outcome {
        Ok(rows)=>Ok(Decision::Table(Table {bank,spec:b.spec,variables:b.prepared.variables,
            exact_order:b.prepared.order,origins:b.prepared.origins,prefix_len:b.prepared.prefix_len,
            private_site:b.prepared.private_site,relation:b.prepared.relation,states:b.states,nodes:b.nodes,
            rows:rows.into_iter().map(|(leaf,polynomial)|RecordRow {leaf,polynomial}).collect(),work:b.work})),
        Err(Failure::Unknown(cause))=>Ok(Decision::Unknown(Unknown {cause,observed:b.work})),
        Err(Failure::Error(error))=>Err(error),
    }
}
