//! Completed rooted-unranked rational readout from a shared fitted survival bank.
//!
//! Reuses the existing Natural whole-word/ancestral-completion provider. It
//! forgets representative IDs, ordered child orientation and latent register
//! ONLY because that observer is explicitly selected here. It does not return
//! evaluated full-Code/timed laws. Rational edge exponents are collected before
//! integrality is required; no log, algebraic root or decimal is evaluated.
use crate::{forest::Tree, polynomial::Polynomial, q, Rational,
    source_epoch, source_fit_bank::{Bank, Expression},
    source_population::{self as population, Location}, source_word as word};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Observer { RootedUnrankedComplete }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramTerm {
    pub label: String,
    pub weight: Rational,
    /// Explicit rooted-observer polynomial specialization, NOT a controlled
    /// full-register source transition: None=natural, Some(false)=parent0,
    /// Some(true)=parent1. The private register distribution is not preserved.
    pub forcing: Vec<Option<bool>>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub word_rows: usize,
    pub monomial_contributions: usize,
    pub normalized_terms: usize,
    pub arithmetic_steps: usize,
    pub rational_bits: usize,
    pub power_exponent: usize,
}
impl Default for Limits {
    fn default() -> Self { Self { word_rows: 4096, monomial_contributions: 262_144,
        normalized_terms: 65_536, arithmetic_steps: 1_000_000,
        rational_bits: 4096, power_exponent: 4096 } }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub observer: Observer,
    pub program: Vec<ProgramTerm>,
    /// Labelled alpha*law outputs are always preserved. Only this explicit
    /// choice additionally returns their label-forgetting mixture.
    pub forget_configuration_label: bool,
    pub word_limits: word::Limits,
    pub provider_limits: word::ProviderLimits,
    pub limits: Limits,
}
impl Request {
    pub fn natural(bank: &Bank) -> Self {
        Self { observer: Observer::RootedUnrankedComplete,
            program: vec![ProgramTerm { label: "natural".into(), weight: q(1,1),
                forcing: vec![None;bank.hybrids().len()] }],
            forget_configuration_label: true,
            word_limits: word::Limits::default(), provider_limits: word::ProviderLimits::default(),
            limits: Limits::default() }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Limit { pub stage: &'static str, pub kind: &'static str, pub required: String, pub cap: usize }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unknown { Provider(word::Limit), Collection(Limit) }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Unsupported {
    RequiresNaturalCompletedWord,
    UsedInactiveOrAncestralVariable { tree: String, variable: word::Variable },
    ResidualFractionalExponent { tree: String, original_edge: usize, exponent: Rational },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error { InvalidInput(&'static str), Internal(&'static str) }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decision { Table(Table), Unknown(Unknown), Unsupported(Unsupported) }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    /// Global integer labels, not local Copy indices. Decode string labels
    /// using global_labels[i] -> copy_labels[i], never copy_labels[globalID].
    pub tree: Tree,
    /// E-variable polynomial after the explicit readout, gamma specialization
    /// and exact rational-exponent normalization. Includes program weight.
    pub polynomial: Polynomial,
    pub probability: Rational,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigurationLaw { pub label: String, pub weight: Rational, pub forcing: Vec<Option<bool>>, pub outcomes: Vec<Outcome> }
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Work {
    pub word_rows: usize,
    pub monomial_contributions: usize,
    pub largest_normalized_terms: usize,
    pub arithmetic_steps: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    pub observer: Observer,
    /// Literal full ordered rows/range witnesses remain evidence, with their
    /// slot-bank polynomials. They are not evaluated full-Code PMFs here.
    pub word_table: word::Table,
    pub configurations: Vec<ConfigurationLaw>,
    pub mixture: Option<Vec<Outcome>>,
    pub work: Work,
}

#[derive(Debug)]
enum Failure { Unknown(Unknown), Unsupported(Unsupported), Error(Error) }
impl From<Error> for Failure { fn from(error: Error) -> Self { Self::Error(error) } }
fn invalid(code: &'static str) -> Error { Error::InvalidInput(code) }
fn internal(code: &'static str) -> Error { Error::Internal(code) }
fn limit(stage: &'static str, kind: &'static str, required: usize, cap: usize) -> Result<(),Failure> {
    if required > cap { Err(Failure::Unknown(Unknown::Collection(Limit {
        stage,kind,required:required.to_string(),cap }))) } else { Ok(()) }
}
fn bits(value: &Rational) -> usize { value.numer().bits().max(value.denom().bits()) as usize }
fn canonical(value: &Rational) -> bool {
    value.denom().is_positive() && value.numer().gcd(value.denom()) == BigInt::one()
}
struct Arithmetic { limits: Limits, steps: usize }
impl Arithmetic {
    fn check(&self, stage: &'static str, value: &Rational) -> Result<(),Failure> {
        limit(stage,"rational_bits",bits(value),self.limits.rational_bits)
    }
    fn step(&mut self, stage: &'static str) -> Result<(),Failure> {
        let next = self.steps.checked_add(1).ok_or(internal("SOURCE_FIT_READOUT_COUNT"))?;
        limit(stage,"arithmetic_steps",next,self.limits.arithmetic_steps)?;
        self.steps=next; Ok(())
    }
    fn add(&mut self, stage: &'static str, a: &Rational, b: &Rational) -> Result<Rational,Failure> {
        self.check(stage,a)?;self.check(stage,b)?;self.step(stage)?;
        let value=a+b;self.check(stage,&value)?;Ok(value)
    }
    fn multiply(&mut self, stage: &'static str, a: &Rational, b: &Rational) -> Result<Rational,Failure> {
        self.check(stage,a)?;self.check(stage,b)?;self.step(stage)?;
        let value=a*b;self.check(stage,&value)?;Ok(value)
    }
    fn exponent(&self, stage: &'static str, exponent: &BigInt) -> Result<usize,Failure> {
        if exponent.is_negative() { return Err(internal("SOURCE_FIT_READOUT_NEGATIVE_POWER").into()); }
        if exponent > &BigInt::from(self.limits.power_exponent) {
            return Err(Failure::Unknown(Unknown::Collection(Limit {stage,kind:"power_exponent",
                required:exponent.to_string(),cap:self.limits.power_exponent})));
        }
        exponent.to_usize().ok_or_else(||internal("SOURCE_FIT_READOUT_POWER").into())
    }
    fn power(&mut self, stage: &'static str, base: &Rational, exponent: usize) -> Result<Rational,Failure> {
        limit(stage,"power_exponent",exponent,self.limits.power_exponent)?;
        self.check(stage,base)?;
        let mut value=q(1,1);self.check(stage,&value)?;
        let mut factor=base.clone();let mut remaining=exponent;
        while remaining>0 {
            if remaining&1==1 {value=self.multiply(stage,&value,&factor)?;}
            remaining>>=1;
            if remaining>0 {factor=self.multiply(stage,&factor,&factor)?;}
        }
        Ok(value)
    }
}
/// Unused axes remain distinct until all exact cancellation is complete. They
/// cannot be projected to an edge or accidentally treated as fitted cuts.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Monomial { edges: Vec<Rational>, unused: Vec<(usize,usize)> }
struct Group { tree: Tree, terms: BTreeMap<Monomial,Rational> }
type Groups = BTreeMap<String,Group>;

fn validate(bank: &Bank, request: &Request) -> Result<(),Error> {
    let limits=request.limits;
    if limits.word_rows>4096 || limits.monomial_contributions>262_144 || limits.normalized_terms>65_536
        || limits.arithmetic_steps>1_000_000 || limits.rational_bits>65_536 || limits.power_exponent>4096 {
        return Err(invalid("SOURCE_FIT_READOUT_LIMITS"));
    }
    if request.program.is_empty() || request.program.len()>16
        || request.program.iter().any(|term|term.label.is_empty() || term.label.len()>128 || term.label.contains('\0'))
        || request.program.iter().map(|term|&term.label).collect::<BTreeSet<_>>().len()!=request.program.len() {
        return Err(invalid("SOURCE_FIT_READOUT_PROGRAM"));
    }
    for term in &request.program {
        if term.forcing.len()!=bank.hybrids().len() || bits(&term.weight)>65_536
            || !canonical(&term.weight) || !term.weight.is_positive() || term.weight.numer()>term.weight.denom() {
            return Err(invalid("SOURCE_FIT_READOUT_PROGRAM"));
        }
    }
    Ok(())
}
fn accumulate(groups: &mut Groups, tree: &Tree, key: Monomial, coefficient: Rational,
    arithmetic: &mut Arithmetic, count: &mut usize, work: &mut Work) -> Result<(),Failure> {
    if coefficient.is_zero() {return Ok(());}
    let label=population::tree_string(tree);
    let group=groups.entry(label).or_insert_with(||Group {tree:tree.clone(),terms:BTreeMap::new()});
    let previous=group.terms.get(&key).cloned();
    let value=arithmetic.add("NORMALIZE",previous.as_ref().unwrap_or(&q(0,1)),&coefficient)?;
    if value.is_zero() {
        if previous.is_some() {group.terms.remove(&key);*count-=1;}
    } else {
        if previous.is_none() {
            let next=count.checked_add(1).ok_or(internal("SOURCE_FIT_READOUT_COUNT"))?;
            limit("NORMALIZE","normalized_terms",next,arithmetic.limits.normalized_terms)?;
            *count=next;work.largest_normalized_terms=work.largest_normalized_terms.max(next);
        }
        group.terms.insert(key,value);
    }
    Ok(())
}
fn collect(bank: &Bank, table: &word::Table, program: &ProgramTerm,
    arithmetic: &mut Arithmetic, work: &mut Work) -> Result<Groups,Failure> {
    let mut groups=Groups::new();let mut count=0;
    for row in &table.transitions {
        if source_epoch::selected_view(&bank.request().context,&row.witness).map_err(internal)?!=row.view {
            return Err(internal("SOURCE_FIT_READOUT_RANGE_WITNESS").into());
        }
        let forest=population::unordered_forest(&bank.request().context,&row.witness).map_err(internal)?;
        if forest.len()!=1 || row.witness.live.len()!=1
            || row.view.population.iter().any(|place|*place!=Some(Location::Ancestral(bank.request().context.source.root))) {
            return Err(internal("SOURCE_FIT_READOUT_INCOMPLETE_GENEALOGY").into());
        }
        if row.polynomial.dimension!=table.variables.len() {return Err(internal("SOURCE_FIT_READOUT_DIMENSION").into());}
        let tree=&forest[0];
        for (powers,coefficient) in &row.polynomial.terms {
            if powers.len()!=table.variables.len() {return Err(internal("SOURCE_FIT_READOUT_DIMENSION").into());}
            let mut coefficient=arithmetic.multiply("SUBSTITUTE",coefficient,&program.weight)?;
            // Endpoint gamma specialization may cancel a term before any
            // unused-axis/refinement checks. It never changes a forced bit.
            for (index,variable) in table.variables.iter().enumerate() {
                if let word::Variable::OriginalGamma(hybrid)=variable {
                    let value=match program.forcing[*hybrid] {
                        None=>bank.hybrids()[*hybrid].original_parent_one_probability.clone(),
                        Some(false)=>q(0,1),Some(true)=>q(1,1),
                    };
                    let factor=arithmetic.power("SUBSTITUTE",&value,powers[index])?;
                    coefficient=arithmetic.multiply("SUBSTITUTE",&coefficient,&factor)?;
                }
            }
            if coefficient.is_zero() {continue;}
            let mut key=Monomial {edges:vec![q(0,1);bank.edges().len()],unused:Vec::new()};
            for (index,coordinate) in bank.coordinates().iter().enumerate() {if powers[index]>0 {
                match &coordinate.expression {
                    Expression::EdgePower {original_edge,exponent,active:true,..}=>{
                        let amount=arithmetic.multiply("SUBSTITUTE",exponent,&Rational::from_integer(powers[index].into()))?;
                        key.edges[*original_edge]=arithmetic.add("SUBSTITUTE",&key.edges[*original_edge],&amount)?;
                    }
                    Expression::OriginalGamma(_)=>{},
                    Expression::EdgePower {active:false,..}|Expression::AncestralExpNeg {..}=>{
                        key.unused.push((index,powers[index]));
                    }
                }
            }}
            accumulate(&mut groups,tree,key,coefficient,arithmetic,&mut count,work)?;
        }
    }
    Ok(groups)
}
fn evaluate(bank: &Bank, groups: Groups, arithmetic: &mut Arithmetic) -> Result<Vec<Outcome>,Failure> {
    let mut outcomes=Vec::new();
    for (label,group) in groups {if !group.terms.is_empty() {
        let mut polynomial=Polynomial::zero(bank.edges().len());let mut probability=q(0,1);
        for (key,coefficient) in group.terms {
            if let Some((index,_))=key.unused.first() {
                return Err(Failure::Unsupported(Unsupported::UsedInactiveOrAncestralVariable {
                    tree:label.clone(),variable:bank.coordinates()[*index].variable }));
            }
            let mut powers=Vec::with_capacity(key.edges.len());let mut value=coefficient.clone();
            for (edge,exponent) in key.edges.iter().enumerate() {
                if exponent.denom()!=&BigInt::one() {
                    return Err(Failure::Unsupported(Unsupported::ResidualFractionalExponent {
                        tree:label.clone(),original_edge:edge,exponent:exponent.clone() }));
                }
                let exponent=arithmetic.exponent("EVALUATE",exponent.numer())?;
                powers.push(exponent);
                let factor=arithmetic.power("EVALUATE",&bank.edges()[edge].survival,exponent)?;
                value=arithmetic.multiply("EVALUATE",&value,&factor)?;
            }
            polynomial.terms.insert(powers,coefficient);
            probability=arithmetic.add("EVALUATE",&probability,&value)?;
        }
        outcomes.push(Outcome {tree:group.tree,polynomial,probability});
    }}
    Ok(outcomes)
}
fn run(bank: &Bank, request: &Request) -> Result<Table,Failure> {
    if bank.symbolic_word().initial!=word::Initial::Natural
        || bank.symbolic_word().terminal!=word::Terminal::AncestralComplete
        || bank.request().context.sample.is_empty() {
        return Err(Failure::Unsupported(Unsupported::RequiresNaturalCompletedWord));
    }
    let mut arithmetic=Arithmetic {limits:request.limits,steps:0};
    arithmetic.check("INPUT",&q(1,1))?;
    for edge in bank.edges() {arithmetic.check("INPUT",&edge.survival)?;}
    for hybrid in bank.hybrids() {arithmetic.check("INPUT",&hybrid.original_parent_one_probability)?;}
    let mut mass=q(0,1);
    for program in &request.program {mass=arithmetic.add("INPUT",&mass,&program.weight)?;}
    if mass!=q(1,1) {return Err(invalid("SOURCE_FIT_READOUT_PROGRAM_MASS").into());}
    let mut word_request=bank.symbolic_word().clone();
    word_request.limits=request.word_limits;word_request.provider_limits=request.provider_limits;
    let word_table=match word::word_row(&word_request) {
        Ok(word::Decision::Table(table))=>table,
        Ok(word::Decision::Unknown(limit))=>return Err(Failure::Unknown(Unknown::Provider(limit))),
        Err(word::Error::InvalidInput(code))=>return Err(invalid(code).into()),
        Err(word::Error::Unsupported(code))|Err(word::Error::Internal(code))=>return Err(internal(code).into()),
    };
    limit("COLLECT","word_rows",word_table.transitions.len(),request.limits.word_rows)?;
    if word_table.variables.len()!=bank.coordinates().len()
        || word_table.variables.iter().zip(bank.coordinates()).any(|(a,b)|*a!=b.variable) {
        return Err(internal("SOURCE_FIT_READOUT_BANK_LAYOUT").into());
    }
    let terms=word_table.transitions.iter().try_fold(0usize,|sum,row|sum.checked_add(row.polynomial.terms.len()))
        .ok_or(internal("SOURCE_FIT_READOUT_COUNT"))?;
    let contributions=terms.checked_mul(request.program.len()).ok_or(internal("SOURCE_FIT_READOUT_COUNT"))?;
    // Check the raw contribution count before generating collected edge keys.
    limit("COLLECT","monomial_contributions",contributions,request.limits.monomial_contributions)?;
    let mut work=Work {word_rows:word_table.transitions.len(),monomial_contributions:contributions,..Work::default()};
    let mut configurations=Vec::with_capacity(request.program.len());
    let mut mixture=BTreeMap::<String,Outcome>::new();
    let mut mixture_terms=0usize;
    for program in &request.program {
        let groups=collect(bank,&word_table,program,&mut arithmetic,&mut work)?;
        let outcomes=evaluate(bank,groups,&mut arithmetic)?;
        let mut mass=q(0,1);
        for outcome in &outcomes {
            if outcome.probability<q(0,1)||outcome.probability>program.weight {
                return Err(internal("SOURCE_FIT_READOUT_PROBABILITY").into());
            }
            mass=arithmetic.add("MASS",&mass,&outcome.probability)?;
            if request.forget_configuration_label {
                let label=population::tree_string(&outcome.tree);
                let target=mixture.entry(label).or_insert_with(||Outcome {tree:outcome.tree.clone(),
                    polynomial:Polynomial::zero(bank.edges().len()),probability:q(0,1)});
                target.probability=arithmetic.add("MIXTURE",&target.probability,&outcome.probability)?;
                for (powers,coefficient) in &outcome.polynomial.terms {
                    let previous=target.polynomial.terms.get(powers).cloned();
                    let value=arithmetic.add("MIXTURE",previous.as_ref().unwrap_or(&q(0,1)),coefficient)?;
                    if value.is_zero() {
                        if previous.is_some() {target.polynomial.terms.remove(powers);mixture_terms-=1;}
                    } else {
                        if previous.is_none() {
                            let next=mixture_terms.checked_add(1).ok_or(internal("SOURCE_FIT_READOUT_COUNT"))?;
                            limit("MIXTURE","normalized_terms",next,request.limits.normalized_terms)?;
                            mixture_terms=next;work.largest_normalized_terms=work.largest_normalized_terms.max(next);
                        }
                        target.polynomial.terms.insert(powers.clone(),value);
                    }
                }
            }
        }
        if mass!=program.weight {return Err(internal("SOURCE_FIT_READOUT_MASS").into());}
        configurations.push(ConfigurationLaw {label:program.label.clone(),weight:program.weight.clone(),
            forcing:program.forcing.clone(),outcomes});
    }
    let mixture=if request.forget_configuration_label {
        let values=mixture.into_values().collect::<Vec<_>>();let mut mass=q(0,1);
        for value in &values {mass=arithmetic.add("MASS",&mass,&value.probability)?;}
        if mass!=q(1,1) {return Err(internal("SOURCE_FIT_READOUT_MIXTURE_MASS").into());}
        Some(values)
    } else {None};
    work.arithmetic_steps=arithmetic.steps;
    Ok(Table {observer:request.observer,word_table,configurations,mixture,work})
}
/// Natural initialized complete calendar only. An explicit observer is part of
/// the Request; a full ordered-view request is never silently coarsened here.
pub fn readout(bank: &Bank, request: &Request) -> Result<Decision,Error> {
    validate(bank,request)?;
    match run(bank,request) {
        Ok(table)=>Ok(Decision::Table(table)),
        Err(Failure::Unknown(limit))=>Ok(Decision::Unknown(limit)),
        Err(Failure::Unsupported(reason))=>Ok(Decision::Unsupported(reason)),
        Err(Failure::Error(error))=>Err(error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{natural_cell::{Source,Edge},source_fit_bank as bank,source_calendar,
        source_population::Context};

    fn two_tip() -> Bank {
        let request=bank::Request {
            context:Context {source:Source {vertices:3,root:0,
                edges:vec![Edge {source:0,target:1},Edge {source:0,target:2}],leaves:vec![1,2],hybrids:vec![]},
                sample:vec![0,1],global_labels:vec![9007199254740993,0]},
            vertex_names:vec!["R".into(),"L0".into(),"L1".into()],taxon_labels:vec!["tipA".into(),"tipB".into()],
            hybrid_labels:vec![],copy_labels:vec!["a".into(),"b".into()],variables:vec!["x0".into(),"x1".into()],
            values:vec![bank::ExactValue::Rational(q(1,2));2],equations:vec![Polynomial::zero(2)],
            mechanism:bank::Mechanism::Common,terminal:word::Terminal::AncestralComplete,
            compiler_limits:source_calendar::CompilerLimits::default(),limits:bank::Limits::default(),
        };
        match bank::bind(&request).unwrap() {bank::Decision::SymbolicBank(bank)=>bank,_=>panic!("bank")}
    }
    #[test]
    fn existing_natural_word_complete_observer_keeps_large_global_embedding() {
        let bank=two_tip();let request=Request::natural(&bank);
        let table=match readout(&bank,&request).unwrap() {Decision::Table(table)=>table,_=>panic!("table")};
        let outcomes=table.mixture.unwrap();
        assert_eq!(outcomes.len(),1);assert_eq!(outcomes[0].probability,q(1,1));
        assert_eq!(population::tree_string(&outcomes[0].tree),"(0,9007199254740993)");
        assert_eq!(table.configurations[0].weight,q(1,1));
    }
    #[test]
    fn exact_cancellation_precedes_fractional_exponent_rejection() {
        let bank=two_tip();let tree=Tree::Node(Box::new(Tree::Leaf(0)),Box::new(Tree::Leaf(9007199254740993)));
        let key=Monomial {edges:vec![q(1,2),q(0,1)],unused:vec![]};
        let mut arithmetic=Arithmetic {limits:Limits::default(),steps:0};
        let mut groups=Groups::new();let mut count=0;let mut work=Work::default();
        accumulate(&mut groups,&tree,key.clone(),q(1,1),&mut arithmetic,&mut count,&mut work).unwrap();
        accumulate(&mut groups,&tree,key,q(-1,1),&mut arithmetic,&mut count,&mut work).unwrap();
        assert_eq!(count,0);assert!(evaluate(&bank,groups,&mut arithmetic).unwrap().is_empty());
    }
    #[test]
    fn surviving_fraction_and_unused_ancestry_axis_do_not_become_rational_pmfs() {
        let bank=two_tip();let tree=Tree::Node(Box::new(Tree::Leaf(0)),Box::new(Tree::Leaf(9007199254740993)));
        let label=population::tree_string(&tree);
        let mut arithmetic=Arithmetic {limits:Limits::default(),steps:0};
        let mut groups=Groups::new();groups.insert(label.clone(),Group {tree:tree.clone(),
            terms:BTreeMap::from([(Monomial {edges:vec![q(1,2),q(0,1)],unused:vec![]},q(1,1))])});
        assert!(matches!(evaluate(&bank,groups,&mut arithmetic),Err(Failure::Unsupported(
            Unsupported::ResidualFractionalExponent {original_edge:0,..}))));
        let mut groups=Groups::new();groups.insert(label,Group {tree,
            terms:BTreeMap::from([(Monomial {edges:vec![q(0,1);2],unused:vec![(2,1)]},q(1,1))])});
        assert!(matches!(evaluate(&bank,groups,&mut arithmetic),Err(Failure::Unsupported(
            Unsupported::UsedInactiveOrAncestralVariable {variable:word::Variable::Survival {
                population:Location::Ancestral(0),..},..}))));
    }
}

