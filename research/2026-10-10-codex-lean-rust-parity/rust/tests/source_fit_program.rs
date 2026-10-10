//! Original saved rooted-genealogy program, not a controlled full-Code claim.
//! Literal values and expected probabilities are transcribed from the preserved
//! hybrid-common-sat source-fit result; the same bank is shared by every term.
use parity_solver::{q, Rational, polynomial::Polynomial, natural_cell::{Source,Edge,Hybrid},
    source_calendar, source_fit_bank as bank, source_fit_readout as readout,
    source_population::{Context,tree_string}, source_word};
use std::collections::BTreeMap;

fn polynomial(terms: &[(&[usize],i64,i64)]) -> Polynomial {
    Polynomial { dimension:6, terms:terms.iter().map(|(p,n,d)|(p.to_vec(),q(*n,*d))).collect() }
}
fn saved_common_bank() -> bank::Bank {
    let natural=polynomial(&[(&[0,1,0,1,0,1],1,3),(&[0,0,1,1,0,1],-1,3),
        (&[0,0,1,1,0,0],1,3),(&[0,0,0,0,0,0],-17,135)]);
    let parent0=polynomial(&[(&[0,1,0,1,0,0],1,3),(&[0,0,0,0,0,0],-1,9)]);
    let parent1=polynomial(&[(&[0,0,1,1,0,0],1,3),(&[0,0,0,0,0,0],-2,15)]);
    let randomized=polynomial(&[(&[0,1,0,1,0,0],1,12),(&[0,0,1,1,0,0],1,4),
        (&[0,0,0,0,0,0],-23,180)]);
    let mut equations=Vec::new();
    for row in [natural,parent0,parent1,randomized] {
        equations.push(row.clone());equations.push(row.clone());equations.push(row.scale(&q(-2,1)));
    }
    let request=bank::Request {
        context:Context {source:Source {vertices:5,root:0,
            edges:vec![Edge{source:0,target:1},Edge{source:0,target:2},Edge{source:1,target:2},
                Edge{source:2,target:3},Edge{source:1,target:4}],leaves:vec![3,4],
            hybrids:vec![Hybrid{vertex:2,incoming:[1,2]}]},sample:vec![0,0,1],global_labels:vec![0,1,2]},
        vertex_names:["R","T0","H0","L0","L1"].map(str::to_owned).to_vec(),
        taxon_labels:["L0","L1"].map(str::to_owned).to_vec(),hybrid_labels:vec!["site_alpha".into()],
        copy_labels:["a","b","c"].map(str::to_owned).to_vec(),
        variables:["x0","x1","x2","x3","x4","g_H0"].map(str::to_owned).to_vec(),
        values:[q(1,2),q(2,3),q(4,5),q(1,2),q(1,2),q(1,3)].map(bank::ExactValue::Rational).to_vec(),
        equations,mechanism:bank::Mechanism::Common,terminal:source_word::Terminal::AncestralComplete,
        compiler_limits:source_calendar::CompilerLimits::default(),limits:bank::Limits::default(),
    };
    match bank::bind(&request).unwrap() {bank::Decision::SymbolicBank(bank)=>bank,other=>panic!("{other:?}")}
}
fn probabilities(rows:&[readout::Outcome]) -> BTreeMap<String,Rational> {
    rows.iter().map(|r|(tree_string(&r.tree),r.probability.clone())).collect()
}
fn expected(ab:Rational,other:Rational)->BTreeMap<String,Rational> {
    BTreeMap::from([("((0,1),2)".into(),ab),("((0,2),1)".into(),other.clone()),("(0,(1,2))".into(),other)])
}

#[test]
fn saved_program_keeps_labelled_alpha_laws_and_explicit_label_forgetting() {
    let bank=saved_common_bank();
    let mut request=readout::Request::natural(&bank);
    request.program=vec![
        readout::ProgramTerm{label:"parent0-quarter".into(),weight:q(1,4),forcing:vec![Some(false)]},
        readout::ProgramTerm{label:"parent1-threequarters".into(),weight:q(3,4),forcing:vec![Some(true)]},
    ];
    let table=match readout::readout(&bank,&request).unwrap() {
        readout::Decision::Table(table)=>table,other=>panic!("{other:?}")};
    assert_eq!(bank.hybrids()[0].original_parent_one_probability,q(2,3));
    assert_eq!(bank.forced_parent(0,0).unwrap(),1);
    assert_eq!(bank.forced_parent(0,1).unwrap(),2);
    assert_eq!(table.configurations[0].label,"parent0-quarter");
    assert_eq!(table.configurations[1].label,"parent1-threequarters");
    assert_eq!(probabilities(&table.configurations[0].outcomes),expected(q(7,36),q(1,36)));
    assert_eq!(probabilities(&table.configurations[1].outcomes),expected(q(11,20),q(1,10)));
    assert_eq!(probabilities(table.mixture.as_ref().unwrap()),expected(q(67,90),q(23,180)));
    // This observer specialization never mutates the unforced hidden bank.
    assert_eq!(bank.request().values[5],bank::ExactValue::Rational(q(1,3)));
    // A caller asking to retain labels gets no implicitly coarsened mixture.
    request.forget_configuration_label=false;
    let labelled=match readout::readout(&bank,&request).unwrap() {
        readout::Decision::Table(table)=>table,other=>panic!("{other:?}")};
    assert!(labelled.mixture.is_none());
    assert_eq!(labelled.configurations,table.configurations);
}
