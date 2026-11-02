//! NEW PRIVATE SOURCE-ONLY control; uncompiled/unexecuted at this freeze.
//! Reuses the accepted recorder and exact historical serial bank constructor.
//! Oracle = literal full Selected vectors + directly expanded signed-Q terms.
//! No kernel, word_row, flat pushforward, erasure or tree canonicalizer in oracle.
#[path="source_selected_prefix.rs"]
mod source_selected_prefix;
use source_selected_prefix as prefix;
use parity_solver::{q,Rational,forest::Tree,polynomial::Polynomial,
    natural_cell::{Source,Edge,Hybrid},source_fit_bank::{self as fit,Bank},
    source_population::{Context,Location},source_epoch::SelectedView,
    source_calendar,source_word as word};
use std::collections::BTreeMap;
const BIG:usize=9_007_199_254_740_993;
// Verbatim fn bank body from accepted8cd harness, retained with provenance.
fn bank(sample:Vec<usize>,global_labels:Vec<usize>,common:bool)->Bank {
    assert!(usize::BITS>=64);
    let source=Source {vertices:7,root:0,edges:vec![Edge{source:0,target:1},
        Edge{source:0,target:2},Edge{source:2,target:3},Edge{source:2,target:3},
        Edge{source:3,target:4},Edge{source:4,target:5},Edge{source:4,target:5},
        Edge{source:5,target:6}],leaves:vec![1,6],hybrids:vec![
        Hybrid{vertex:3,incoming:[2,3]},Hybrid{vertex:5,incoming:[5,6]}]};
    let copies=sample.len();let mut values=vec![fit::ExactValue::Rational(q(1,2));8];
    values.extend([fit::ExactValue::Rational(q(2,3)),fit::ExactValue::Rational(q(3,5))]);
    let mut variables=(0..8).map(|i|format!("x{i}")).collect::<Vec<_>>();
    variables.extend(["g_V3".into(),"g_V5".into()]);
    let request=fit::Request {context:Context{source,sample,global_labels},
        vertex_names:(0..7).map(|i|format!("V{i}")).collect(),
        taxon_labels:vec!["T0".into(),"T1".into()],hybrid_labels:vec!["H0".into(),"H1".into()],
        copy_labels:(0..copies).map(|i|format!("C{i}")).collect(),variables,values,
        equations:vec![Polynomial::zero(10)],
        mechanism:if common{fit::Mechanism::Common}else{fit::Mechanism::Independent},
        terminal:word::Terminal::FullView,compiler_limits:source_calendar::CompilerLimits::default(),
        limits:fit::Limits::default()};
    let b=match fit::bind(&request).unwrap(){fit::Decision::SymbolicBank(b)=>b,
        other=>panic!("supplied rational bank refused: {other:?}")};
    assert_eq!(b.ages(),&[q(5,1),q(0,1),q(4,1),q(3,1),q(2,1),q(1,1),q(0,1)]);
    assert_eq!(b.hybrids()[0].original_parent_one_probability,q(1,3));
    assert_eq!(b.hybrids()[1].original_parent_one_probability,q(2,5));
    assert_eq!(b.symbolic_word().word,vec![word::Symbol::Enter(1),word::Symbol::Enter(6),
        word::Symbol::Interval(0),word::Symbol::Exit(7),word::Symbol::Enter(5),
        word::Symbol::Interval(1),word::Symbol::Exit(5),word::Symbol::Exit(6),
        word::Symbol::Enter(4),word::Symbol::Interval(2),word::Symbol::Exit(4),
        word::Symbol::Enter(3),word::Symbol::Interval(3),word::Symbol::Exit(2),
        word::Symbol::Exit(3),word::Symbol::Enter(2),word::Symbol::Interval(4),
        word::Symbol::Exit(0),word::Symbol::Exit(1),word::Symbol::Enter(0)]);
    b
}

const DIMENSION:usize=47;
const X07:usize=7;
const G0:usize=45;
const G1:usize=46;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum History {Early(bool),Late(bool),Unmerged}
#[derive(Clone,Debug)]
struct Expected {bits:(bool,bool),history:History,views:Vec<SelectedView>,polynomial:Polynomial}
#[derive(Clone,Debug)]
struct Actual {leaf:prefix::PathId,views:Vec<SelectedView>,polynomial:Polynomial}
// Explicit expansion of (G0 or1-G0)*(G1 or1-G1), not Polynomial multiplication.
fn seed_terms(bits:(bool,bool))->&'static[(usize,usize,i64)] {
    match bits {
        (false,false)=>&[(0,0,1),(1,0,-1),(0,1,-1),(1,1,1)],
        (false,true)=>&[(0,1,1),(1,1,-1)],
        (true,false)=>&[(1,0,1),(1,1,-1)],
        (true,true)=>&[(1,1,1)],
    }
}
// Clock tuple = (power of X07,power of X1chosen,numerator,denominator).
const EARLY:&[(usize,usize,i64,i64)]=&[(0,0,1,2),(1,0,-1,2)];
const LATE:&[(usize,usize,i64,i64)]=&[(1,0,1,2),(1,1,-1,2)];
const UNMERGED:&[(usize,usize,i64,i64)]=&[(1,1,1,1)];
const ORDERED_FINAL:&[(usize,usize,i64,i64)]=&[(0,0,1,2),(1,1,-1,2)];
fn direct_polynomial(bits:(bool,bool),clock:&[(usize,usize,i64,i64)])->Polynomial {
    let mut terms=BTreeMap::new();let y=14+usize::from(bits.1);
    for &(a,b,seed_sign) in seed_terms(bits) {
        for &(x_power,y_power,n,d) in clock {
            let mut powers=vec![0;DIMENSION];
            powers[G0]=a;powers[G1]=b;powers[X07]=x_power;powers[y]=y_power;
            assert!(terms.insert(powers,q(seed_sign*n,d)).is_none(),"oracle term identity");
        }
    }
    Polynomial{dimension:DIMENSION,terms}
}
fn literal_view(bits:(bool,bool),place:Location,ordered:Option<bool>)->SelectedView {
    let genealogy=match ordered {
        None=>vec![Some(Tree::Leaf(0)),Some(Tree::Leaf(1))],
        Some(first)=>{
            let (a,b)=if first{(0,1)}else{(1,0)};
            let t=Tree::Node(Box::new(Tree::Leaf(a)),Box::new(Tree::Leaf(b)));
            vec![Some(t.clone()),Some(t)]
        }
    };
    SelectedView {genealogy,population:vec![Some(place);2],
        register:vec![false,false,false,bits.0,false,bits.1,false]}
}
// Literal positions: entry, Enter1, Enter6, Interval0, Exit7, Enter5, Interval1.
// No transition/helper/selected_key/ancestor reconstruction is called here.
fn manual_record(bits:(bool,bool),history:History)->Vec<SelectedView> {
    let early=match history {History::Early(first)=>Some(first),_=>None};
    let final_tree=match history {History::Early(first)|History::Late(first)=>Some(first),
        History::Unmerged=>None};
    let chosen=Location::Edge(if bits.1{6}else{5});
    vec![literal_view(bits,Location::Node(6),None),
        literal_view(bits,Location::Node(6),None),
        literal_view(bits,Location::Edge(7),None),
        literal_view(bits,Location::Edge(7),early),
        literal_view(bits,Location::Node(5),early),
        literal_view(bits,chosen,early),
        literal_view(bits,chosen,final_tree)]
}
fn expected_rows()->Vec<Expected> {
    let mut rows=Vec::new();
    for upper in [false,true] {for lower in [false,true] {
        let bits=(upper,lower);
        for history in [History::Early(true),History::Early(false),History::Late(true),
            History::Late(false),History::Unmerged] {
            let clock=match history {History::Early(_)=>EARLY,History::Late(_)=>LATE,
                History::Unmerged=>UNMERGED};
            rows.push(Expected{bits,history,views:manual_record(bits,history),
                polynomial:direct_polynomial(bits,clock)});
        }
    }}
    rows
}
fn expected_variables()->Vec<word::Variable> {
    let mut v=Vec::new();
    for slot in 0..5 {
        for edge in 0..8 {v.push(word::Variable::Survival{slot,population:Location::Edge(edge)});}
        v.push(word::Variable::Survival{slot,population:Location::Ancestral(0)});
    }
    v.push(word::Variable::OriginalGamma(0));v.push(word::Variable::OriginalGamma(1));v
}
fn seed_at_point(bits:(bool,bool))->Rational {
    match bits {(false,false)=>q(2,5),(false,true)=>q(4,15),
        (true,false)=>q(1,5),(true,true)=>q(2,15)}
}
fn diagnostic_point()->Vec<Rational> {
    // A separate formal-coordinate diagnostic, not the captured fitted bank.
    let mut p=vec![q(1,2);DIMENSION];p[X07]=q(2,3);
    p[14]=q(3,5);p[15]=q(3,5);p[G0]=q(1,3);p[G1]=q(2,5);p
}
fn unique_actual<'a>(rows:&'a[Actual],views:&[SelectedView])->&'a Actual {
    let found=rows.iter().filter(|r|r.views==views).collect::<Vec<_>>();
    assert_eq!(found.len(),1,"complete record must have one canonical coefficient row");found[0]
}
#[test]
fn serial_early_late_mergers_keep_entire_history_and_signed_coefficients() {
    let b=bank(vec![1,1],vec![BIG,0],true);
    assert_eq!(b.symbolic_word().common,vec![true,true]);
    let symbols=[word::Symbol::Enter(1),word::Symbol::Enter(6),word::Symbol::Interval(0),
        word::Symbol::Exit(7),word::Symbol::Enter(5),word::Symbol::Interval(1)];
    assert_eq!(&b.symbolic_word().word[..6],symbols.as_slice());
    let spec=prefix::Spec{end:prefix::End::After(6),..prefix::Spec::default()};
    let t=match prefix::selected_prefix_record(&b,&spec).unwrap(){prefix::Decision::Table(t)=>t,
        prefix::Decision::Unknown(u)=>panic!("finite control needs a complete table: {u:?}")};
    assert_eq!(t.prefix_len(),6);assert_eq!(t.exact_order()[..6],symbols);
    assert_eq!(t.variables(),expected_variables().as_slice());
    assert_eq!(t.work().initializer_calls,1);
    assert!(!t.compiler_literal_order_bound());assert!(!t.literal_code_history_verified());
    assert!(!t.native_refinement_verified());assert!(!t.source_admission_verified());
    assert!(!t.timed_history_supported());
    let actual=t.rows().iter().map(|row|Actual{leaf:row.leaf,
        views:t.record_views(row.leaf).unwrap().into_iter().cloned().collect(),
        polynomial:row.polynomial.clone()}).collect::<Vec<_>>();
    let expected=expected_rows();assert_eq!(actual.len(),20);assert_eq!(expected.len(),20);
    assert_eq!(expected.iter().map(|r|r.polynomial.terms.len()).sum::<usize>(),81);
    assert_eq!(actual.iter().map(|r|r.polynomial.terms.len()).sum::<usize>(),81);
    let point=diagnostic_point();
    for e in &expected {
        let a=unique_actual(&actual,&e.views);
        assert_eq!(a.views.len(),7);assert_eq!(a.polynomial,e.polynomial,
            "entire signed coefficient map at bits {:?}, history {:?}",e.bits,e.history);
        assert_eq!(t.stored_seed(a.leaf,0).unwrap(),e.bits.0);
        assert_eq!(t.stored_seed(a.leaf,1).unwrap(),e.bits.1);
        let conditional=match e.history {History::Early(_)=>q(1,6),
            History::Late(_)=>q(2,15),History::Unmerged=>q(2,5)};
        assert_eq!(a.polynomial.evaluate(&point).unwrap()/seed_at_point(e.bits),conditional);
    }
    // Complete row coverage forbids extra or duplicated paths, even if their
    // final marginal is normalized. Native selected_key is not the oracle key.
    for a in &actual {assert_eq!(expected.iter().filter(|e|e.views==a.views).count(),1);}
    for upper in [false,true] {for lower in [false,true] {for first in [false,true] {
        let bits=(upper,lower);let e=unique_actual(&actual,&manual_record(bits,History::Early(first)));
        let l=unique_actual(&actual,&manual_record(bits,History::Late(first)));
        assert_ne!(e.leaf,l.leaf);assert_eq!(e.views.last(),l.views.last());
        assert_eq!(e.views[..3],l.views[..3]);assert_ne!(e.views[3],l.views[3]);
        assert_eq!(t.nodes()[e.leaf.0 as usize].state,t.nodes()[l.leaf.0 as usize].state,
            "shared final state must retain different parent paths");
        let total=e.polynomial.add(&l.polynomial).unwrap();
        assert_eq!(total,direct_polynomial(bits,ORDERED_FINAL));
        assert_eq!(total.evaluate(&point).unwrap()/seed_at_point(bits),q(3,10));
    }}}
    let mass=actual.iter().fold(Polynomial::zero(DIMENSION),|sum,r|sum.add(&r.polynomial).unwrap());
    assert_eq!(mass,Polynomial::one(DIMENSION));
}
