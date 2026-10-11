//! Private proposed controls; uncompiled and unexecuted. No second law engine.
#[path="/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/proposals/selected-prefix-record-20261011T0034Z/source_selected_prefix.rs"]
mod source_selected_prefix;
#[path="/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/selected-prefix-erased-observer-sourceonly-20261011T0254Z/source_erased_selected_observer.rs"]
mod source_erased_selected_observer;
use source_selected_prefix as prefix;
use source_erased_selected_observer as obs;
use parity_solver::{q,forest::{Forest,Tree},polynomial::Polynomial,
    natural_cell::{Source,Edge,Hybrid},source_fit_bank::{self as fit,Bank},
    source_population::{Context,Location},source_epoch::SelectedView,
    source_calendar,source_word as word};
use std::collections::BTreeMap;
const BIG:usize=9_007_199_254_740_993;
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
fn record<'b>(b:&'b Bank,spec:&prefix::Spec)->prefix::Table<'b> {
    match prefix::selected_prefix_record(b,spec).unwrap(){prefix::Decision::Table(t)=>t,
        prefix::Decision::Unknown(u)=>panic!("recorder refused: {u:?}")}
}
fn observe<'s,'b>(t:&'s prefix::Table<'b>,old:usize)->obs::Table<'s,'b> {
    let spec=obs::Spec {original_hybrid:0,old_prefix_len:old,limits:obs::Limits::default()};
    match obs::observe(t,&spec).unwrap(){obs::Decision::Table(t)=>t,
        obs::Decision::Unknown(u)=>panic!("observer refused: {u:?}")}
}
fn variable(t:&prefix::Table<'_>,v:word::Variable)->Polynomial {
    let i=t.variables().iter().position(|x|*x==v).unwrap();
    Polynomial::variable(t.variables().len(),i).unwrap()
}
fn x(t:&prefix::Table<'_>,s:usize,e:usize)->Polynomial {
    variable(t,word::Variable::Survival{slot:s,population:Location::Edge(e)})
}
fn gamma(t:&prefix::Table<'_>,h:usize)->Polynomial {variable(t,word::Variable::OriginalGamma(h))}
fn complement(t:&prefix::Table<'_>,p:&Polynomial)->Polynomial {
    Polynomial::one(t.variables().len()).subtract(p).unwrap()
}
fn add_to(m:&mut BTreeMap<String,Polynomial>,key:String,p:&Polynomial) {
    let q=m.remove(&key).unwrap_or_else(||Polynomial::zero(p.dimension)).add(p).unwrap();
    if !q.is_zero(){m.insert(key,q);}
}
fn no_claims(t:&obs::Table<'_,'_>){
    assert_eq!(t.child_law_queries_added(),0);
    assert!(!t.literal_code_old_supported());assert!(!t.compiler_literal_order_bound());
    assert!(!t.no_private_word_read_source_verified());assert!(!t.native_refinement_verified());
    assert!(!t.source_admission_verified());assert!(!t.timed_history_supported());
    assert!(!t.independence_verified());assert!(!t.common_factorization_verified());
    assert_eq!(t.input().work().initializer_calls,1);
}
// Literal finite expected forests, not another canonicalization recurrence.
// No observer interning or unordered_forest call is used by this flat oracle.
fn two_copy_forest(v:&SelectedView)->Forest {
    match v.genealogy[0].as_ref().unwrap(){
        Tree::Leaf(0)=>{assert_eq!(v.genealogy[1],Some(Tree::Leaf(1)));
            vec![Tree::Leaf(0),Tree::Leaf(BIG)]},
        Tree::Node(a,b)=>{assert!((**a==Tree::Leaf(0)&&**b==Tree::Leaf(1))||
            (**a==Tree::Leaf(1)&&**b==Tree::Leaf(0)));
            assert_eq!(v.genealogy[0],v.genealogy[1]);
            vec![Tree::Node(Box::new(Tree::Leaf(0)),Box::new(Tree::Leaf(BIG)))]},
        other=>panic!("outside explicit two-copy fixture: {other:?}"),
    }
}
fn joint_key(old:&[SelectedView],register:&[bool],forest:&Forest)->String {
    format!("OLD{old:?}REG{register:?}FOREST{forest:?}")
}
fn flat_two_copy_fibres(t:&prefix::Table<'_>,old_len:usize)->BTreeMap<String,Polynomial> {
    let mut m=BTreeMap::new();
    for row in t.rows(){let source=t.record_views(row.leaf).unwrap();
        let mut old=source[..=old_len].iter().map(|v|(*v).clone()).collect::<Vec<_>>();
        for v in &mut old{v.register[3]=false;}
        let final_view=source.last().unwrap();let forest=two_copy_forest(final_view);
        let mut reg=final_view.register.clone();reg[3]=false;
        add_to(&mut m,joint_key(&old,&reg,&forest),&row.polynomial);
    }m
}
fn actual_fibres(t:&obs::Table<'_,'_>)->BTreeMap<String,Polynomial> {
    let mut m=BTreeMap::new();
    for row in t.rows(){let old=t.record_views(row.old_leaf).unwrap().into_iter().cloned().collect::<Vec<_>>();
        add_to(&mut m,joint_key(&old,&row.final_forest_register.register,
            &row.final_forest_register.forest),&row.polynomial);
    }m
}
#[test]
fn empty_once_seed_closed_form_and_full_original_register(){
    let b=bank(vec![],vec![],true);let t=record(&b,&prefix::Spec::default());
    assert_eq!(t.rows().len(),4);let before=format!("{t:?}");let a=observe(&t,0);
    assert_eq!(a.rows().len(),2);let g=gamma(&t,1);
    for r in a.rows(){assert_eq!(r.final_forest_register.register.len(),7);
        assert!(!r.final_forest_register.register[3]);assert!(r.final_forest_register.forest.is_empty());
        assert_eq!(a.record_views(r.old_leaf).unwrap().len(),1);
        let expected=if r.final_forest_register.register[5]{g.clone()}else{complement(&t,&g)};
        assert_eq!(r.polynomial,expected);
        assert!(r.final_forest_register.register.iter().enumerate().all(|(i,b)|i==5||!*b));
    }
    assert_eq!(before,format!("{t:?}"));assert!(std::ptr::eq(a.input(),&t));no_claims(&a);
}
#[test]
fn upper_erasure_keeps_lower_old_correlation_and_exact_parallel_survival_formula(){
    let b=bank(vec![1,1],vec![BIG,0],true);
    let t=record(&b,&prefix::Spec{end:prefix::End::After(13),..prefix::Spec::default()});
    let a=observe(&t,11);let g0=gamma(&t,0);let g1=gamma(&t,1);
    let upper=complement(&t,&g0).multiply(&x(&t,3,2)).unwrap()
        .add(&g0.multiply(&x(&t,3,3)).unwrap()).unwrap();
    let base=x(&t,0,7).multiply(&x(&t,2,4)).unwrap().multiply(&upper).unwrap();
    let expected=[complement(&t,&g1).multiply(&x(&t,1,5)).unwrap().multiply(&base).unwrap(),
        g1.multiply(&x(&t,1,6)).unwrap().multiply(&base).unwrap()];
    let mut unmerged=[Polynomial::zero(t.variables().len()),Polynomial::zero(t.variables().len())];
    let mut seen=[false,false];
    for r in a.rows(){let old=a.record_views(r.old_leaf).unwrap();assert_eq!(old.len(),12);
        assert!(old.iter().all(|v|v.register.len()==7&&!v.register[3]));
        let bit=r.final_forest_register.register[5];seen[usize::from(bit)]=true;
        assert!(old.iter().all(|v|v.register[5]==bit));
        assert!(old[5].population.iter().all(|p|*p==Some(Location::Edge(if bit{6}else{5}))));
        if r.final_forest_register.forest.len()==2{
            let i=usize::from(bit);unmerged[i]=unmerged[i].add(&r.polynomial).unwrap();}
    }
    assert_eq!(seen,[true,true]);assert_eq!(unmerged,expected);
    assert_eq!(actual_fibres(&a),flat_two_copy_fibres(&t,11));no_claims(&a);
}
#[test]
fn flat_full_old_fibres_preserve_distinct_pasts_sharing_final_forest(){
    let b=bank(vec![1,1],vec![BIG,0],true);
    let t=record(&b,&prefix::Spec{end:prefix::End::After(13),..prefix::Spec::default()});
    let a=observe(&t,11);assert_eq!(actual_fibres(&a),flat_two_copy_fibres(&t,11));
    let mut groups=BTreeMap::<String,Vec<obs::PathId>>::new();
    for r in a.rows(){groups.entry(format!("{:?}",r.final_forest_register)).or_default().push(r.old_leaf);}
    let leaves=groups.values().find(|l|l.len()>1).expect("equal final forest, distinct Old");
    assert_ne!(a.record_views(leaves[0]).unwrap(),a.record_views(leaves[1]).unwrap());
    assert!(a.rows().len()<t.rows().len(),"latent h0-only fibres must sum");no_claims(&a);
}
#[test]
fn all_carried_components_large_global_ids_and_literal_tied_order_are_retained(){
    let b=bank(vec![1,1,1],vec![BIG,0,17],true);let t=record(&b,&prefix::Spec::default());
    let a=observe(&t,0);let forest=vec![Tree::Leaf(0),Tree::Leaf(17),Tree::Leaf(BIG)];
    assert!(a.rows().iter().all(|r|r.final_forest_register.forest==forest));no_claims(&a);
    let b=bank(vec![0,1],vec![BIG,0],true);let n=record(&b,&prefix::Spec{
        end:prefix::End::After(2),..prefix::Spec::default()});
    let mut order=b.symbolic_word().word.clone();order.swap(0,1);
    let s=record(&b,&prefix::Spec{order:prefix::Order::SuppliedCohortOrder(order),
        end:prefix::End::After(2),..prefix::Spec::default()});
    let an=observe(&n,2);let as_=observe(&s,2);
    let rn=an.rows().iter().find(|r|!r.final_forest_register.register[5]).unwrap();
    let rs=as_.rows().iter().find(|r|!r.final_forest_register.register[5]).unwrap();
    let v=an.record_views(rn.old_leaf).unwrap();let w=as_.record_views(rs.old_leaf).unwrap();
    assert_eq!(v[0],w[0]);assert_ne!(v[1],w[1]);assert_eq!(v[2],w[2]);
    assert_eq!(actual_fibres(&an),flat_two_copy_fibres(&n,2));
    assert_eq!(actual_fibres(&as_),flat_two_copy_fibres(&s,2));no_claims(&an);no_claims(&as_);
}
#[test]
fn invalid_cut_limits_and_child_unknown_return_no_partial_observation(){
    let b=bank(vec![],vec![],true);let t=record(&b,&prefix::Spec::default());let a=observe(&t,0);
    let mut spec=obs::Spec{original_hybrid:0,old_prefix_len:0,limits:obs::Limits::default()};
    spec.limits.nodes=a.work().projected_nodes;
    match obs::observe(&t,&spec).unwrap(){obs::Decision::Table(v)=>assert_eq!(actual_fibres(&v),actual_fibres(&a)),
        other=>panic!("exact cap refused: {other:?}")};
    spec.limits.nodes-=1;
    assert!(matches!(obs::observe(&t,&spec).unwrap(),obs::Decision::Unknown(obs::Unknown{
        limit:obs::Limit{kind:obs::Kind::Nodes,..},..})));
    for (kind,limits) in [(obs::Kind::InputRows,obs::Limits{input_rows:0,..obs::Limits::default()}),
        (obs::Kind::RationalBits,obs::Limits{rational_bits:0,..obs::Limits::default()}),
        (obs::Kind::ArithmeticSteps,obs::Limits{arithmetic_steps:0,..obs::Limits::default()})]{
        spec.limits=limits;match obs::observe(&t,&spec).unwrap(){
            obs::Decision::Unknown(u)=>{assert_eq!(u.limit.kind,kind);assert!(u.limit.required>u.limit.cap);},
            other=>panic!("zero cap supplied table: {other:?}")}
    }
    spec.original_hybrid=2;
    assert!(matches!(obs::observe(&t,&spec),Err(obs::Error::InvalidInput(_))));
    spec.original_hybrid=0;spec.old_prefix_len=1;
    assert!(matches!(obs::observe(&t,&spec),Err(obs::Error::InvalidInput(_))));
    let b=bank(vec![1,1],vec![BIG,0],true);let mut child=prefix::Spec{
        end:prefix::End::After(1),..prefix::Spec::default()};child.provider_limits.boundary.assignments=0;
    assert!(matches!(prefix::selected_prefix_record(&b,&child).unwrap(),prefix::Decision::Unknown(prefix::Unknown{
        cause:prefix::UnknownCause::Child{..},..})));
    let b=bank(vec![],vec![],false);let t=record(&b,&prefix::Spec::default());
    assert!(matches!(obs::observe(&t,&obs::Spec{original_hybrid:0,old_prefix_len:0,
        limits:obs::Limits::default()}),Err(obs::Error::InvalidInput(_))));no_claims(&a);
}
