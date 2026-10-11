//! Private future test harness, authored source-only; never invoked by its author.
//! Original candidate and all linked accepted libraries remain unchanged.
#[path="/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/proposals/selected-prefix-record-20261011T0034Z/source_selected_prefix.rs"]
mod selected_prefix;
use selected_prefix as prefix;
use parity_solver::{q,polynomial::Polynomial,natural_cell::{Source,Edge},
    source_fit_bank::{self as fit,Bank},source_population::{Context,Location},
    source_epoch,source_calendar,source_word as word};
use std::collections::BTreeMap;

const COMMON:&[u8]=include_bytes!("/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/fixtures/source-fit/hybrid-common-sat.request.json");
const INDEPENDENT:&[u8]=include_bytes!("/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity/rust/fixtures/source-fit/hybrid-independent-sat.request.json");
fn checked_bank(raw:&[u8])->Bank {
    let request=calendar_cli::source_fit::parse(raw).expect("saved request parse");
    match fit::bind(&request).expect("saved bank binding") {
        fit::Decision::SymbolicBank(bank)=>bank,
        _=>panic!("saved rational request must bind"),
    }
}
fn ordinary_bank(source:Source,sample:Vec<usize>,global_labels:Vec<usize>)->Bank {
    let edges=source.edges.len();let vertices=source.vertices;let taxa=source.leaves.len();let copies=sample.len();
    let request=fit::Request {
        context:Context {source,sample,global_labels},
        vertex_names:(0..vertices).map(|i|format!("V{i}")).collect(),
        taxon_labels:(0..taxa).map(|i|format!("T{i}")).collect(),
        hybrid_labels:Vec::new(),copy_labels:(0..copies).map(|i|format!("C{i}")).collect(),
        variables:(0..edges).map(|i|format!("x{i}")).collect(),
        values:vec![fit::ExactValue::Rational(q(1,2));edges],
        equations:vec![Polynomial::zero(edges)],mechanism:fit::Mechanism::Common,
        terminal:word::Terminal::FullView,compiler_limits:source_calendar::CompilerLimits::default(),
        limits:fit::Limits::default(),
    };
    match fit::bind(&request).expect("input-only ordinary bank binding") {
        fit::Decision::SymbolicBank(bank)=>bank,
        _=>panic!("ordinary rational bank must bind"),
    }
}
fn two_tip_bank()->Bank {
    ordinary_bank(Source {vertices:3,root:0,edges:vec![Edge{source:0,target:1},Edge{source:0,target:2}],
        leaves:vec![1,2],hybrids:Vec::new()},vec![0,1],vec![13,2])
}
fn split_edge_bank()->Bank {
    ordinary_bank(Source {vertices:5,root:0,edges:vec![Edge{source:0,target:1},Edge{source:0,target:2},
        Edge{source:2,target:3},Edge{source:2,target:4}],leaves:vec![1,3,4],hybrids:Vec::new()},
        vec![0,0],vec![13,2])
}
fn table<'a>(bank:&'a Bank,spec:&prefix::Spec)->prefix::Table<'a> {
    match prefix::selected_prefix_record(bank,spec).expect("record should execute") {
        prefix::Decision::Table(table)=>table,
        prefix::Decision::Unknown(value)=>panic!("unexpected operational refusal: {value:?}"),
    }
}
fn aggregate(table:&prefix::Table<'_>)->BTreeMap<String,Polynomial> {
    let mut result=BTreeMap::<String,Polynomial>::new();
    for row in table.rows() {
        let node=table.nodes()[row.leaf.0 as usize];
        let key=source_epoch::selected_key(&table.states()[node.state.0 as usize].view);
        let sum=result.remove(&key).unwrap_or_else(||Polynomial::zero(table.variables().len()))
            .add(&row.polynomial).unwrap();
        if !sum.is_zero(){result.insert(key,sum);}
    }
    result
}
fn marginal_from_word(bank:&Bank)->BTreeMap<String,Polynomial> {
    let mut request=bank.symbolic_word().clone();request.terminal=word::Terminal::FullView;
    match word::word_row(&request).expect("existing full word") {
        word::Decision::Table(table)=>table.transitions.into_iter()
            .map(|t|(source_epoch::selected_key(&t.view),t.polynomial)).collect(),
        word::Decision::Unknown(value)=>panic!("unchanged full word refused: {value:?}"),
    }
}
fn assert_false_gates(table:&prefix::Table<'_>) {
    assert!(!table.compiler_literal_order_bound());assert!(!table.literal_code_history_verified());
    assert!(!table.native_refinement_verified());assert!(!table.source_admission_verified());
    assert!(!table.timed_history_supported());
}
fn unknown(bank:&Bank,spec:&prefix::Spec)->prefix::Unknown {
    match prefix::selected_prefix_record(bank,spec).expect("limit is not invalid input") {
        prefix::Decision::Unknown(value)=>value,
        prefix::Decision::Table(_)=>panic!("limit unexpectedly returned table"),
    }
}

#[test]
fn natural_initializer_once_asymmetric_seed_and_empty_entering_record() {
    let bank=checked_bank(COMMON);assert_eq!(bank.hybrids()[0].original_parent_one_probability,q(2,3));
    let mut spec=prefix::Spec::default();spec.limits.queries=0;
    let empty=table(&bank,&spec);assert_false_gates(&empty);
    assert_eq!(empty.work().initializer_calls,1);assert_eq!(empty.work().conditional_calls,0);
    assert!(empty.rows().iter().all(|row|empty.record_views(row.leaf).unwrap().len()==1));
    let dimension=empty.variables().len();
    let gamma_index=empty.variables().iter().position(|v|*v==word::Variable::OriginalGamma(0)).unwrap();
    let gamma=Polynomial::variable(dimension,gamma_index).unwrap();
    for (record,expected) in [(empty,gamma.clone()),(table(&bank,&prefix::Spec {
        end:prefix::End::BeforeCommon(0),..prefix::Spec::default()}),gamma)] {
        let mut masses=[Polynomial::zero(dimension),Polynomial::zero(dimension)];
        for row in record.rows() {
            let bit=record.stored_seed(row.leaf,0).unwrap();
            masses[usize::from(bit)]=masses[usize::from(bit)].add(&row.polynomial).unwrap();
            let views=record.record_views(row.leaf).unwrap();
            assert!(views.iter().all(|view|view.register==views[0].register));
        }
        assert_eq!(masses[1],expected);
        assert_eq!(masses[0],Polynomial::one(dimension).subtract(&expected).unwrap());
        assert_eq!(record.work().initializer_calls,1);
        for query in record.work().completed_queries.iter().filter(|q|q.entering.is_some()) {
            assert_eq!(query.child_work.initial_assignments,1);assert_eq!(query.child_work.initial_term_contributions,1);
            assert_eq!(query.child_work.queries,1);
        }
        assert_false_gates(&record);
    }
}

#[test]
fn distinct_prefix_histories_share_final_state_with_closed_form_split_edge_mass() {
    let bank=split_edge_bank();assert_eq!(bank.ages(),&[q(2,1),q(0,1),q(1,1),q(0,1),q(0,1)]);
    let record=table(&bank,&prefix::Spec {end:prefix::End::After(bank.symbolic_word().word.len()),
        ..prefix::Spec::default()});
    let mut fibres=BTreeMap::<String,Vec<prefix::PathId>>::new();
    for row in record.rows() {
        let views=record.record_views(row.leaf).unwrap();
        assert_eq!(views.len(),record.prefix_len()+1);
        fibres.entry(source_epoch::selected_key(views.last().unwrap())).or_default().push(row.leaf);
    }
    let same_final=fibres.values().find(|paths|paths.len()>1).expect("two merge timings share final view");
    assert_ne!(record.record_views(same_final[0]).unwrap(),record.record_views(same_final[1]).unwrap());
    let dimension=record.variables().len();
    let axes=(0..2).map(|slot|record.variables().iter().position(|v|
        *v==word::Variable::Survival{slot,population:Location::Edge(0)}).unwrap()).collect::<Vec<_>>();
    let expected=Polynomial::one(dimension).subtract(&Polynomial::variable(dimension,axes[0]).unwrap()
        .multiply(&Polynomial::variable(dimension,axes[1]).unwrap()).unwrap()).unwrap().scale(&q(1,2));
    let marginal=aggregate(&record);
    let ordered_key=fibres.keys().find(|key|key.contains("(0,1)")).expect("ordered graft endpoint");
    assert_eq!(&marginal[ordered_key],&expected);
    assert_eq!(marginal,marginal_from_word(&bank));assert_false_gates(&record);
}

#[test]
fn complete_endpoint_marginals_match_existing_common_and_independent_word() {
    for raw in [COMMON,INDEPENDENT] {
        let bank=checked_bank(raw);let record=table(&bank,&prefix::Spec {
            end:prefix::End::After(bank.symbolic_word().word.len()),..prefix::Spec::default()});
        assert_eq!(aggregate(&record),marginal_from_word(&bank));
        assert_eq!(record.work().initializer_calls,1);assert_false_gates(&record);
        assert_eq!(record.work().conditional_calls,record.work().completed_queries.iter().filter(|q|q.entering.is_some()).count());
    }
}

#[test]
fn tied_entries_keep_literal_intermediate_order_and_reject_bad_order_before_caps() {
    let bank=two_tip_bank();let native=table(&bank,&prefix::Spec {end:prefix::End::After(2),..prefix::Spec::default()});
    let mut order=bank.symbolic_word().word.clone();assert_eq!(&order[..2],&[word::Symbol::Enter(1),word::Symbol::Enter(2)]);
    order.swap(0,1);
    let supplied=table(&bank,&prefix::Spec {order:prefix::Order::SuppliedCohortOrder(order.clone()),
        end:prefix::End::After(2),..prefix::Spec::default()});
    assert_eq!(native.rows().len(),1);assert_eq!(supplied.rows().len(),1);
    let a=native.record_views(native.rows()[0].leaf).unwrap();let b=supplied.record_views(supplied.rows()[0].leaf).unwrap();
    assert_eq!(a[0],b[0]);assert_ne!(a[1],b[1]);assert_eq!(a[2],b[2]);
    assert_eq!(aggregate(&native),aggregate(&supplied));
    assert_eq!(supplied.order_relation(),prefix::OrderRelation::SuppliedCohortOrder);assert_false_gates(&supplied);
    order[0]=word::Symbol::Exit(0);
    let mut invalid=prefix::Spec {order:prefix::Order::SuppliedCohortOrder(order),end:prefix::End::After(2),..prefix::Spec::default()};
    invalid.limits.rational_bits=0;invalid.limits.queries=0;
    assert!(matches!(prefix::selected_prefix_record(&bank,&invalid),Err(prefix::Error::InvalidInput(_))));
}

#[test]
fn recorder_and_child_unknown_keep_exact_metadata_and_no_partial_table() {
    let bank=two_tip_bank();let mut spec=prefix::Spec {end:prefix::End::After(1),..prefix::Spec::default()};
    spec.limits.queries=0;
    let refused=unknown(&bank,&spec);
    assert!(matches!(refused.cause,prefix::UnknownCause::Recorder(prefix::Limit {
        stage:prefix::Stage::Letter(0),kind:prefix::LimitKind::Queries,required:1,cap:0})));
    assert_eq!(refused.observed.initializer_calls,1);assert_eq!(refused.observed.conditional_calls,0);
    let mut child=prefix::Spec {end:prefix::End::After(1),..prefix::Spec::default()};child.provider_limits.boundary.assignments=0;
    let refused=unknown(&bank,&child);
    match refused.cause {
        prefix::UnknownCause::Child {outer_stage:prefix::Stage::Letter(0),entering:Some(_),limit}=>{
            assert_eq!(limit.stage,word::Stage::Letter(0));assert_eq!(limit.required,1);assert_eq!(limit.cap,0);
            assert_eq!(limit.kind,word::LimitKind::Boundary(parity_solver::source_boundary::LimitKind::Assignments));
            assert_eq!(limit.population,None);
        },other=>panic!("child metadata changed: {other:?}"),
    }
    let good=table(&bank,&prefix::Spec {end:prefix::End::After(2),..prefix::Spec::default()});
    let mut exact=prefix::Spec {end:prefix::End::After(2),..prefix::Spec::default()};exact.limits.nodes=good.work().nodes;
    assert_eq!(table(&bank,&exact).rows(),good.rows());
    exact.limits.nodes-=1;
    assert!(matches!(unknown(&bank,&exact).cause,prefix::UnknownCause::Recorder(prefix::Limit {kind:prefix::LimitKind::Nodes,..})));
    let mut empty=prefix::Spec::default();empty.limits.rational_bits=0;
    assert_eq!(unknown(&bank,&empty).observed.initializer_calls,0);
}
