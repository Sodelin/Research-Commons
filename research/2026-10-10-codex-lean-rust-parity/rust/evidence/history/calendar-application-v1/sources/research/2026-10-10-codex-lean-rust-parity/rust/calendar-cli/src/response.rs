//! Canonical public framing; fields preserve the accepted private payloads.
use crate::request::RequestDto;
use parity_solver::{canonical, forest::Tree, polynomial::Polynomial,
    source_calendar as calendar, source_epoch::SelectedView,
    source_population::{Location, Snapshot}, source_word as word};
use serde_json::{json, Value};

pub const MAX_RESULT_BYTES: usize = 4 * 1024 * 1024;
pub const SCHEMA: &str = "source_calendar_result_v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind { InvalidRequest, Internal, ExecutionFailure }
impl ErrorKind {
    fn wire(self) -> &'static str { match self {
        Self::InvalidRequest => "INVALID_REQUEST", Self::Internal => "INTERNAL",
        Self::ExecutionFailure => "EXECUTION_FAILURE",
    } }
}
#[derive(Clone, Debug)]
pub struct Frame { pub value: Value, pub exit_code: u8, pub diagnostic: Option<String> }
impl Frame {
    pub fn error(kind: ErrorKind, diagnostic: impl Into<String>) -> Self {
        Self { value: json!({"schema": SCHEMA, "status": "ERROR", "error": kind.wire()}),
            exit_code: 1, diagnostic: Some(diagnostic.into()) }
    }
    pub fn bytes(&self) -> Vec<u8> { canonical_json(&self.value) }
    pub fn bounded(self) -> Self {
        if self.bytes().len() > MAX_RESULT_BYTES {
            Self::error(ErrorKind::ExecutionFailure, "SOURCE_CALENDAR_RESULT_BYTES")
        } else { self }
    }
}

/// Value maps use serde_json's default sorted map, without preserve_order.
pub fn canonical_json(value: &Value) -> Vec<u8> {
    let mut bytes = serde_json::to_vec(value).expect("Value serialization cannot fail");
    bytes.push(b'\n');
    bytes
}
fn tree(value: &Tree) -> Value { match value {
    Tree::Leaf(i) => json!(i), Tree::Node(a, b) => json!([tree(a), tree(b)]),
} }
fn place(value: Location) -> Value { match value {
    Location::Node(i) => json!(["V", i]), Location::Edge(i) => json!(["E", i]),
    Location::Ancestral(i) => json!(["A", i]),
} }
fn snapshot(value: &Snapshot) -> Value {
    json!({"live":value.live, "ancestor":value.ancestor,
        "genealogy":value.genealogy.iter().map(|t| t.as_ref().map(tree)).collect::<Vec<_>>(),
        "location":value.population.iter().map(|p| p.map(place)).collect::<Vec<_>>(),
        "register":value.register})
}
fn view(value: &SelectedView) -> Value {
    json!({"genealogy":value.genealogy.iter().map(|t| t.as_ref().map(tree)).collect::<Vec<_>>(),
        "location":value.population.iter().map(|p| p.map(place)).collect::<Vec<_>>(),
        "register":value.register})
}
fn polynomial(value: &Polynomial) -> Value {
    json!(value.terms.iter().map(|(powers, coefficient)| json!([powers, canonical(coefficient)]))
        .collect::<Vec<_>>())
}
fn variable(value: word::Variable) -> Value { match value {
    word::Variable::Survival { slot, population: Location::Edge(e) } => json!(["X",slot,"E",e]),
    word::Variable::Survival { slot, population: Location::Ancestral(r) } => json!(["X",slot,"A",r]),
    word::Variable::OriginalGamma(h) => json!(["ORIGINAL_GAMMA",h]),
    word::Variable::Survival { population: Location::Node(_), .. } =>
        panic!("SOURCE_CALENDAR_NODE_VARIABLE"),
} }
fn variables(request: &word::Request) -> Vec<Value> {
    (0..request.slots).flat_map(|slot| {
        (0..request.context.source.edges.len()).map(move |edge|
            variable(word::Variable::Survival { slot, population: Location::Edge(edge) }))
            .chain(std::iter::once(variable(word::Variable::Survival {
                slot, population: Location::Ancestral(request.context.source.root) })))
    }).chain((0..request.context.source.hybrids.len()).map(|hybrid|
        variable(word::Variable::OriginalGamma(hybrid)))).collect()
}
fn symbol(value: word::Symbol) -> Value { match value {
    word::Symbol::Interval(i) => json!(["INTERVAL",i]), word::Symbol::Exit(i) => json!(["EXIT",i]),
    word::Symbol::Enter(i) => json!(["ENTER",i]),
} }
fn word_request(value: &word::Request) -> Value {
    let c = &value.context;
    let initial = match &value.initial {
        word::Initial::Natural => json!({"kind":"NATURAL"}),
        word::Initial::Conditional(s) => json!({"kind":"CONDITIONAL","snapshot":snapshot(s)}),
    };
    let w = &value.limits;
    json!({"context":{"vertices":c.source.vertices,"root":c.source.root,
        "edges":c.source.edges.iter().map(|e| [e.source,e.target]).collect::<Vec<_>>(),
        "leaves":c.source.leaves,
        "hybrids":c.source.hybrids.iter().map(|h| [h.vertex,h.incoming[0],h.incoming[1]]).collect::<Vec<_>>(),
        "local_samples":c.sample,"global_labels":c.global_labels},
        "initial":initial,"common":value.common,"slots":value.slots,
        "word":value.word.iter().copied().map(symbol).collect::<Vec<_>>(),
        "terminal":match value.terminal { word::Terminal::FullView=>"FULL_VIEW",
            word::Terminal::AncestralComplete=>"ANCESTRAL_COMPLETE" },
        "limits":{"initial_assignments":w.initial_assignments,"initial_terms":w.initial_terms,
            "queries":w.queries,"branches":w.branches,"term_products":w.term_products,
            "destinations":w.destinations,"terms":w.terms}})
}
fn requirements(value: calendar::Requirements) -> Value {
    json!({"word_length":value.word_length,"slots":value.slots,"variables":value.variables})
}
fn agenda(value: &calendar::Agenda) -> Value {
    json!({"dates":value.dates.iter().map(canonical).collect::<Vec<_>>(),
        "cohorts":value.cohorts.iter().map(|c| json!({"date_index":c.date_index,
            "representative":c.representative,"vertices":c.vertices,"exits":c.exits})).collect::<Vec<_>>(),
        "word":value.word.iter().copied().map(symbol).collect::<Vec<_>>(),
        "origins":value.origins.iter().map(|o| json!({"date_index":o.date_index,"phase":match o.phase {
            calendar::Phase::Exit=>"EXIT",calendar::Phase::Enter=>"ENTER",calendar::Phase::Interval=>"INTERVAL"},
            "index":o.index})).collect::<Vec<_>>(),
        "slots":value.slots.iter().map(|s| json!({"slot":s.slot,"word_position":s.word_position,
            "younger_date":canonical(&s.younger_date),"older_date":canonical(&s.older_date),
            "duration":canonical(&s.duration)})).collect::<Vec<_>>(),
        "physical_coordinates":value.physical_coordinates.iter().map(|c| json!({"variable":variable(c.variable),
            "kind":match c.kind { calendar::CoordinateKind::ExpNeg=>"EXP_NEG",calendar::CoordinateKind::Rational=>"RATIONAL" },
            "argument":canonical(&c.argument)})).collect::<Vec<_>>(),
        "leaf_age_zero":value.leaf_age_zero})
}
fn limit_kind(value: word::LimitKind) -> String { match value {
    word::LimitKind::InitialAssignments=>"initial_assignments".into(),
    word::LimitKind::InitialTerms=>"initial_terms".into(),word::LimitKind::Queries=>"queries".into(),
    word::LimitKind::Branches=>"branches".into(),word::LimitKind::TermProducts=>"term_products".into(),
    word::LimitKind::Destinations=>"destinations".into(),word::LimitKind::Terms=>"terms".into(),
    word::LimitKind::Epoch(k)=>format!("EPOCH:{k:?}"),
    word::LimitKind::Boundary(k)=>format!("BOUNDARY:{k:?}"),
    word::LimitKind::Completion(k)=>format!("COMPLETION:{k:?}"),
} }
fn child_prefix(request: &word::Request) -> Value {
    json!({"schema":"source_word_result_v1","request":word_request(request),
        "variables":variables(request),"source_admission_verified":false})
}
fn child_table(request: &word::Request, table: &word::Table) -> Value {
    let mut child = child_prefix(request);
    let vars = table.variables.iter().copied().map(variable).collect::<Vec<_>>();
    assert_eq!(vars, variables(request), "SOURCE_CALENDAR_BANK");
    child["status"] = json!("TABLE");
    child["rows"] = json!(table.transitions.iter().map(|r| json!({"view":view(&r.view),
        "witness":snapshot(&r.witness),"coefficients":polynomial(&r.polynomial)})).collect::<Vec<_>>());
    let w = &table.work;
    child["work"] = json!({"initial_assignments":w.initial_assignments,
        "initial_term_contributions":w.initial_term_contributions,"queries":w.queries,
        "branches":w.branches,"term_products":w.term_products,"largest_row":w.largest_row,
        "largest_terms":w.largest_terms});
    child
}
fn child_unknown(request: &word::Request, limit: &word::Limit) -> Value {
    let mut child = child_prefix(request);
    child["status"] = json!("UNKNOWN");
    let stage = match limit.stage { word::Stage::Initialization=>json!("INITIAL"),
        word::Stage::Letter(i)=>json!(i),word::Stage::Completion=>json!("COMPLETION") };
    child["limit"] = json!({"stage":stage,"kind":limit_kind(limit.kind),
        "required":limit.required,"cap":limit.cap});
    child
}

pub fn decision(input: &RequestDto, result: calendar::Decision) -> Frame {
    let mut value = json!({"schema":SCHEMA,"request":input,"source_admission_verified":false});
    let exit_code = match result {
        calendar::Decision::Table { generated, table } => {
            value["status"] = json!("TABLE");
            value["requirements"] = requirements(generated.requirements);
            value["agenda"] = agenda(&generated.agenda);
            value["word_result"] = child_table(&generated.child,&table);
            0
        },
        calendar::Decision::WordUnknown { generated, limit } => {
            value["status"] = json!("UNKNOWN");
            value["requirements"] = requirements(generated.requirements);
            value["agenda"] = agenda(&generated.agenda);
            value["word_result"] = child_unknown(&generated.child,&limit);
            value["unknown_scope"] = json!("WORD");
            value["consumer_population"] = limit.population.map(place).unwrap_or(Value::Null);
            2
        },
        calendar::Decision::CompilerUnknown(unknown) => {
            value["status"] = json!("UNKNOWN");
            value["requirements"] = requirements(unknown.requirements);
            value["unknown_scope"] = json!("COMPILER");
            value["limit"] = json!({"stage":"COMPILER","kind":match unknown.limit.kind {
                calendar::CompilerLimitKind::WordLength=>"word_length",
                calendar::CompilerLimitKind::Slots=>"slots",
                calendar::CompilerLimitKind::Variables=>"variables" },
                "required":unknown.limit.required,"cap":unknown.limit.cap});
            2
        },
    };
    Frame { value, exit_code, diagnostic: None }.bounded()
}
