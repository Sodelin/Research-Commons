//! Frozen input-only supplied calendars. Expected tables are never embedded.
//! Contract7e2202ae and input inventoryb9bd9a83; private scope only.
use parity_solver::{canonical, Rational, forest::Tree, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial,
    source_calendar as calendar, source_epoch::{self as epoch, SelectedView},
    source_population::{self as population, Context, Location, Snapshot}, source_boundary as boundary,
    source_word::{self as word, Initial, LimitKind, Limits, ProviderLimits, Request, Stage, Symbol, Terminal, Variable}};

fn rat(raw: &str) -> Rational {
    let (a,b)=raw.split_once('/').expect("frozen canonical rational");
    Rational::new(a.parse().expect("integer"),b.parse().expect("positive denominator"))
}
fn list<T>(items: impl IntoIterator<Item=T>, render: impl Fn(T)->String) -> String {
    format!("[{}]", items.into_iter().map(render).collect::<Vec<_>>().join(","))
}
fn tree(t: &Tree) -> String { match t {
    Tree::Leaf(i) => i.to_string(), Tree::Node(a,b) => format!("[{},{}]",tree(a),tree(b)),
} }
fn place(p: Location) -> String { match p {
    Location::Node(i) => format!("[\"V\",{i}]"), Location::Edge(i) => format!("[\"E\",{i}]"),
    Location::Ancestral(i) => format!("[\"A\",{i}]"),
} }
fn snapshot(s: &Snapshot) -> String {
    format!("{{\"live\":{},\"ancestor\":{},\"genealogy\":{},\"location\":{},\"register\":{}}}",
        list(s.live.iter(), |i| i.to_string()), list(s.ancestor.iter(), |i| i.to_string()),
        list(s.genealogy.iter(), |t| t.as_ref().map(tree).unwrap_or_else(|| "null".into())),
        list(s.population.iter(), |p| p.map(place).unwrap_or_else(|| "null".into())),
        list(s.register.iter(), |bit| bit.to_string()))
}
fn view(v: &SelectedView) -> String {
    format!("{{\"genealogy\":{},\"location\":{},\"register\":{}}}",
        list(v.genealogy.iter(), |t| tree(t.as_ref().expect("full-copy tree"))),
        list(v.population.iter(), |p| place(p.expect("full-copy location"))),
        list(v.register.iter(), |bit| bit.to_string()))
}
fn polynomial(p: &Polynomial) -> String {
    list(p.terms.iter(), |(powers,c)| format!("[{},\"{}\"]",list(powers.iter(),|i|i.to_string()),canonical(c)))
}
fn variable(v: Variable) -> String { match v {
    Variable::Survival{slot,population:Location::Edge(edge)} => format!("[\"X\",{slot},\"E\",{edge}]"),
    Variable::Survival{slot,population:Location::Ancestral(root)} => format!("[\"X\",{slot},\"A\",{root}]"),
    Variable::OriginalGamma(hybrid) => format!("[\"ORIGINAL_GAMMA\",{hybrid}]"),
    _ => panic!("word bank contains a node"),
} }
fn variables(r: &Request) -> Vec<Variable> {
    (0..r.slots).flat_map(|slot| (0..r.context.source.edges.len()).map(move |edge|
        Variable::Survival{slot,population:Location::Edge(edge)})
        .chain(std::iter::once(Variable::Survival{slot,population:Location::Ancestral(r.context.source.root)})))
        .chain((0..r.context.source.hybrids.len()).map(Variable::OriginalGamma)).collect()
}
fn symbol(s: Symbol) -> String { match s {
    Symbol::Interval(i) => format!("[\"INTERVAL\",{i}]"), Symbol::Exit(i) => format!("[\"EXIT\",{i}]"),
    Symbol::Enter(i) => format!("[\"ENTER\",{i}]"),
} }
fn word_request(r: &Request) -> String {
    let initial = match &r.initial {
        Initial::Natural => "{\"kind\":\"NATURAL\"}".into(),
        Initial::Conditional(s) => format!("{{\"kind\":\"CONDITIONAL\",\"snapshot\":{}}}",snapshot(s)),
    };
    let c=&r.context;
    let terminal=if r.terminal==Terminal::FullView {"FULL_VIEW"} else {"ANCESTRAL_COMPLETE"};
    format!("{{\"context\":{{\"vertices\":{},\"root\":{},\"edges\":{},\"leaves\":{},\"hybrids\":{},\"local_samples\":{},\"global_labels\":{}}},\"initial\":{},\"common\":{},\"slots\":{},\"word\":{},\"terminal\":\"{terminal}\",\"limits\":{{\"initial_assignments\":{},\"initial_terms\":{},\"queries\":{},\"branches\":{},\"term_products\":{},\"destinations\":{},\"terms\":{}}}}}",
        c.source.vertices,c.source.root,list(c.source.edges.iter(),|e|format!("[{},{}]",e.source,e.target)),
        list(c.source.leaves.iter(),|i|i.to_string()),list(c.source.hybrids.iter(),|h|format!("[{},{},{}]",h.vertex,h.incoming[0],h.incoming[1])),
        list(c.sample.iter(),|i|i.to_string()),list(c.global_labels.iter(),|i|i.to_string()),initial,
        list(r.common.iter(),|b|b.to_string()),r.slots,list(r.word.iter(),|s|symbol(*s)),
        r.limits.initial_assignments,r.limits.initial_terms,r.limits.queries,r.limits.branches,r.limits.term_products,r.limits.destinations,r.limits.terms)
}

fn word_limits(w: Limits) -> String {
    format!("{{\"initial_assignments\":{},\"initial_terms\":{},\"queries\":{},\"branches\":{},\"term_products\":{},\"destinations\":{},\"terms\":{}}}",
        w.initial_assignments,w.initial_terms,w.queries,w.branches,w.term_products,w.destinations,w.terms)
}
fn provider_limits(p: ProviderLimits) -> String {
    format!("{{\"epoch\":{{\"calls\":{},\"destinations\":{},\"lifted_terms\":{},\"branches\":{},\"term_products\":{}}},\"boundary\":{{\"assignments\":{},\"destinations\":{},\"term_contributions\":{}}},\"completion\":{{\"calls\":{},\"destinations\":{},\"lifted_terms\":{}}}}}",
        p.epoch.calls,p.epoch.destinations,p.epoch.lifted_terms,p.epoch.branches,p.epoch.term_products,
        p.boundary.assignments,p.boundary.destinations,p.boundary.term_contributions,
        p.completion.calls,p.completion.destinations,p.completion.lifted_terms)
}
fn calendar_request(r: &calendar::Request) -> String {
    let c=&r.context;
    let terminal=if r.terminal==Terminal::FullView {"FULL_VIEW"} else {"ANCESTRAL_COMPLETE"};
    format!("{{\"context\":{{\"vertices\":{},\"root\":{},\"edges\":{},\"leaves\":{},\"hybrids\":{},\"local_samples\":{},\"global_labels\":{}}},\"ages\":{},\"inverse_rates\":{},\"original_gamma\":{},\"common\":{},\"terminal\":\"{terminal}\",\"compiler_limits\":{{\"word_length\":{},\"slots\":{},\"variables\":{}}},\"word_limits\":{},\"provider_limits\":{}}}",
        c.source.vertices,c.source.root,list(c.source.edges.iter(),|e|format!("[{},{}]",e.source,e.target)),
        list(c.source.leaves.iter(),|i|i.to_string()),list(c.source.hybrids.iter(),|h|format!("[{},{},{}]",h.vertex,h.incoming[0],h.incoming[1])),
        list(c.sample.iter(),|i|i.to_string()),list(c.global_labels.iter(),|i|i.to_string()),
        list(r.ages.iter(),|v|format!("\"{}\"",canonical(v))),list(r.inverse_rates.iter(),|v|format!("\"{}\"",canonical(v))),
        list(r.original_gamma.iter(),|v|format!("\"{}\"",canonical(v))),list(r.common.iter(),|v|v.to_string()),
        r.compiler_limits.word_length,r.compiler_limits.slots,r.compiler_limits.variables,
        word_limits(r.word_limits),provider_limits(r.provider_limits))
}
fn requirements(r: calendar::Requirements) -> String {
    format!("{{\"word_length\":{},\"slots\":{},\"variables\":{}}}",r.word_length,r.slots,r.variables)
}
fn agenda(a: &calendar::Agenda) -> String {
    let phase=|phase|match phase {calendar::Phase::Exit=>"EXIT",calendar::Phase::Enter=>"ENTER",calendar::Phase::Interval=>"INTERVAL"};
    format!("{{\"dates\":{},\"cohorts\":{},\"word\":{},\"origins\":{},\"slots\":{},\"physical_coordinates\":{},\"leaf_age_zero\":{}}}",
        list(a.dates.iter(),|v|format!("\"{}\"",canonical(v))),
        list(a.cohorts.iter(),|c|format!("{{\"date_index\":{},\"representative\":{},\"vertices\":{},\"exits\":{}}}",
            c.date_index,c.representative,list(c.vertices.iter(),|i|i.to_string()),list(c.exits.iter(),|i|i.to_string()))),
        list(a.word.iter(),|s|symbol(*s)),
        list(a.origins.iter(),|o|format!("{{\"date_index\":{},\"phase\":\"{}\",\"index\":{}}}",o.date_index,phase(o.phase),o.index)),
        list(a.slots.iter(),|s|format!("{{\"slot\":{},\"word_position\":{},\"younger_date\":\"{}\",\"older_date\":\"{}\",\"duration\":\"{}\"}}",
            s.slot,s.word_position,canonical(&s.younger_date),canonical(&s.older_date),canonical(&s.duration))),
        list(a.physical_coordinates.iter(),|c|format!("{{\"variable\":{},\"kind\":\"{}\",\"argument\":\"{}\"}}",
            variable(c.variable),match c.kind {calendar::CoordinateKind::ExpNeg=>"EXP_NEG",calendar::CoordinateKind::Rational=>"RATIONAL"},canonical(&c.argument))),
        a.leaf_age_zero)
}
fn limit_kind(kind: LimitKind) -> String { match kind {
    LimitKind::InitialAssignments=>"initial_assignments".into(),LimitKind::InitialTerms=>"initial_terms".into(),
    LimitKind::Queries=>"queries".into(),LimitKind::Branches=>"branches".into(),
    LimitKind::TermProducts=>"term_products".into(),LimitKind::Destinations=>"destinations".into(),LimitKind::Terms=>"terms".into(),
    LimitKind::Epoch(k)=>format!("EPOCH:{k:?}"),LimitKind::Boundary(k)=>format!("BOUNDARY:{k:?}"),LimitKind::Completion(k)=>format!("COMPLETION:{k:?}"),
} }
fn child_prefix(name: &str, r: &Request) -> String {
    format!("\"schema\":\"source_word_probe_v1\",\"fixture\":\"{name}\",\"request\":{},\"variables\":{},\"source_admission_verified\":false",
        word_request(r),list(variables(r).iter(),|v|variable(*v)))
}
fn child_table(name: &str, g: &calendar::Generated, t: &word::Table) -> String {
    assert_eq!(t.variables,variables(&g.child));
    let rows=list(t.transitions.iter(),|r|format!("{{\"view\":{},\"witness\":{},\"coefficients\":{}}}",view(&r.view),snapshot(&r.witness),polynomial(&r.polynomial)));
    let w=&t.work;
    format!("{{{},\"status\":\"TABLE\",\"rows\":{rows},\"work\":{{\"initial_assignments\":{},\"initial_term_contributions\":{},\"queries\":{},\"branches\":{},\"term_products\":{},\"largest_row\":{},\"largest_terms\":{}}}}}",
        child_prefix(name,&g.child),w.initial_assignments,w.initial_term_contributions,w.queries,w.branches,w.term_products,w.largest_row,w.largest_terms)
}
fn child_unknown(name: &str, g: &calendar::Generated, l: &word::Limit) -> String {
    let stage=match l.stage {Stage::Initialization=>"\"INITIAL\"".into(),Stage::Letter(i)=>i.to_string(),Stage::Completion=>"\"COMPLETION\"".into()};
    format!("{{{},\"status\":\"UNKNOWN\",\"limit\":{{\"stage\":{stage},\"kind\":\"{}\",\"required\":{},\"cap\":{}}}}}",
        child_prefix(name,&g.child),limit_kind(l.kind),l.required,l.cap)
}
fn fixture(name: &str) -> Option<calendar::Request> {
    match name {
        // Frozen request only: aboveHardcapRejected.request.json; SHA256 ca71fee2ea42eb74a9493c658769f190d0cfb5b6c8d39e9343a16507d5b43169.
        "aboveHardcapRejected" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 33, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: boundaryAssignmentLimit.request.json; SHA256 11c1c547919e204b6e5a92685377c8447ce71970479ac8af348fdb41cdd25048.
        "boundaryAssignmentLimit" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![1], global_labels: vec![0] },
            ages: vec![rat("1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 0, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: compilerLimit_slots.request.json; SHA256 7db0d37c4f09cf21ed24502a1f05a607d53e7a78119487409767ccce29f3bb07.
        "compilerLimit_slots" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 0, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: compilerLimit_variables.request.json; SHA256 758f868b0aa56ba0f44ff5722d38ae1e1f112ea1eb789a28c3db8b3d35dfe002.
        "compilerLimit_variables" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 2 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: compilerLimit_word_length.request.json; SHA256 0de6cec15fc1a64607f170623f54088cbbf67a62bafec1080b621f1de5104019.
        "compilerLimit_word_length" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 5, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: compilerPriority.request.json; SHA256 7a3db1bb042d713748a70f79daf7aa070d4dc4ef1aab50c957d6f976addc3a22.
        "compilerPriority" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 0, slots: 0, variables: 0 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: completionCallLimit.request.json; SHA256 09aedfd7eabb0eb2fe23ba7464e314994d02543418eb9d9233501777745ea68f.
        "completionCallLimit" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![1], global_labels: vec![0] },
            ages: vec![rat("1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 0, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: emptyCompletionRejected.request.json; SHA256 996b29a6f7867f820b954ee5cc49e46c1689f68520bff4dd640ccccea6e06039.
        "emptyCompletionRejected" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![], global_labels: vec![] },
            ages: vec![rat("1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 0, slots: 0, variables: 0 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: emptyNaturalCalendar.request.json; SHA256 bfde4e578ade6c193050389aa655cb2f10976fc86c2857f6e4660886b7d1e671.
        "emptyNaturalCalendar" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![], global_labels: vec![] },
            ages: vec![rat("3/1"), rat("0/1"), rat("2/1"), rat("1/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![rat("1/3")], common: vec![true],
            terminal: Terminal::FullView,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: epochCallLimit.request.json; SHA256 b7e630bb1c28f15a9a350482d2fd07b12ad9b915aa337e15e30f09bc537c7604.
        "epochCallLimit" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![1], global_labels: vec![0] },
            ages: vec![rat("1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 0, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: equalEdgeAgeRejected.request.json; SHA256 9e67a86c63c882099c35f17844677e5535174f33bbdf97b7aaa596a4f19e5512.
        "equalEdgeAgeRejected" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("0/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: gammaOneRejected.request.json; SHA256 9870104a0f5b0eb8776c3dd4351212e59a6c03ed029872876897328d30b4eb52.
        "gammaOneRejected" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![0, 1, 1], global_labels: vec![0, 1, 2] },
            ages: vec![rat("3/1"), rat("0/1"), rat("2/1"), rat("1/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2"), rat("5/2"), rat("7/3"), rat("2/3")],
            original_gamma: vec![rat("1/1")], common: vec![true],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: gammaZeroRejected.request.json; SHA256 78c50a4379ff69cacca40772309361d129d67f688e4c64837f20ed0aa4254585.
        "gammaZeroRejected" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![0, 1, 1], global_labels: vec![0, 1, 2] },
            ages: vec![rat("3/1"), rat("0/1"), rat("2/1"), rat("1/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2"), rat("5/2"), rat("7/3"), rat("2/3")],
            original_gamma: vec![rat("0/1")], common: vec![true],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: incomparableOrderLeft.request.json; SHA256 ee0cf441d57394dc699e6ea0a55ab5a939e1bfcebd5fbe1b23bdae083d3f4181.
        "incomparableOrderLeft" => Some(calendar::Request { context: Context { source: Source { vertices: 7, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 1, target: 3 }, Edge { source: 1, target: 4 }, Edge { source: 2, target: 5 }, Edge { source: 2, target: 6 }],
            leaves: vec![3, 4, 5, 6], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![0, 1, 2] },
            ages: vec![rat("4/1"), rat("1/1"), rat("2/1"), rat("0/1"), rat("0/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: incomparableOrderRight.request.json; SHA256 6ce7b5b7275d0e0c6aca4e0ea139145f57bc3aff16af8354148a72e673e509a8.
        "incomparableOrderRight" => Some(calendar::Request { context: Context { source: Source { vertices: 7, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 1, target: 3 }, Edge { source: 1, target: 4 }, Edge { source: 2, target: 5 }, Edge { source: 2, target: 6 }],
            leaves: vec![3, 4, 5, 6], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![0, 1, 2] },
            ages: vec![rat("4/1"), rat("2/1"), rat("1/1"), rat("0/1"), rat("0/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: largeExactExposure.request.json; SHA256 2cfd4dabf1a1d164025e973c0db7422a21e188890f87193ca579b96343802b43.
        "largeExactExposure" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397377/11"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("13/17"), rat("19/23"), rat("29/31")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: negativeInverseRejected.request.json; SHA256 4ab85724a65602a0de4c4ca487c274974cc6c4e3946ca590fe94b723ccf92e68.
        "negativeInverseRejected" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("-1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: ordinaryThreeCalendar.request.json; SHA256 51d2150c2b9d8f601303c2c9f486e8f0ae2adce61f50fd1886b7188909a1685a.
        "ordinaryThreeCalendar" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 4 }],
            leaves: vec![1, 3, 4], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![0, 1, 2] },
            ages: vec![rat("3/1"), rat("0/1"), rat("1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2"), rat("5/2"), rat("3/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: ordinaryThreeRetimed.request.json; SHA256 8c3798a77a2bf0ee313930ca13a95a376a4beda7e5aa6540c86238bf28473d36.
        "ordinaryThreeRetimed" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 4 }],
            leaves: vec![1, 3, 4], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![0, 1, 2] },
            ages: vec![rat("7/1"), rat("0/1"), rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2"), rat("5/2"), rat("3/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: parallelCommonCalendar.request.json; SHA256 f4c9784938ede6f83c294b037018dac38392e80b91d33d2544b5c9660f334076.
        "parallelCommonCalendar" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![0, 1, 1], global_labels: vec![0, 1, 2] },
            ages: vec![rat("3/1"), rat("0/1"), rat("2/1"), rat("1/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2"), rat("5/2"), rat("7/3"), rat("2/3")],
            original_gamma: vec![rat("1/3")], common: vec![true],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: parallelIndependentCalendar.request.json; SHA256 108456e9a7670f704877c715f8bcdc693a66295c68dd3e1dfbb0aad8e97fd3c8.
        "parallelIndependentCalendar" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![0, 1, 1], global_labels: vec![0, 1, 2] },
            ages: vec![rat("3/1"), rat("0/1"), rat("2/1"), rat("1/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2"), rat("5/2"), rat("7/3"), rat("2/3")],
            original_gamma: vec![rat("1/3")], common: vec![false],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: permutedLabelsCalendar.request.json; SHA256 846f2a5c2369c576d0417b2a8d4308f806baba74c37ef60938f251ad38b4f2d7.
        "permutedLabelsCalendar" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 4 }],
            leaves: vec![1, 3, 4], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![3, 0, 2] },
            ages: vec![rat("3/1"), rat("0/1"), rat("1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: reversedEdgeAgeRejected.request.json; SHA256 8a06b5a6cd19020cec9a6df932950d133865fee14cf705c0a2d90005c55e6e84.
        "reversedEdgeAgeRejected" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("-1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: reversedParallelParents.request.json; SHA256 a98b153d466b296607a3317f2d4d728ed2904b475f461e963cbe3a6f8e444bdc.
        "reversedParallelParents" => Some(calendar::Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [3, 2] }] },
            sample: vec![0, 1, 1], global_labels: vec![0, 1, 2] },
            ages: vec![rat("3/1"), rat("0/1"), rat("2/1"), rat("1/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2"), rat("5/2"), rat("7/3"), rat("2/3")],
            original_gamma: vec![rat("1/3")], common: vec![true],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: serialNegativeTips.request.json; SHA256 435c41549a96c529ce7545480d2f52bef9e2280ce01b64523e5f0a62944a11db.
        "serialNegativeTips" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 0, 1], global_labels: vec![0, 1, 2] },
            ages: vec![rat("3/2"), rat("-3/2"), rat("1/4")], inverse_rates: vec![rat("7/3"), rat("11/5"), rat("2/3")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: singletonCalendar.request.json; SHA256 eb88dcb72944aba127c03b0948a7c551b426f045ec99ba2df3a68ff31c7a3c70.
        "singletonCalendar" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![1], global_labels: vec![0] },
            ages: vec![rat("1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: tiedInternalCohort.request.json; SHA256 c534e8395ea268f836d39836c22c23f29642b03948378b4f171823b5590964e7.
        "tiedInternalCohort" => Some(calendar::Request { context: Context { source: Source { vertices: 7, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 1, target: 3 }, Edge { source: 1, target: 4 }, Edge { source: 2, target: 5 }, Edge { source: 2, target: 6 }],
            leaves: vec![3, 4, 5, 6], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![0, 1, 2] },
            ages: vec![rat("3/1"), rat("1/1"), rat("1/1"), rat("0/1"), rat("0/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: twoTipCalendar.request.json; SHA256 42eb6a95c160825cb19da7945bd025cb2e31e8a2d43aaab4fe1c87a0d4c64dbf.
        "twoTipCalendar" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: validFortyThreeLetters.request.json; SHA256 f8c0e605e7d3b49506f23cc314aa8809db6b0c725fb4c807d9d5097d5be8be80.
        "validFortyThreeLetters" => Some(calendar::Request { context: Context { source: Source { vertices: 15, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 1, target: 3 }, Edge { source: 1, target: 4 }, Edge { source: 2, target: 5 }, Edge { source: 2, target: 6 }, Edge { source: 3, target: 7 }, Edge { source: 3, target: 8 }, Edge { source: 4, target: 9 }, Edge { source: 4, target: 10 }, Edge { source: 5, target: 11 }, Edge { source: 5, target: 12 }, Edge { source: 6, target: 13 }, Edge { source: 6, target: 14 }],
            leaves: vec![7, 8, 9, 10, 11, 12, 13, 14], hybrids: vec![] },
            sample: vec![0], global_labels: vec![0] },
            ages: vec![rat("20/1"), rat("19/1"), rat("18/1"), rat("17/1"), rat("16/1"), rat("15/1"), rat("14/1"), rat("13/1"), rat("12/1"), rat("11/1"), rat("10/1"), rat("9/1"), rat("8/1"), rat("7/1"), rat("6/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: wordQueryBeforeProviderLimit.request.json; SHA256 9678cf8546a011606746168147a7b76877f71441de692068c72968cb6ca012c1.
        "wordQueryBeforeProviderLimit" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![1], global_labels: vec![0] },
            ages: vec![rat("1/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("1/1"), rat("1/1")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 0, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 0, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: wordQueryLimit.request.json; SHA256 fde57004bafc5c875535740d05b7b4e6bb3a7b4d3b2c89161ffcfa7e5fb3a07b.
        "wordQueryLimit" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("1/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 32, slots: 16, variables: 256 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 0, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        // Frozen request only: zeroInverseRejected.request.json; SHA256 4c98c6d3209141171baa69b1a4126f2336be425eef76decf40c8558f7f301e63.
        "zeroInverseRejected" => Some(calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            ages: vec![rat("2/1"), rat("0/1"), rat("0/1")], inverse_rates: vec![rat("0/1"), rat("2/1"), rat("3/2")],
            original_gamma: vec![], common: vec![],
            terminal: Terminal::AncestralComplete,
            compiler_limits: calendar::CompilerLimits { word_length: 0, slots: 0, variables: 0 },
            word_limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits {
                epoch: epoch::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536, branches: 4096, term_products: 65536 }, boundary: boundary::Limits { assignments: 16, destinations: 16, term_contributions: 128 },
                completion: population::Limits { calls: 4096, destinations: 4096, lifted_terms: 65536 } } }),
        _ => None,
    }
}

fn main() {
    let args=std::env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() || !(args.len()==1 || args.len()==4 && (args[1]=="--limit" || args[1]=="--compiler-limit")) {std::process::exit(2);}
    let Some(mut input)=fixture(&args[0]) else {std::process::exit(2);};
    if args.len()==4 {
        let Ok(cap)=args[3].parse::<usize>() else {std::process::exit(2);};
        if args[1]=="--compiler-limit" {
            match args[2].as_str() {"word_length"=>input.compiler_limits.word_length=cap,
                "slots"=>input.compiler_limits.slots=cap,"variables"=>input.compiler_limits.variables=cap,_=>std::process::exit(2)}
        } else {
            match args[2].as_str() {"initial_assignments"=>input.word_limits.initial_assignments=cap,
                "initial_terms"=>input.word_limits.initial_terms=cap,"queries"=>input.word_limits.queries=cap,
                "branches"=>input.word_limits.branches=cap,"term_products"=>input.word_limits.term_products=cap,
                "destinations"=>input.word_limits.destinations=cap,"terms"=>input.word_limits.terms=cap,_=>std::process::exit(2)}
        }
    }
    let prefix=format!("\"schema\":\"source_calendar_probe_v1\",\"fixture\":\"{}\",\"request\":{},\"source_admission_verified\":false",
        args[0],calendar_request(&input));
    match calendar::calendar_row(&input) {
        Ok(calendar::Decision::Table {generated,table})=>println!("{{{prefix},\"requirements\":{},\"status\":\"TABLE\",\"agenda\":{},\"word_result\":{}}}",
            requirements(generated.requirements),agenda(&generated.agenda),child_table(&args[0],&generated,&table)),
        Ok(calendar::Decision::WordUnknown {generated,limit})=>println!("{{{prefix},\"requirements\":{},\"status\":\"UNKNOWN\",\"agenda\":{},\"word_result\":{},\"unknown_scope\":\"WORD\",\"consumer_population\":{}}}",
            requirements(generated.requirements),agenda(&generated.agenda),child_unknown(&args[0],&generated,&limit),
            limit.population.map(place).unwrap_or_else(||"null".into())),
        Ok(calendar::Decision::CompilerUnknown(unknown))=>println!("{{{prefix},\"requirements\":{},\"status\":\"UNKNOWN\",\"unknown_scope\":\"COMPILER\",\"limit\":{{\"stage\":\"COMPILER\",\"kind\":\"{}\",\"required\":{},\"cap\":{}}}}}",
            requirements(unknown.requirements),match unknown.limit.kind {calendar::CompilerLimitKind::WordLength=>"word_length",calendar::CompilerLimitKind::Slots=>"slots",calendar::CompilerLimitKind::Variables=>"variables"},
            unknown.limit.required,unknown.limit.cap),
        Err(error)=>{eprintln!("{error:?}");std::process::exit(1);}
    }
}
