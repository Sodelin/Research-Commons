//! Frozen supplied-word requests; expected rows are computed independently.
//! This private fixture probe adds no endpoint or source-admission claim.
use parity_solver::{canonical, forest::Tree, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial,
    source_epoch::SelectedView, source_population::{Location, Snapshot},
    source_word::{self as word, Decision, Error, Initial, LimitKind, Limits, ProviderLimits,
        Request, Stage, Symbol, Terminal, Variable}};
use parity_solver::source_population::Context;

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
fn request(r: &Request) -> String {
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
fn fixture(name: &str) -> Option<Request> {
    match name {
        "parallelCommonFinite" => fixture("parallelCommonCalendar").map(|mut request| {
            request.terminal = Terminal::FullView;
            request
        }),
        "parallelIndependentFinite" => fixture("parallelIndependentCalendar").map(|mut request| {
            request.terminal = Terminal::FullView;
            request
        }),
        // Frozen input request only, SHA256 467656dedebf99bfedd591991164f0114f1108b380cc23738829aedfd729ed49.
        "completion1" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![1], global_labels: vec![0] },
            initial: Initial::Conditional(Snapshot { live: vec![0], ancestor: vec![0],
                genealogy: vec![Some(Tree::Leaf(0))],
                population: vec![Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 f49c9065a8818709682c3ad06ba1627d4240b8b74885ca6907943e6ea7e16b89.
        "completion2" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 1], global_labels: vec![0, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 1cee5b5da1e747ecd1f2a1d719092f68d7ffea91c7b72a1ac594b82a28ddff2b.
        "completion3" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 0, 1], global_labels: vec![0, 1, 2] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1, 2], ancestor: vec![0, 1, 2],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1)), Some(Tree::Leaf(2))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 659d15e6b9ce4aef5ce4f66013eb91235c45332edcb8390ec5739832f391bd21.
        "completion4" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 0, 0, 1], global_labels: vec![0, 1, 2, 3] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1, 2, 3], ancestor: vec![0, 1, 2, 3],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1)), Some(Tree::Leaf(2)), Some(Tree::Leaf(3))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0)), Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 1af9bf6b8b00defc1635c48c1acb12ec1f76b234b1a5fc987f8c5291749517da.
        "completionCarriedNonminimum" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 0, 0, 1], global_labels: vec![0, 1, 2, 3] },
            initial: Initial::Conditional(Snapshot { live: vec![2, 3], ancestor: vec![2, 2, 2, 3],
                genealogy: vec![None, None, Some(Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)))), Box::new(Tree::Leaf(2)))), Some(Tree::Leaf(3))],
                population: vec![None, None, Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 b54fcfc3cbde8b08297e25fb915a6b7a63387f377267b36e79e775fa7b2c0e2f.
        "completionEmptyRejected" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![], global_labels: vec![] },
            initial: Initial::Conditional(Snapshot { live: vec![], ancestor: vec![],
                genealogy: vec![],
                population: vec![], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 02869356ad14044691ed0a362b6efedfd470c660c20e0beadaddcedc2816e499.
        "completionLimit_branches" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 1], global_labels: vec![0, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 1, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 188b45b6d206307a71ab75318f5cf8bd2a95617f6de63e8be259644023a623cb.
        "completionLimit_destinations" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 1], global_labels: vec![0, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 1, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 0e01f34fb6eee4c29c8ab63b49a8cb0a73eb83f5fb8308bb06cc1d38520835a7.
        "completionLimit_queries" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 1], global_labels: vec![0, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 0, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 38a46a7c6b09591dee00daf2bcd674c143deef125b968629fa4550ab6f430a64.
        "completionLimit_term_products" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 1], global_labels: vec![0, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 1, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 12b51bb935563c01659d5480f39c95a873f9178f4d6c8fb22a6ffeac51aca3f4.
        "completionLimit_terms" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 1], global_labels: vec![0, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 1 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 5eed26b2aa9d5ab15d006434e764c42cb5548d804e20a6dd1b383431e67efa38.
        "completionNonrootRejected" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![1], global_labels: vec![0] },
            initial: Initial::Conditional(Snapshot { live: vec![0], ancestor: vec![0],
                genealogy: vec![Some(Tree::Leaf(0))],
                population: vec![Some(Location::Node(2))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen input request only, SHA256 4e636d82e3a8adf7da82cd9330f365d8dc19dcff07b1a927363e753b1eda035c.
        "completionPermutedFour" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
                edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }], leaves: vec![1, 2], hybrids: vec![] },
                sample: vec![0, 0, 0, 1], global_labels: vec![3, 0, 2, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1, 2, 3], ancestor: vec![0, 1, 2, 3],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1)), Some(Tree::Leaf(2)), Some(Tree::Leaf(3))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0)), Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 ee40f397aefe2e441b502e1189c30ad7193e0764e42b45db31830cf39baa9c62.
        "carriedOutsideWord" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 1, 1, 0], global_labels: vec![0, 1, 2, 3] },
            initial: Initial::Conditional(Snapshot { live: vec![2, 3], ancestor: vec![2, 2, 2, 3],
                genealogy: vec![None, None, Some(Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)))), Box::new(Tree::Leaf(2)))), Some(Tree::Leaf(3))],
                population: vec![None, None, Some(Location::Node(3)), Some(Location::Node(1))], register: vec![true, false, true, false, true] }), common: vec![false], slots: 1,
            word: vec![Symbol::Enter(3), Symbol::Interval(0), Symbol::Exit(2), Symbol::Exit(3), Symbol::Enter(2)], terminal: Terminal::FullView,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 cd9b7a2be45c26e19965ec22c18a3597d878465128a38208595863bc307734c2.
        "conditionalCommonFalseWord" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 1], global_labels: vec![0, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))],
                population: vec![Some(Location::Node(3)), Some(Location::Node(3))], register: vec![true, false, true, false, true] }), common: vec![true], slots: 0,
            word: vec![Symbol::Enter(3), Symbol::Enter(3)], terminal: Terminal::FullView,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 a2154c505257068c3fc2a7e927b422ad7b23083fe01d38e6f67c0d83420b4371.
        "conditionalCommonTrueWord" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 1], global_labels: vec![0, 1] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))],
                population: vec![Some(Location::Node(3)), Some(Location::Node(3))], register: vec![true, false, true, true, true] }), common: vec![true], slots: 0,
            word: vec![Symbol::Enter(3), Symbol::Enter(3)], terminal: Terminal::FullView,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 e60422f11866b4afa54ac8f210634224db08eaba535bac3b38dd1f3ab87ab6e9.
        "emptyConditionalWord" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![], global_labels: vec![] },
            initial: Initial::Conditional(Snapshot { live: vec![], ancestor: vec![],
                genealogy: vec![],
                population: vec![], register: vec![true, false, true] }), common: vec![], slots: 0,
            word: vec![], terminal: Terminal::FullView,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 86fb022a4b3e184763877aa61ee35a8c4d471412c822cb42562b863ff4eb02d5.
        "emptyNaturalCommonWord" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![], global_labels: vec![] },
            initial: Initial::Natural, common: vec![true], slots: 0,
            word: vec![Symbol::Enter(3), Symbol::Enter(3)], terminal: Terminal::FullView,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 3113b7000adba3b0ca13db119fdde8159f51fd8cc679e9b655aa70668062c2e3.
        "emptyNaturalWord" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![], global_labels: vec![] },
            initial: Initial::Natural, common: vec![true], slots: 0,
            word: vec![], terminal: Terminal::FullView,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 54f673b3e9a1c40084ea8c528126d5e802939464d84eadb1c54f3168bdf7e752.
        "ordinaryThreeComplete" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 4 }],
            leaves: vec![1, 3, 4], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![0, 1, 2] },
            initial: Initial::Natural, common: vec![], slots: 2,
            word: vec![Symbol::Enter(1), Symbol::Enter(3), Symbol::Enter(4), Symbol::Interval(0), Symbol::Exit(2), Symbol::Exit(3), Symbol::Enter(2), Symbol::Interval(1), Symbol::Exit(0), Symbol::Exit(1), Symbol::Enter(0)], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 6754b3cc7bbeb87a46f141b95e38bef3e95d6f701e1469d73e59a9d5f1cbcf8b.
        "ordinaryThreeFinite" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 4 }],
            leaves: vec![1, 3, 4], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![0, 1, 2] },
            initial: Initial::Natural, common: vec![], slots: 2,
            word: vec![Symbol::Enter(1), Symbol::Enter(3), Symbol::Enter(4), Symbol::Interval(0), Symbol::Exit(2), Symbol::Exit(3), Symbol::Enter(2), Symbol::Interval(1), Symbol::Exit(0), Symbol::Exit(1), Symbol::Enter(0)], terminal: Terminal::FullView,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 b1f6826803eca7189000b33b6c565b3b50511d18ab2d20c791430f6e330f5ad4.
        "parallelCommonCalendar" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![0, 1, 1], global_labels: vec![0, 1, 2] },
            initial: Initial::Natural, common: vec![true], slots: 3,
            word: vec![Symbol::Enter(1), Symbol::Enter(4), Symbol::Interval(0), Symbol::Exit(4), Symbol::Enter(3), Symbol::Interval(1), Symbol::Exit(2), Symbol::Exit(3), Symbol::Enter(2), Symbol::Interval(2), Symbol::Exit(0), Symbol::Exit(1), Symbol::Enter(0)], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 94599cd4f08ee94b222b71e347f1d17eeb9b3f6a62e49fcfc9705849a1158900.
        "parallelIndependentCalendar" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![0, 1, 1], global_labels: vec![0, 1, 2] },
            initial: Initial::Natural, common: vec![false], slots: 3,
            word: vec![Symbol::Enter(1), Symbol::Enter(4), Symbol::Interval(0), Symbol::Exit(4), Symbol::Enter(3), Symbol::Interval(1), Symbol::Exit(2), Symbol::Exit(3), Symbol::Enter(2), Symbol::Interval(2), Symbol::Exit(0), Symbol::Exit(1), Symbol::Enter(0)], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 f27bb2bc02c4848ac9154f6f579649b4424e6f3bc0d68868c8cc592488800b56.
        "permutedCalendar" => Some(Request { context: Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 4 }],
            leaves: vec![1, 3, 4], hybrids: vec![] },
            sample: vec![0, 1, 2], global_labels: vec![3, 0, 2] },
            initial: Initial::Natural, common: vec![], slots: 2,
            word: vec![Symbol::Enter(1), Symbol::Enter(3), Symbol::Enter(4), Symbol::Interval(0), Symbol::Exit(2), Symbol::Exit(3), Symbol::Enter(2), Symbol::Interval(1), Symbol::Exit(0), Symbol::Exit(1), Symbol::Enter(0)], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 9a6afbe1192bd0d6d3553756d8f13057cc3941a3642fe1a818ca97f95df04482.
        "repeatedIntervalSlot" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 0, 1], global_labels: vec![0, 1, 2] },
            initial: Initial::Conditional(Snapshot { live: vec![0, 1, 2], ancestor: vec![0, 1, 2],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1)), Some(Tree::Leaf(2))],
                population: vec![Some(Location::Ancestral(0)), Some(Location::Ancestral(0)), Some(Location::Ancestral(0))], register: vec![true, false, true] }), common: vec![], slots: 1,
            word: vec![Symbol::Interval(0), Symbol::Interval(0)], terminal: Terminal::FullView,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        // Frozen request only, SHA256 9d6f9035c349533f8d0a3d4639cf5d0afc486719a53735dd6a8363b491b55af5.
        "singletonCalendar" => Some(Request { context: Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0], global_labels: vec![0] },
            initial: Initial::Natural, common: vec![], slots: 1,
            word: vec![Symbol::Enter(1), Symbol::Enter(2), Symbol::Interval(0), Symbol::Exit(0), Symbol::Exit(1), Symbol::Enter(0)], terminal: Terminal::AncestralComplete,
            limits: Limits { initial_assignments: 16, initial_terms: 256, queries: 4096, branches: 65536, term_products: 262144, destinations: 4096, terms: 65536 }, provider_limits: ProviderLimits::default() }),
        _ => None,
    }
}
fn limit_kind(kind: LimitKind) -> String { match kind {
    LimitKind::InitialAssignments => "initial_assignments".into(), LimitKind::InitialTerms => "initial_terms".into(),
    LimitKind::Queries => "queries".into(), LimitKind::Branches => "branches".into(),
    LimitKind::TermProducts => "term_products".into(), LimitKind::Destinations => "destinations".into(),
    LimitKind::Terms => "terms".into(), LimitKind::Epoch(kind) => format!("EPOCH:{kind:?}"),
    LimitKind::Boundary(kind) => format!("BOUNDARY:{kind:?}"),
    LimitKind::Completion(kind) => format!("COMPLETION:{kind:?}"),
} }
fn main() {
    let args=std::env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() || !(args.len()==1 || args.len()==4 && args[1]=="--limit") {std::process::exit(2);}
    let Some(mut input)=fixture(&args[0]) else {std::process::exit(2);};
    if args.len()==4 {
        let Ok(cap)=args[3].parse::<usize>() else {std::process::exit(2);};
        match args[2].as_str() {
            "initial_assignments" => input.limits.initial_assignments=cap,
            "initial_terms" => input.limits.initial_terms=cap,
            "queries" => input.limits.queries=cap, "branches" => input.limits.branches=cap,
            "term_products" => input.limits.term_products=cap, "destinations" => input.limits.destinations=cap,
            "terms" => input.limits.terms=cap, _ => std::process::exit(2),
        }
    }
    let bank=variables(&input);
    let prefix=format!("\"schema\":\"source_word_probe_v1\",\"fixture\":\"{}\",\"request\":{},\"variables\":{},\"source_admission_verified\":false",
        args[0],request(&input),list(bank.iter(),|v|variable(*v)));
    match word::word_row(&input) {
        Ok(Decision::Table(table)) => {
            assert_eq!(table.variables,bank);
            let rows=list(table.transitions.iter(),|r|format!("{{\"view\":{},\"witness\":{},\"coefficients\":{}}}",view(&r.view),snapshot(&r.witness),polynomial(&r.polynomial)));
            let w=table.work;
            println!("{{{prefix},\"status\":\"TABLE\",\"rows\":{rows},\"work\":{{\"initial_assignments\":{},\"initial_term_contributions\":{},\"queries\":{},\"branches\":{},\"term_products\":{},\"largest_row\":{},\"largest_terms\":{}}}}}",
                w.initial_assignments,w.initial_term_contributions,w.queries,w.branches,w.term_products,w.largest_row,w.largest_terms);
        }
        Ok(Decision::Unknown(limit)) => {
            let stage=match limit.stage {Stage::Initialization=>"\"INITIAL\"".into(),Stage::Letter(i)=>i.to_string(),
                Stage::Completion=>"\"COMPLETION\"".into()};
            println!("{{{prefix},\"status\":\"UNKNOWN\",\"limit\":{{\"stage\":{stage},\"kind\":\"{}\",\"required\":{},\"cap\":{}}}}}",limit_kind(limit.kind),limit.required,limit.cap);
        }
        Err(Error::Unsupported(reason)) => println!("{{{prefix},\"status\":\"UNSUPPORTED\",\"reason\":\"{reason}\"}}"),
        Err(error) => {eprintln!("{error:?}");std::process::exit(1);}
    }
}
