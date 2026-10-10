//! Twelve frozen original entering-state boundary fixtures.
//! Only context/action fields are copied; expected coefficients are never used.
//! No public RC1 operation or original-source admission is added.
use parity_solver::{canonical, forest::Tree, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial,
    source_boundary::{self as boundary, Action, Decision, Limits}, source_epoch::SelectedView,
    source_population::{Context, Location, Snapshot}};

fn list<T>(items: impl IntoIterator<Item = T>, render: impl Fn(T) -> String) -> String {
    format!("[{}]", items.into_iter().map(render).collect::<Vec<_>>().join(","))
}
fn tree(t: &Tree) -> String { match t {
    Tree::Leaf(i) => i.to_string(), Tree::Node(left, right) => format!("[{},{}]", tree(left), tree(right)),
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
        list(v.genealogy.iter(), |t| tree(t.as_ref().expect("full-copy selected tree"))),
        list(v.population.iter(), |p| place(p.expect("full-copy selected location"))),
        list(v.register.iter(), |bit| bit.to_string()))
}
fn coefficients(p: &Polynomial) -> String {
    list(p.terms.iter(), |(powers, coefficient)| format!("[{},\"{}\"]",
        list(powers.iter(), |power| power.to_string()), canonical(coefficient)))
}
fn fixture(name: &str) -> (Context, Snapshot, Action) {
    match name {
        // Independent fixed entering context, SHA256 9fa156b3439d221f15c8812f21ed90500067e3181955d03866310c2d43581597.
        "emptyCommon" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![], global_labels: vec![] },
            Snapshot { live: vec![], ancestor: vec![],
                genealogy: vec![], population: vec![],
                register: vec![true, false, true, true, true] }, Action::Common(0)),
        // Independent fixed entering context, SHA256 67e789add346c9012a3fa69531f278da73883e7c156929e39210a3149d448117.
        "emptyIndependent" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![], global_labels: vec![] },
            Snapshot { live: vec![], ancestor: vec![],
                genealogy: vec![], population: vec![],
                register: vec![true, false, true, false, true] }, Action::Independent(0)),
        // Independent fixed entering context, SHA256 ede7911a67f3f38a93ebe3290e870966694337f5b80b52944be47765ac5b4111.
        "commonFalse" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 1], global_labels: vec![0, 1] },
            Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))], population: vec![Some(Location::Node(3)), Some(Location::Node(3))],
                register: vec![true, false, true, false, true] }, Action::Common(0)),
        // Independent fixed entering context, SHA256 357acfb35dbb3a16abb7d9a00bca5c0b96d629a3057dd047651a30803a62ceb6.
        "commonTrue" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 1], global_labels: vec![0, 1] },
            Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))], population: vec![Some(Location::Node(3)), Some(Location::Node(3))],
                register: vec![true, false, true, true, true] }, Action::Common(0)),
        // Independent fixed entering context, SHA256 adba9007e10233db8dd595ae77ebfbbb592a7bbdeb59b16967bc9ab8fe02b856.
        "independentTwo" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 1], global_labels: vec![0, 1] },
            Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))], population: vec![Some(Location::Node(3)), Some(Location::Node(3))],
                register: vec![true, false, true, true, true] }, Action::Independent(0)),
        // Independent fixed entering context, SHA256 f7e4d9cb2bb13ff1af6d16cfc67ee994140dd08aec52d1cd9352839a4e15028c.
        "carriedOwnerOutside" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 1, 1, 0], global_labels: vec![0, 1, 2, 3] },
            Snapshot { live: vec![2, 3], ancestor: vec![2, 2, 2, 3],
                genealogy: vec![None, None, Some(Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)))), Box::new(Tree::Leaf(2)))), Some(Tree::Leaf(3))], population: vec![None, None, Some(Location::Node(3)), Some(Location::Node(1))],
                register: vec![true, false, true, false, true] }, Action::Independent(0)),
        // Independent fixed entering context, SHA256 a576919fe7e7cb7f7ca8f28a4812216bc7df81e0f0406f0ffe9765d53f4d0813.
        "noOwnerAtSite" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 0], global_labels: vec![0, 1] },
            Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))], population: vec![Some(Location::Edge(2)), Some(Location::Node(1))],
                register: vec![true, false, true, true, true] }, Action::Independent(0)),
        // Independent fixed entering context, SHA256 5aab69ad8f971388ecaddf244e9ac798734c7dd9eb118cb47eaae4c0f9bda528.
        "parallelExit" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 1, 0], global_labels: vec![0, 1, 2] },
            Snapshot { live: vec![0, 1, 2], ancestor: vec![0, 1, 2],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1)), Some(Tree::Leaf(2))], population: vec![Some(Location::Edge(2)), Some(Location::Edge(3)), Some(Location::Node(1))],
                register: vec![true, false, true, false, true] }, Action::Exit(2)),
        // Independent fixed entering context, SHA256 7a1b2f33b75b9405427d3dff74218c664ba7ee9d372fa74fa30e70a81704a5e9.
        "ordinaryEntry" => (Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))], population: vec![Some(Location::Node(1)), Some(Location::Node(2))],
                register: vec![true, false, true] }, Action::Ordinary(0)),
        // Independent fixed entering context, SHA256 6de8f1b49d2979d748360c903ac9bcf3789ba4f96ff9d9f542508317073ab77d.
        "rootEntry" => (Context { source: Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] },
            sample: vec![0, 1], global_labels: vec![0, 1] },
            Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))], population: vec![Some(Location::Node(0)), Some(Location::Node(0))],
                register: vec![true, true, false] }, Action::Root),
        // Independent fixed entering context, SHA256 bb672bc6d4565b224071883202bf2ccc776931256a6210b62c9bb0e178605a59.
        "registerRepeat" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 0], global_labels: vec![0, 1] },
            Snapshot { live: vec![0, 1], ancestor: vec![0, 1],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1))], population: vec![Some(Location::Node(3)), Some(Location::Node(1))],
                register: vec![false, true, false, false, false] }, Action::Common(0)),
        // Independent fixed entering context, SHA256 ba23c92db666a146f4dfdb7635dd809e835fb6f757bdf2549b0d45a89f9bf567.
        "permutedIndependent" => (Context { source: Source { vertices: 5, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
            leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] },
            sample: vec![1, 0, 1], global_labels: vec![3, 0, 2] },
            Snapshot { live: vec![0, 1, 2], ancestor: vec![0, 1, 2],
                genealogy: vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1)), Some(Tree::Leaf(2))], population: vec![Some(Location::Node(3)), Some(Location::Node(1)), Some(Location::Node(3))],
                register: vec![true, false, true, false, true] }, Action::Independent(0)),
        _ => panic!("unknown frozen boundary fixture"),
    }
}

fn action(a: Action) -> String { match a {
    Action::Exit(e) => format!("[\"EXIT\",{e}]"), Action::Ordinary(e) => format!("[\"ORDINARY\",{e}]"),
    Action::Root => "[\"ROOT\"]".into(), Action::Common(h) => format!("[\"COMMON\",{h}]"),
    Action::Independent(h) => format!("[\"INDEPENDENT\",{h}]"),
} }
fn main() {
    let names = ["emptyCommon", "emptyIndependent", "commonFalse", "commonTrue", "independentTwo", "carriedOwnerOutside", "noOwnerAtSite", "parallelExit", "ordinaryEntry", "rootEntry", "registerRepeat", "permutedIndependent"];
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() > 1 || args.first().is_some_and(|name| !names.contains(&name.as_str())) {
        std::process::exit(2);
    }
    for name in names {
        if args.first().is_some_and(|wanted| wanted != name) { continue; }
        let (context, start, operation) = fixture(name);
        let Decision::Table(result) = boundary::boundary_row(&context, &start, operation, Limits::default()).unwrap()
            else { panic!("fixed boundary fixture resource limit"); };
        let rows = list(result.transitions.iter(), |transition|
            format!("{{\"view\":{},\"witness\":{},\"coefficients\":{}}}",
                view(&transition.view), snapshot(&transition.witness), coefficients(&transition.polynomial)));
        println!("{{\"schema\":\"source_boundary_probe_v1\",\"fixture\":\"{name}\",\"context\":{{\"vertices\":{},\"root\":{},\"edges\":{},\"leaves\":{},\"hybrids\":{},\"global_labels\":{},\"local_samples\":{},\"register\":{},\"start\":{}}},\"action\":{},\"variables\":{},\"rows\":{},\"work\":{{\"owners\":{},\"assignments\":{},\"destinations\":{},\"term_contributions\":{}}},\"source_admission_verified\":false}}",
            context.source.vertices, context.source.root,
            list(context.source.edges.iter(), |edge| format!("[{},{}]", edge.source, edge.target)),
            list(context.source.leaves.iter(), |leaf| leaf.to_string()),
            list(context.source.hybrids.iter(), |hybrid| format!("[{},{},{}]", hybrid.vertex, hybrid.incoming[0], hybrid.incoming[1])),
            list(context.global_labels.iter(), |copy| copy.to_string()),
            list(context.sample.iter(), |taxon| taxon.to_string()),
            list(start.register.iter(), |bit| bit.to_string()), snapshot(&start), action(operation),
            list(result.variables.iter(), |variable| format!("[\"ORIGINAL_GAMMA\",{variable}]")), rows,
            result.work.owners, result.work.assignments, result.work.destinations, result.work.term_contributions);
    }
}
