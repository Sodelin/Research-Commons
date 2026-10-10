//! Fixed diagnostic fixtures for the internal ordered full source epoch.
//! No public RC1 endpoint, physical image or scientific certificate is added.
use parity_solver::{canonical, forest::Tree, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial,
    source_epoch::{self as epoch, Decision, Limits, SelectedView},
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
fn fixture(name: &str) -> (Context, Snapshot) {
    let source = if name == "parallelPanels" {
        Source { vertices: 5, root: 0, edges: vec![Edge { source: 0, target: 1 },
            Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 },
            Edge { source: 3, target: 4 }], leaves: vec![1, 4],
            hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] }
    } else {
        Source { vertices: 3, root: 0,
            edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
            leaves: vec![1, 2], hybrids: vec![] }
    };
    let sample = match name {
        "empty" => vec![], "oneAncestral" => vec![0], "nodeIdentity" => vec![0, 0],
        "twoEdgePanels" => vec![0, 0, 1, 1], "permutedRestricted" => vec![0, 1, 0],
        "parallelPanels" => vec![1; 4], _ => vec![0, 0, 0, 1],
    };
    let copies = sample.len();
    let global_labels = match name {
        "permutedRestricted" => vec![3, 0, 2], "parallelPanels" => vec![2, 0, 3, 1],
        _ => (0..copies).collect(),
    };
    let register = match name {
        "frozenRegister" => vec![true, false, true],
        "parallelPanels" => vec![true, false, true, false, true], _ => vec![false; source.vertices],
    };
    let context = Context { source, sample, global_labels };
    let mut start = Snapshot { live: (0..copies).collect(), ancestor: (0..copies).collect(),
        genealogy: (0..copies).map(|copy| Some(Tree::Leaf(copy))).collect(),
        population: vec![None; copies], register };
    let locations = match name {
        "empty" => vec![], "oneAncestral" => vec![Location::Ancestral(0)],
        "nodeIdentity" => vec![Location::Node(1); 2],
        "twoEdgePanels" => vec![Location::Edge(0), Location::Edge(0), Location::Edge(1), Location::Edge(1)],
        "permutedRestricted" => vec![Location::Edge(0), Location::Ancestral(0), Location::Edge(0)],
        "parallelPanels" => vec![Location::Edge(2), Location::Edge(2), Location::Edge(3), Location::Edge(3)],
        _ => vec![Location::Edge(0), Location::Edge(0), Location::Ancestral(0), Location::Ancestral(0)],
    };
    start.population = locations.into_iter().map(Some).collect();
    if name == "carriedNodeExterior" {
        start.live = vec![2, 3]; start.ancestor = vec![2, 2, 2, 3];
        start.genealogy = vec![None, None, Some(Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)),
            Box::new(Tree::Leaf(1)))), Box::new(Tree::Leaf(2)))), Some(Tree::Leaf(3))];
        start.population = vec![None, None, Some(Location::Node(1)), Some(Location::Ancestral(0))];
    }
    context.validate_snapshot(&start).expect("frozen original entering-state fixture");
    (context, start)
}

fn main() {
    let names = ["empty", "oneAncestral", "nodeIdentity", "twoEdgePanels", "edgeAncestral",
        "carriedNodeExterior", "permutedRestricted", "frozenRegister", "parallelPanels"];
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() > 1 || args.first().is_some_and(|name| !names.contains(&name.as_str())) {
        std::process::exit(2);
    }
    for name in names {
        if args.first().is_some_and(|wanted| wanted != name) { continue; }
        let (context, start) = fixture(name);
        let Decision::Table(result) = epoch::epoch_row(&context, &start, Limits::default()).unwrap()
            else { panic!("fixture resource limit"); };
        let rows = list(result.transitions.iter(), |transition|
            format!("{{\"view\":{},\"witness\":{},\"coefficients\":{}}}",
                view(&transition.view), snapshot(&transition.witness), coefficients(&transition.polynomial)));
        println!("{{\"schema\":\"source_epoch_probe_v1\",\"fixture\":\"{name}\",\"context\":{{\"vertices\":{},\"root\":{},\"edges\":{},\"leaves\":{},\"hybrids\":{},\"global_labels\":{},\"local_samples\":{},\"register\":{},\"start\":{}}},\"variables\":{},\"rows\":{},\"work\":{{\"calls\":{},\"lifted_terms\":{},\"largest_panel_row\":{},\"branches\":{},\"term_products\":{}}},\"source_admission_established\":false}}",
            context.source.vertices, context.source.root,
            list(context.source.edges.iter(), |edge| format!("[{},{}]", edge.source, edge.target)),
            list(context.source.leaves.iter(), |leaf| leaf.to_string()),
            list(context.source.hybrids.iter(), |hybrid| format!("[{},{},{}]", hybrid.vertex, hybrid.incoming[0], hybrid.incoming[1])),
            list(context.global_labels.iter(), |copy| copy.to_string()),
            list(context.sample.iter(), |taxon| taxon.to_string()),
            list(start.register.iter(), |bit| bit.to_string()), snapshot(&start),
            list(result.variables.iter(), |variable| place(*variable)), rows,
            result.work.calls, result.work.lifted_terms, result.work.largest_panel_row,
            result.work.branches, result.work.term_products);
    }
}
