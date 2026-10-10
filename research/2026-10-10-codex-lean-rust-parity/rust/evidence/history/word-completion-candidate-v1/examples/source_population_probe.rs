//! Fixed-fixture diagnostic probe for the library-only source refinement.
//! This is not a public RC1 endpoint or an admitted source-law certificate.
use parity_solver::{canonical, forest::Tree, natural_cell::{Edge, Source}, polynomial::Polynomial,
    source_population::{self as population, Context, Decision, Limits, Location, Snapshot}};

fn list<T>(items: impl IntoIterator<Item = T>, render: impl Fn(T) -> String) -> String {
    format!("[{}]", items.into_iter().map(render).collect::<Vec<_>>().join(","))
}
fn tree(t: &Tree) -> String { match t {
    Tree::Leaf(i) => i.to_string(), Tree::Node(a, b) => format!("[{},{}]", tree(a), tree(b)),
} }
fn place(p: Location) -> String { match p {
    Location::Node(i) => format!("[\"V\",{i}]"), Location::Edge(i) => format!("[\"E\",{i}]"),
    Location::Ancestral(i) => format!("[\"A\",{i}]"),
} }
fn snapshot(s: &Snapshot) -> String {
    format!("\"live\":{},\"ancestor\":{},\"genealogy\":{},\"location\":{},\"register\":{}",
        list(s.live.iter(), |i| i.to_string()), list(s.ancestor.iter(), |i| i.to_string()),
        list(s.genealogy.iter(), |t| t.as_ref().map(tree).unwrap_or_else(|| "null".into())),
        list(s.population.iter(), |p| p.map(place).unwrap_or_else(|| "null".into())),
        list(s.register.iter(), |b| b.to_string()))
}
fn coefficients(p: &Polynomial) -> String {
    list(p.terms.iter(), |(powers, coefficient)| format!("[{},\"{}\"]", powers[0], canonical(coefficient)))
}

fn main() {
    let source = Source { vertices: 3, root: 0,
        edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
        leaves: vec![1, 2], hybrids: vec![] };
    let names = ["emptyEdge0", "oneAncestral", "twoAncestral", "threeEdge0", "fourAncestral",
        "carriedNonminimum", "permutedRestrictedEdge0", "frozenRegisterRepeat"];
    let wanted = std::env::args().nth(1);
    if wanted.as_ref().is_some_and(|name| !names.contains(&name.as_str())) { std::process::exit(1); }
    for name in names {
        if wanted.as_ref().is_some_and(|wanted| wanted != name) { continue; }
        let copies = match name { "emptyEdge0" => 0, "oneAncestral" => 1, "twoAncestral" => 2,
            "threeEdge0" | "permutedRestrictedEdge0" | "frozenRegisterRepeat" => 3, _ => 4 };
        let population = if name.ends_with("Edge0") || name == "frozenRegisterRepeat" {
            Location::Edge(0) } else { Location::Ancestral(0) };
        let sample = match name { "twoAncestral" => vec![0, 1],
            "fourAncestral" | "carriedNonminimum" => vec![0, 1, 0, 1],
            _ => vec![0; copies] };
        let global_labels = if name == "permutedRestrictedEdge0" { vec![3, 0, 2] }
            else { (0..copies).collect() };
        let register = if name == "frozenRegisterRepeat" { vec![true, false, true] }
            else if name == "threeEdge0" { vec![false, true, false] }
            else { vec![false; 3] };
        let lineages = if name == "carriedNonminimum" {
            vec![(2, Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)))),
                Box::new(Tree::Leaf(2)))), (3, Tree::Leaf(3))]
        } else { (0..copies).map(|i| (i, Tree::Leaf(i))).collect() };
        let context = Context { source: source.clone(), sample, global_labels };
        let start = Snapshot::from_lineages(&context, &lineages, population, register.clone()).unwrap();
        let Decision::Table(result) = population::population_row(&context, &start, population,
            Limits::default()).unwrap() else { panic!("fixture resource limit"); };
        let unordered = population::unordered_pushforward(&context, &result).unwrap();
        let rows = list(result.transitions.iter(), |t| format!("{{{},\"coefficients\":{}}}",
            snapshot(&t.destination), coefficients(&t.polynomial)));
        let unordered = list(unordered.values(), |(f, p)| format!("{{\"forest\":{},\"coefficients\":{}}}",
            list(f.iter(), tree), coefficients(p)));
        println!("{{\"schema\":\"source_population_probe_v1\",\"fixture\":\"{name}\",\"context\":{{\"vertices\":3,\"root\":0,\"edges\":[[0,1],[0,2]],\"leaves\":[1,2],\"hybrids\":[],\"global_labels\":{},\"local_samples\":{},\"population\":{},\"register\":{},\"start\":{{{}}}}},\"rows\":{},\"unordered\":{},\"work\":{{\"calls\":{},\"lifted_terms\":{},\"largest_row\":{}}},\"source_admission_established\":false}}",
            list(context.global_labels.iter(), |i| i.to_string()), list(context.sample.iter(), |i| i.to_string()),
            place(population), list(register.iter(), |b| b.to_string()), snapshot(&start), rows, unordered,
            result.work.calls, result.work.lifted_terms, result.work.largest_row);
    }
}
