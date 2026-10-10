use parity_solver::{forest::Tree, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial,
    q, source_epoch::{self as epoch, Decision, LimitKind, Limits},
    source_population::{Context, Location, Snapshot}};

fn two_tip() -> Source { Source { vertices: 3, root: 0,
    edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
    leaves: vec![1, 2], hybrids: vec![] } }
fn tips(context: &Context, locations: &[Location], register: Vec<bool>) -> Snapshot {
    assert_eq!(locations.len(), context.sample.len());
    let snapshot = Snapshot { live: (0..locations.len()).collect(), ancestor: (0..locations.len()).collect(),
        genealogy: (0..locations.len()).map(|copy| Some(Tree::Leaf(copy))).collect(),
        population: locations.iter().copied().map(Some).collect(), register };
    context.validate_snapshot(&snapshot).unwrap(); snapshot
}
fn table(context: &Context, snapshot: &Snapshot) -> epoch::Table {
    match epoch::epoch_row(context, snapshot, Limits::default()).unwrap() {
        Decision::Table(table) => table, other => panic!("unexpected {other:?}"),
    }
}
fn two_panels() -> (Context, Snapshot) {
    let context = Context { source: two_tip(), sample: vec![0, 0, 1, 1], global_labels: vec![0, 1, 2, 3] };
    let snapshot = tips(&context, &[Location::Edge(0), Location::Edge(0),
        Location::Edge(1), Location::Edge(1)], vec![true, false, true]);
    (context, snapshot)
}
fn two_root_factor(dimension: usize, variable: usize, unchanged: bool) -> Polynomial {
    let x = Polynomial::variable(dimension, variable).unwrap();
    if unchanged { x } else { Polynomial::one(dimension).subtract(&x).unwrap().scale(&q(1, 2)) }
}

#[test]
fn two_original_edge_panels_keep_every_ordered_view_coefficient() {
    let (context, snapshot) = two_panels();
    let result = table(&context, &snapshot);
    assert_eq!(result.variables, vec![Location::Edge(0), Location::Edge(1), Location::Ancestral(0)]);
    assert_eq!(result.transitions.len(), 9);
    for transition in &result.transitions {
        assert_eq!(transition.view, epoch::selected_view(&context, &transition.witness).unwrap());
        assert_eq!(transition.view.population, snapshot.population);
        assert_eq!(transition.view.register, snapshot.register);
        let expected = two_root_factor(3, 0, transition.view.genealogy[0] == Some(Tree::Leaf(0)))
            .multiply(&two_root_factor(3, 1, transition.view.genealogy[2] == Some(Tree::Leaf(2)))).unwrap();
        assert_eq!(transition.polynomial, expected);
        assert!(transition.polynomial.terms.keys().all(|powers| powers[2] == 0));
    }
    let quotient = epoch::unordered_pushforward(&context, &result).unwrap();
    assert_eq!(quotient.len(), 4);
    assert_eq!(result.work.calls, 7); // Two three-call kernels and one empty identity panel.
    assert_eq!(result.work.lifted_terms, 8);
    assert_eq!(result.work.branches, 21); // 3, 9 and 9 raw normalized-row branches.
    assert_eq!(result.work.term_products, 55); // 5, 25 and 25 raw polynomial term products.
}

#[test]
fn node_locations_are_exterior_identity_and_each_copy_keeps_its_tree() {
    let context = Context { source: two_tip(), sample: vec![0, 0, 1], global_labels: vec![2, 0, 3] };
    let snapshot = tips(&context, &[Location::Node(1), Location::Node(1), Location::Ancestral(0)],
        vec![true, false, true]);
    let result = table(&context, &snapshot);
    assert_eq!(result.transitions.len(), 1);
    assert_eq!(result.transitions[0].witness, snapshot);
    assert_eq!(result.transitions[0].view.genealogy, vec![Some(Tree::Leaf(0)), Some(Tree::Leaf(1)), Some(Tree::Leaf(2))]);
    assert_eq!(result.transitions[0].polynomial, Polynomial::one(3));
    assert_eq!(result.panels.iter().map(|panel| panel.copies.clone()).collect::<Vec<_>>(),
        vec![vec![], vec![], vec![2]]);
}

#[test]
fn whole_copy_panel_restriction_handles_carried_nonminimum_representatives() {
    let context = Context { source: two_tip(), sample: vec![0, 0, 0, 1], global_labels: vec![3, 0, 2, 1] };
    let carried = Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)))),
        Box::new(Tree::Leaf(2)));
    let snapshot = Snapshot { live: vec![2, 3], ancestor: vec![2, 2, 2, 3],
        genealogy: vec![None, None, Some(carried.clone()), Some(Tree::Leaf(3))],
        population: vec![None, None, Some(Location::Edge(0)), Some(Location::Node(2))],
        register: vec![false, true, false] };
    let panel = epoch::restrict_panel(&context, &snapshot, Location::Edge(0)).unwrap();
    assert_eq!(panel.copies, vec![0, 1, 2]);
    assert_eq!(panel.context.global_labels, vec![3, 0, 2]);
    assert_eq!(panel.start.live, vec![2]);
    assert_eq!(panel.start.ancestor, vec![2, 2, 2]);
    let result = table(&context, &snapshot);
    assert_eq!(result.transitions.len(), 1);
    assert_eq!(result.transitions[0].witness, snapshot);
    assert_eq!(result.transitions[0].view.genealogy, vec![Some(carried.clone()), Some(carried.clone()),
        Some(carried), Some(Tree::Leaf(3))]);
    assert_eq!(result.transitions[0].polynomial, Polynomial::one(3));
}

#[test]
fn distinct_parallel_populations_have_distinct_original_rate_coordinates() {
    let source = Source { vertices: 5, root: 0, edges: vec![Edge { source: 0, target: 1 },
        Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 },
        Edge { source: 3, target: 4 }], leaves: vec![1, 4],
        hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] };
    let context = Context { source, sample: vec![1; 4], global_labels: vec![3, 0, 2, 1] };
    let snapshot = tips(&context, &[Location::Edge(2), Location::Edge(2), Location::Edge(3), Location::Edge(3)],
        vec![true, false, true, false, true]);
    let result = table(&context, &snapshot);
    assert_eq!(result.variables.len(), 6);
    assert_eq!(result.transitions.len(), 9);
    for transition in &result.transitions {
        let expected = two_root_factor(6, 2, transition.view.genealogy[0] == Some(Tree::Leaf(0)))
            .multiply(&two_root_factor(6, 3, transition.view.genealogy[2] == Some(Tree::Leaf(2)))).unwrap();
        assert_eq!(transition.polynomial, expected);
        assert_eq!(transition.view.population, snapshot.population);
        assert_eq!(transition.view.register, snapshot.register);
        assert!(transition.polynomial.terms.keys().all(|powers|
            powers[0] == 0 && powers[1] == 0 && powers[4] == 0 && powers[5] == 0));
    }
}

#[test]
fn empty_and_one_copy_epochs_include_all_empty_population_identity_calls() {
    for copies in [0, 1] {
        let context = Context { source: two_tip(), sample: vec![0; copies], global_labels: (0..copies).collect() };
        let snapshot = tips(&context, &vec![Location::Ancestral(0); copies], vec![false; 3]);
        let result = table(&context, &snapshot);
        assert_eq!(result.transitions.len(), 1);
        assert_eq!(result.transitions[0].polynomial, Polynomial::one(3));
        assert_eq!(result.transitions[0].witness, snapshot);
        assert_eq!(result.work.calls, 3);
        assert_eq!(result.work.lifted_terms, 0);
        assert_eq!(result.work.branches, 3);
        assert_eq!(result.work.term_products, 3);
    }
}

#[test]
fn every_resource_bound_is_cumulative_or_explicitly_per_panel_without_partial_rows() {
    let (context, snapshot) = two_panels();
    for (kind, limits) in [(LimitKind::Calls, Limits { calls: 0, ..Limits::default() }),
        (LimitKind::Destinations, Limits { destinations: 0, ..Limits::default() }),
        (LimitKind::LiftedTerms, Limits { lifted_terms: 0, ..Limits::default() }),
        (LimitKind::Branches, Limits { branches: 0, ..Limits::default() }),
        (LimitKind::TermProducts, Limits { term_products: 0, ..Limits::default() })] {
        assert!(matches!(epoch::epoch_row(&context, &snapshot, limits).unwrap(),
            Decision::Unknown(limit) if limit.kind == kind && limit.cap == 0));
    }
    let result = table(&context, &snapshot);
    let exact = Limits { calls: result.work.calls, destinations: result.work.largest_panel_row,
        lifted_terms: result.work.lifted_terms, branches: result.work.branches,
        term_products: result.work.term_products };
    assert_eq!(epoch::epoch_row(&context, &snapshot, exact).unwrap(), Decision::Table(result));
    for (kind, limits, required) in [
        (LimitKind::Calls, Limits { calls: 6, ..exact }, 7),
        (LimitKind::LiftedTerms, Limits { lifted_terms: 7, ..exact }, 8),
        (LimitKind::Branches, Limits { branches: 20, ..exact }, 21),
        (LimitKind::TermProducts, Limits { term_products: 54, ..exact }, 55)] {
        assert!(matches!(epoch::epoch_row(&context, &snapshot, limits).unwrap(),
            Decision::Unknown(limit) if limit.kind == kind && limit.required == required));
    }
}

#[test]
fn range_witness_gluing_rejects_bad_context_and_shared_register() {
    let (context, snapshot) = two_panels();
    let panel = epoch::restrict_panel(&context, &snapshot, Location::Edge(0)).unwrap();
    let destination = panel.start.merge(&panel.context, 1, 0).unwrap();
    let joined = epoch::join_panel(&context, &snapshot, &panel, &destination).unwrap();
    context.validate_snapshot(&joined).unwrap();
    assert_eq!(joined.genealogy[1], Some(Tree::Node(Box::new(Tree::Leaf(1)), Box::new(Tree::Leaf(0)))));
    assert_eq!(joined.genealogy[2], snapshot.genealogy[2]);
    assert_eq!(joined.genealogy[3], snapshot.genealogy[3]);
    let mut forged = panel.clone(); forged.copies = vec![0, 2];
    assert!(epoch::join_panel(&context, &snapshot, &forged, &destination).is_err());
    let mut forged = destination.clone(); forged.register[0] = !forged.register[0];
    assert_eq!(epoch::join_panel(&context, &snapshot, &panel, &forged), Err("SOURCE_EPOCH_PANEL_CONTEXT"));
    let mut forged = destination; forged.genealogy[0] = Some(Tree::Leaf(0));
    assert!(epoch::join_panel(&context, &snapshot, &panel, &forged).is_err());
}

#[test]
fn ordered_selected_view_omits_representative_but_keeps_child_orientation() {
    let context = Context { source: two_tip(), sample: vec![0, 1], global_labels: vec![0, 1] };
    let ordered = Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)));
    let first = Snapshot::from_lineages(&context, &[(0, ordered.clone())], Location::Ancestral(0), vec![false; 3]).unwrap();
    let second = Snapshot::from_lineages(&context, &[(1, ordered)], Location::Ancestral(0), vec![false; 3]).unwrap();
    assert_ne!(first, second);
    let a = table(&context, &first); let b = table(&context, &second);
    assert_eq!(a.transitions[0].view, b.transitions[0].view);
    assert_eq!(a.transitions[0].polynomial, b.transitions[0].polynomial);
    let reverse = Snapshot::from_lineages(&context, &[(1, Tree::Node(Box::new(Tree::Leaf(1)),
        Box::new(Tree::Leaf(0))))], Location::Ancestral(0), vec![false; 3]).unwrap();
    assert_ne!(a.transitions[0].view, table(&context, &reverse).transitions[0].view);
}
