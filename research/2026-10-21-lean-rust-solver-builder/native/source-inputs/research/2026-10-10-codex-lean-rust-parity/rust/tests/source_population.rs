use parity_solver::{forest::Tree, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial,
    q, source_population::{self as population, Context, Decision, LimitKind, Limits, Location, Snapshot}};

fn two_tip() -> Source { Source { vertices: 3, root: 0,
    edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
    leaves: vec![1, 2], hybrids: vec![] } }
fn context(copies: usize) -> Context {
    Context { source: two_tip(), sample: vec![0; copies], global_labels: (0..copies).collect() }
}
fn start(context: &Context, place: Location) -> Snapshot {
    let lineages = (0..context.sample.len()).map(|i| (i, Tree::Leaf(i))).collect::<Vec<_>>();
    Snapshot::from_lineages(context, &lineages, place, vec![false, true, false]).unwrap()
}
fn table(context: &Context, snapshot: &Snapshot, place: Location) -> population::Table {
    match population::population_row(context, snapshot, place, Limits::default()).unwrap() {
        Decision::Table(table) => table, other => panic!("unexpected {other:?}"),
    }
}

#[test]
fn ordered_merger_retains_literal_survivor_and_half_rate() {
    let context = context(2);
    let snapshot = start(&context, Location::Edge(0));
    let result = table(&context, &snapshot, Location::Edge(0));
    assert_eq!(result.transitions.len(), 3);
    let x = Polynomial::variable(1, 0).unwrap();
    let half = Polynomial::one(1).subtract(&x).unwrap().scale(&q(1, 2));
    for transition in &result.transitions {
        if transition.destination == snapshot { assert_eq!(transition.polynomial, x); }
        else {
            assert_eq!(transition.polynomial, half);
            let a = transition.destination.live[0];
            let b = 1 - a;
            assert_eq!(transition.destination.ancestor, vec![a, a]);
            assert_eq!(transition.destination.genealogy[a], Some(Tree::Node(
                Box::new(Tree::Leaf(a)), Box::new(Tree::Leaf(b)))));
            assert_eq!(transition.destination.genealogy[b], None);
            assert_eq!(transition.destination.population, (0..2).map(|i|
                if i == a { Some(Location::Edge(0)) } else { None }).collect::<Vec<_>>());
            assert_eq!(transition.destination.register, snapshot.register);
        }
    }
    let quotient = population::unordered_pushforward(&context, &result).unwrap();
    assert_eq!(quotient["[(0,1)]"].1, Polynomial::one(1).subtract(&x).unwrap());
}

#[test]
fn full_ordered_rows_keep_every_orientation_and_ancestor_fibre() {
    for (copies, literal_count, unordered_count) in [(0, 1, 1), (1, 1, 1), (2, 3, 2),
        (3, 19, 7), (4, 193, 37)] {
        let context = context(copies);
        let snapshot = start(&context, Location::Ancestral(0));
        let result = table(&context, &snapshot, Location::Ancestral(0));
        assert_eq!(result.transitions.len(), literal_count);
        let quotient = population::unordered_pushforward(&context, &result).unwrap();
        assert_eq!(quotient.len(), unordered_count);
        assert_eq!(result.transitions.iter().fold(Polynomial::zero(1), |sum, t|
            sum.add(&t.polynomial).unwrap()), Polynomial::one(1));
        for transition in &result.transitions {
            assert_eq!(transition.polynomial.evaluate(&[q(1, 1)]).unwrap(),
                q(i64::from(transition.destination == snapshot), 1));
            let value = transition.polynomial.evaluate(&[q(1, 2)]).unwrap();
            assert!(value >= q(0, 1) && value <= q(1, 1));
        }
    }
}

#[test]
fn carried_subtrees_nonminimum_representatives_and_label_embedding_are_literal() {
    let mut context = context(4);
    context.global_labels = vec![3, 0, 2, 1];
    let carried = Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)))),
        Box::new(Tree::Leaf(2)));
    let snapshot = Snapshot::from_lineages(&context, &[(2, carried.clone()), (3, Tree::Leaf(3))],
        Location::Ancestral(0), vec![true, false, true]).unwrap();
    assert_eq!(snapshot.ancestor, vec![2, 2, 2, 3]);
    let merged = snapshot.merge(&context, 3, 2).unwrap();
    assert_eq!(merged.live, vec![3]);
    assert_eq!(merged.genealogy[3], Some(Tree::Node(Box::new(Tree::Leaf(3)), Box::new(carried))));
    assert_eq!(merged.ancestor, vec![3; 4]);
    assert_eq!(merged.register, snapshot.register);
    assert_eq!(population::forest_key(&population::unordered_forest(&context, &snapshot).unwrap()),
        "[((0,3),2),1]");
    assert_eq!(table(&context, &snapshot, Location::Ancestral(0)).transitions.len(), 3);
}

#[test]
fn canonical_snapshot_source_descendants_and_co_location_are_checked() {
    let context = context(2);
    let snapshot = start(&context, Location::Edge(0));
    let mut wrong = snapshot.clone(); wrong.ancestor[0] = 1;
    assert!(context.validate_snapshot(&wrong).is_err());
    let mut wrong = snapshot.clone(); wrong.genealogy[0] = Some(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(0))));
    assert!(context.validate_snapshot(&wrong).is_err());
    let mut wrong = snapshot.merge(&context, 0, 1).unwrap(); wrong.genealogy[1] = Some(Tree::Leaf(1));
    assert_eq!(context.validate_snapshot(&wrong), Err("SOURCE_CANONICAL_DEAD_FIELDS"));
    let mut wrong_context = context.clone(); wrong_context.sample[1] = 1;
    assert_eq!(wrong_context.validate_snapshot(&snapshot), Err("SOURCE_DESCENDANT"));
    let mut wrong_context = context.clone(); wrong_context.global_labels[1] = 0;
    assert!(wrong_context.validate().is_err());
    let node = start(&context, Location::Node(1));
    assert_eq!(population::population_row(&context, &node, Location::Node(1), Limits::default()),
        Err("SOURCE_NOT_COLOCATED"));
    assert!(Snapshot::from_lineages(&context, &[(1, Tree::Leaf(0)), (0, Tree::Leaf(1))],
        Location::Ancestral(0), vec![false; 3]).is_err());
}

#[test]
fn original_parallel_occurrences_and_vertex_registers_are_preserved() {
    let source = Source { vertices: 5, root: 0, edges: vec![Edge { source: 0, target: 1 },
        Edge { source: 0, target: 2 }, Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 },
        Edge { source: 3, target: 4 }], leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] };
    let context = Context { source, sample: vec![1; 3], global_labels: vec![2, 0, 3] };
    let lineages = (0..3).map(|i| (i, Tree::Leaf(i))).collect::<Vec<_>>();
    let register = vec![true, false, true, false, true];
    let mut tables = vec![];
    for edge in [2, 3] {
        let snapshot = Snapshot::from_lineages(&context, &lineages, Location::Edge(edge), register.clone()).unwrap();
        let result = table(&context, &snapshot, Location::Edge(edge));
        for transition in &result.transitions {
            assert_eq!(transition.destination.register, register);
            for &a in &transition.destination.live {
                assert_eq!(transition.destination.population[a], Some(Location::Edge(edge)));
            }
        }
        tables.push(population::unordered_pushforward(&context, &result).unwrap());
    }
    assert_eq!(tables[0], tables[1]); // Same scalar kernel, distinctly retained population identities above.
}

#[test]
fn bounded_refusal_never_returns_a_partial_transition_row() {
    let context = context(4);
    let snapshot = start(&context, Location::Ancestral(0));
    for (kind, limits) in [(LimitKind::Calls, Limits { calls: 0, ..Limits::default() }),
        (LimitKind::Destinations, Limits { destinations: 0, ..Limits::default() }),
        (LimitKind::LiftedTerms, Limits { lifted_terms: 0, ..Limits::default() })] {
        assert!(matches!(population::population_row(&context, &snapshot, Location::Ancestral(0), limits).unwrap(),
            Decision::Unknown(limit) if limit.kind == kind));
    }
    let result = table(&context, &snapshot, Location::Ancestral(0));
    let exact = Limits { calls: result.work.calls, destinations: result.work.largest_row,
        lifted_terms: result.work.lifted_terms };
    assert_eq!(population::population_row(&context, &snapshot, Location::Ancestral(0), exact).unwrap(), Decision::Table(result));
    let limited = Limits { calls: exact.calls - 1, ..exact };
    assert!(matches!(population::population_row(&context, &snapshot, Location::Ancestral(0), limited).unwrap(),
        Decision::Unknown(limit) if limit.kind == LimitKind::Calls));
}
