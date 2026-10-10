use parity_solver::{forest::Tree, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial, q,
    source_boundary::{self as boundary, Action, Decision, Error, LimitKind, Limits},
    source_epoch, source_population::{Context, Location, Snapshot}};

fn two_tip() -> Source { Source { vertices: 3, root: 0,
    edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
    leaves: vec![1, 2], hybrids: vec![] } }
fn parallel() -> Source { Source { vertices: 5, root: 0,
    edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
        Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
    leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] } }
fn tips(context: &Context, places: &[Location], register: Vec<bool>) -> Snapshot {
    let snapshot = Snapshot { live: (0..places.len()).collect(), ancestor: (0..places.len()).collect(),
        genealogy: (0..places.len()).map(|copy| Some(Tree::Leaf(copy))).collect(),
        population: places.iter().copied().map(Some).collect(), register };
    context.validate_snapshot(&snapshot).unwrap(); snapshot
}
fn table(context: &Context, snapshot: &Snapshot, action: Action) -> boundary::Table {
    match boundary::boundary_row(context, snapshot, action, Limits::default()).unwrap() {
        Decision::Table(result) => result, other => panic!("unexpected {other:?}"),
    }
}
fn at_hybrid(copies: usize) -> (Context, Snapshot) {
    let context = Context { source: parallel(), sample: vec![1; copies], global_labels: (0..copies).collect() };
    let snapshot = tips(&context, &vec![Location::Node(3); copies], vec![true, false, true, false, true]);
    (context, snapshot)
}

#[test]
fn independent_original_gamma_is_parent_one_with_exact_asymmetric_weights() {
    let (context, snapshot) = at_hybrid(2);
    let result = table(&context, &snapshot, Action::Independent(0));
    assert_eq!(result.transitions.len(), 4);
    assert_eq!(result.variables, vec![0]);
    assert_eq!(result.work, boundary::Work { owners: 2, assignments: 4, destinations: 4, term_contributions: 8 });
    let gamma = Polynomial::variable(1, 0).unwrap();
    let false_weight = Polynomial::one(1).subtract(&gamma).unwrap();
    for transition in &result.transitions {
        let truths = transition.view.population.iter().filter(|place| **place == Some(Location::Edge(3))).count();
        let expected = gamma.power(truths).unwrap().multiply(&false_weight.power(2 - truths).unwrap()).unwrap();
        assert_eq!(transition.polynomial, expected);
        assert_eq!(transition.polynomial.evaluate(&[q(1, 3)]).unwrap(), [q(4, 9), q(2, 9), q(1, 9)][truths]);
        assert_eq!(transition.view, source_epoch::selected_view(&context, &transition.witness).unwrap());
        assert_eq!(transition.witness.live, snapshot.live);
        assert_eq!(transition.witness.ancestor, snapshot.ancestor);
        assert_eq!(transition.witness.genealogy, snapshot.genealogy);
        assert_eq!(transition.witness.register, snapshot.register);
    }
}

#[test]
fn common_reuses_the_entering_site_register_without_redrawing_or_mutating_any_bit() {
    let (context, mut snapshot) = at_hybrid(2);
    for bit in [false, true] {
        snapshot.register[3] = bit;
        let result = table(&context, &snapshot, Action::Common(0));
        assert_eq!(result.transitions.len(), 1);
        assert_eq!(result.transitions[0].polynomial, Polynomial::one(1));
        assert_eq!(result.transitions[0].witness.population, vec![Some(Location::Edge(if bit { 3 } else { 2 })); 2]);
        assert_eq!(result.transitions[0].view.register, snapshot.register);
        assert_eq!(result.work.owners, 2);
        assert_eq!(result.work.term_contributions, 1);
    }
}

#[test]
fn carried_nonminimum_owner_gets_one_coin_and_keeps_the_other_population() {
    let context = Context { source: parallel(), sample: vec![1, 1, 1, 0], global_labels: vec![3, 0, 2, 1] };
    let carried = Tree::Node(Box::new(Tree::Leaf(2)), Box::new(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)))));
    let snapshot = Snapshot { live: vec![2, 3], ancestor: vec![2, 2, 2, 3],
        genealogy: vec![None, None, Some(carried.clone()), Some(Tree::Leaf(3))],
        population: vec![None, None, Some(Location::Node(3)), Some(Location::Ancestral(0))],
        register: vec![true, false, true, false, true] };
    let result = table(&context, &snapshot, Action::Independent(0));
    assert_eq!(result.work, boundary::Work { owners: 1, assignments: 2, destinations: 2, term_contributions: 3 });
    for transition in &result.transitions {
        assert_eq!(transition.witness.genealogy, snapshot.genealogy);
        assert_eq!(transition.witness.ancestor, vec![2, 2, 2, 3]);
        assert_eq!(transition.view.genealogy, vec![Some(carried.clone()), Some(carried.clone()), Some(carried.clone()), Some(Tree::Leaf(3))]);
        assert!(transition.view.population[..3].iter().all(|place| *place == transition.view.population[0]));
        assert_eq!(transition.view.population[3], Some(Location::Ancestral(0)));
        assert_eq!(transition.witness.register, snapshot.register);
    }
}

#[test]
fn empty_and_unoccupied_sites_are_identity_with_one_assignment_and_one_term() {
    for copies in [0, 2] {
        let (context, mut snapshot) = at_hybrid(copies);
        snapshot.population = vec![Some(Location::Ancestral(0)); copies];
        for action in [Action::Common(0), Action::Independent(0), Action::Exit(2), Action::Ordinary(1), Action::Root] {
            let result = table(&context, &snapshot, action);
            assert_eq!(result.transitions.len(), 1);
            assert_eq!(result.transitions[0].witness, snapshot);
            assert_eq!(result.transitions[0].polynomial, Polynomial::one(1));
            assert_eq!(result.work, boundary::Work { owners: 0, assignments: 1, destinations: 1, term_contributions: 1 });
        }
    }
}

#[test]
fn every_limit_prechecks_exact_requirements_and_returns_no_partial_table() {
    for copies in 0..=4 {
        let (context, snapshot) = at_hybrid(copies);
        let result = table(&context, &snapshot, Action::Independent(0));
        let assignments = 1 << copies;
        let terms = if copies == 0 { 1 } else { assignments + copies * (assignments / 2) };
        let exact = Limits { assignments, destinations: assignments, term_contributions: terms };
        assert_eq!(boundary::boundary_row(&context, &snapshot, Action::Independent(0), exact).unwrap(), Decision::Table(result));
        for (kind, required, limits) in [
            (LimitKind::Assignments, assignments, Limits { assignments: assignments - 1, ..exact }),
            (LimitKind::Destinations, assignments, Limits { destinations: assignments - 1, ..exact }),
            (LimitKind::TermContributions, terms, Limits { term_contributions: terms - 1, ..exact })] {
            assert_eq!(boundary::boundary_row(&context, &snapshot, Action::Independent(0), limits).unwrap(),
                Decision::Unknown(boundary::Limit { kind, required, cap: required - 1 }));
        }
    }
    let (context, snapshot) = at_hybrid(4);
    assert_eq!(table(&context, &snapshot, Action::Independent(0)).work.term_contributions, 48);
    assert!(matches!(boundary::boundary_row(&context, &snapshot, Action::Independent(0),
        Limits { assignments: 0, destinations: 0, term_contributions: 0 }).unwrap(),
        Decision::Unknown(limit) if limit.kind == LimitKind::Assignments && limit.required == 16));
}

#[test]
fn input_admission_is_checked_before_limits_and_parent_occurrences_are_authentic() {
    let (context, snapshot) = at_hybrid(2);
    let none = Limits { assignments: 0, destinations: 0, term_contributions: 0 };
    for action in [Action::Exit(999), Action::Ordinary(999), Action::Common(1), Action::Independent(1)] {
        assert!(matches!(boundary::boundary_row(&context, &snapshot, action, none), Err(Error::InvalidInput(_))));
    }
    assert_eq!(boundary::boundary_row(&context, &snapshot, Action::Ordinary(2), Limits::default()),
        Err(Error::InvalidInput("SOURCE_BOUNDARY_ORDINARY_DEGREE")));
    for parents in [[2, 2], [2, 4], [2, 999]] {
        let mut bad = context.clone(); bad.source.hybrids[0].incoming = parents;
        assert!(matches!(boundary::boundary_row(&bad, &snapshot, Action::Independent(0), none), Err(Error::InvalidInput(_))));
    }
    let mut bad = context.clone(); bad.source.hybrids.push(bad.source.hybrids[0].clone());
    assert!(matches!(boundary::boundary_row(&bad, &snapshot, Action::Common(0), none), Err(Error::InvalidInput(_))));
    let mut bad = snapshot; bad.register.pop();
    assert!(matches!(boundary::boundary_row(&context, &bad, Action::Common(0), none), Err(Error::InvalidInput(_))));
}

#[test]
fn original_parallel_exits_and_ordinary_entry_do_not_commute_in_reverse_order() {
    let context = Context { source: parallel(), sample: vec![1, 1], global_labels: vec![1, 0] };
    let snapshot = tips(&context, &[Location::Edge(2), Location::Edge(3)], vec![true, false, true, false, true]);
    let exit2 = table(&context, &snapshot, Action::Exit(2)).transitions.remove(0).witness;
    assert_eq!(exit2.population, vec![Some(Location::Node(2)), Some(Location::Edge(3))]);
    let exit3 = table(&context, &exit2, Action::Exit(3)).transitions.remove(0).witness;
    let correct = table(&context, &exit3, Action::Ordinary(1)).transitions.remove(0).witness;
    assert_eq!(correct.population, vec![Some(Location::Edge(1)); 2]);
    let entry_first = table(&context, &snapshot, Action::Ordinary(1)).transitions.remove(0).witness;
    let reversed = table(&context, &table(&context, &entry_first, Action::Exit(2)).transitions.remove(0).witness,
        Action::Exit(3)).transitions.remove(0).witness;
    assert_eq!(reversed.population, vec![Some(Location::Node(2)); 2]);
    assert_ne!(source_epoch::selected_view(&context, &correct).unwrap(), source_epoch::selected_view(&context, &reversed).unwrap());
}

#[test]
fn original_root_entry_composes_with_the_existing_ancestral_epoch() {
    let context = Context { source: two_tip(), sample: vec![0, 1], global_labels: vec![1, 0] };
    let snapshot = tips(&context, &[Location::Node(0); 2], vec![true, false, true]);
    let entered = table(&context, &snapshot, Action::Root);
    assert_eq!(entered.transitions[0].witness.population, vec![Some(Location::Ancestral(0)); 2]);
    assert_eq!(entered.transitions[0].polynomial, Polynomial::one(0));
    let source_epoch::Decision::Table(epoch) = source_epoch::epoch_row(&context, &entered.transitions[0].witness,
        source_epoch::Limits::default()).unwrap() else { panic!("ancestral epoch limit"); };
    assert_eq!(epoch.transitions.len(), 3);
    for transition in epoch.transitions {
        assert_eq!(transition.view.register, snapshot.register);
        assert_eq!(transition.view.population, vec![Some(Location::Ancestral(0)); 2]);
        let expected = if transition.witness.live.len() == 2 { Polynomial::variable(3, 2).unwrap() }
            else { Polynomial::one(3).subtract(&Polynomial::variable(3, 2).unwrap()).unwrap().scale(&q(1, 2)) };
        assert_eq!(transition.polynomial, expected);
    }
}

#[test]
fn original_hybrid_coordinates_and_site_bits_remain_distinct_in_a_serial_source() {
    let source = Source { vertices: 7, root: 0, edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
        Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 },
        Edge { source: 4, target: 5 }, Edge { source: 4, target: 5 }, Edge { source: 5, target: 6 }],
        leaves: vec![1, 6], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }, Hybrid { vertex: 5, incoming: [5, 6] }] };
    let context = Context { source, sample: vec![1, 1], global_labels: vec![3, 1] };
    let snapshot = tips(&context, &[Location::Node(3), Location::Node(5)], vec![true, false, true, false, true, true, false]);
    let result = table(&context, &snapshot, Action::Independent(1));
    assert_eq!(result.variables, vec![0, 1]);
    for transition in result.transitions {
        assert_eq!(transition.witness.population[0], Some(Location::Node(3)));
        assert_eq!(transition.witness.register, snapshot.register);
        assert!(transition.polynomial.terms.keys().all(|powers| powers[0] == 0));
        let expected = if transition.witness.population[1] == Some(Location::Edge(6)) { q(1, 5) } else { q(4, 5) };
        assert_eq!(transition.polynomial.evaluate(&[q(1, 3), q(1, 5)]).unwrap(), expected);
    }
    let common0 = table(&context, &snapshot, Action::Common(0));
    assert_eq!(common0.transitions[0].witness.population, vec![Some(Location::Edge(2)), Some(Location::Node(5))]);
    let common1 = table(&context, &snapshot, Action::Common(1));
    assert_eq!(common1.transitions[0].witness.population, vec![Some(Location::Node(3)), Some(Location::Edge(6))]);
}
