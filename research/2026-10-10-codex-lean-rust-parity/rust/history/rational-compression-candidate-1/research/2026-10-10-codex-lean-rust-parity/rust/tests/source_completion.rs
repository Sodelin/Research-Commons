use parity_solver::{forest::Tree, natural_cell::{Edge, Source}, q, source_completion as completion,
    source_epoch, source_population::{Context, Location, Snapshot, Limits, LimitKind}};

fn context(copies: usize) -> Context {
    Context { source: Source { vertices: 3, root: 0,
        edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
        leaves: vec![1, 2], hybrids: vec![] }, sample: (0..copies).map(|i| i % 2).collect(),
        global_labels: (0..copies).collect() }
}
fn singleton_start(context: &Context) -> Snapshot {
    let n = context.sample.len();
    Snapshot { live: (0..n).collect(), ancestor: (0..n).collect(),
        genealogy: (0..n).map(|copy| Some(Tree::Leaf(copy))).collect(),
        population: vec![Some(Location::Ancestral(0)); n], register: vec![true, false, true] }
}
fn table(context: &Context, snapshot: &Snapshot, limits: Limits) -> completion::Table {
    match completion::completion_row(context, snapshot, limits).unwrap() {
        completion::Decision::Table(table) => table, other => panic!("unexpected {other:?}"),
    }
}

#[test]
fn constant_term_gives_every_ordered_complete_tree_and_exact_ranked_history_weights() {
    // Each literal ordered choice has weight 1/(k*(k-1)). Four-tip balanced
    // trees have two ranked histories; the other shapes have exactly one.
    for (copies, expected_rows) in [(1, 1), (2, 2), (3, 12), (4, 120)] {
        let context = context(copies);
        let entering = singleton_start(&context);
        let result = table(&context, &entering, Limits::default());
        assert_eq!(result.transitions.len(), expected_rows);
        assert_eq!(result.population, Location::Ancestral(0));
        let mut balanced = 0;
        let mut mass = q(0, 1);
        for transition in result.transitions {
            let witness = &transition.witness;
            assert_eq!(witness.live.len(), 1);
            assert!(witness.ancestor.iter().all(|owner| *owner == witness.live[0]));
            assert_eq!(witness.register, entering.register);
            assert_eq!(transition.view, source_epoch::selected_view(&context, witness).unwrap());
            assert_eq!(transition.view.population, vec![Some(Location::Ancestral(0)); copies]);
            let tree = witness.genealogy[witness.live[0]].as_ref().unwrap();
            let is_balanced = matches!(tree, Tree::Node(left, right)
                if matches!(left.as_ref(), Tree::Node(_, _)) && matches!(right.as_ref(), Tree::Node(_, _)));
            let expected = match copies { 1 => q(1, 1), 2 => q(1, 2), 3 => q(1, 12),
                4 if is_balanced => { balanced += 1; q(1, 72) }, 4 => q(1, 144), _ => unreachable!() };
            assert_eq!(transition.weight, expected);
            mass += transition.weight;
        }
        assert_eq!(mass, q(1, 1));
        if copies == 4 { assert_eq!(balanced, 24); }
    }
}

#[test]
fn carried_nonminimum_representative_is_one_owner_coin_and_retains_both_graft_orientations() {
    let mut context = context(4);
    context.sample = vec![0, 0, 0, 1];
    let carried = Tree::Node(Box::new(Tree::Node(Box::new(Tree::Leaf(0)), Box::new(Tree::Leaf(1)))),
        Box::new(Tree::Leaf(2)));
    let entering = Snapshot { live: vec![2, 3], ancestor: vec![2, 2, 2, 3],
        genealogy: vec![None, None, Some(carried.clone()), Some(Tree::Leaf(3))],
        population: vec![None, None, Some(Location::Ancestral(0)), Some(Location::Ancestral(0))],
        register: vec![true, false, true] };
    let result = table(&context, &entering, Limits::default());
    assert_eq!(result.transitions.len(), 2);
    for transition in result.transitions {
        assert_eq!(transition.weight, q(1, 2));
        let owner = transition.witness.live[0];
        let expected = match owner {
            2 => Tree::Node(Box::new(carried.clone()), Box::new(Tree::Leaf(3))),
            3 => Tree::Node(Box::new(Tree::Leaf(3)), Box::new(carried.clone())),
            _ => panic!("retained representative changed to a dead copy"),
        };
        assert_eq!(transition.witness.genealogy[owner], Some(expected));
        assert_eq!(transition.witness.register, entering.register);
    }
}

#[test]
fn original_provider_limits_bound_the_full_polynomial_before_constant_filtering() {
    let context = context(2);
    let entering = singleton_start(&context);
    let exact = Limits { calls: 3, destinations: 3, lifted_terms: 4 };
    let result = table(&context, &entering, exact);
    assert_eq!(result.work.calls, 3);
    assert_eq!(result.work.lifted_terms, 4);
    assert_eq!(result.work.largest_row, 3);
    assert_eq!(result.transitions.len(), 2);
    for (kind, required) in [(LimitKind::Calls, 3), (LimitKind::Destinations, 3), (LimitKind::LiftedTerms, 4)] {
        let mut low = exact;
        match kind { LimitKind::Calls => low.calls = required - 1,
            LimitKind::Destinations => low.destinations = required - 1,
            LimitKind::LiftedTerms => low.lifted_terms = required - 1 }
        assert_eq!(completion::completion_row(&context, &entering, low).unwrap(),
            completion::Decision::Unknown(parity_solver::source_population::Limit {
                kind, required, cap: required - 1 }));
    }
}

#[test]
fn empty_and_nonroot_carriers_are_refused_before_zero_provider_caps() {
    let empty = context(0);
    let zero = Limits { calls: 0, destinations: 0, lifted_terms: 0 };
    assert_eq!(completion::completion_row(&empty, &singleton_start(&empty), zero),
        Err(completion::Error::InvalidInput("SOURCE_WORD_COMPLETION_EMPTY_COPY")));
    let context = context(2);
    let mut mixed = singleton_start(&context);
    mixed.population[1] = Some(Location::Edge(1));
    context.validate_snapshot(&mixed).unwrap();
    assert_eq!(completion::completion_row(&context, &mixed, zero),
        Err(completion::Error::InvalidInput("SOURCE_WORD_COMPLETION_ROOT_SUPPORT")));
}

#[test]
fn global_label_permutation_changes_only_readout_metadata_and_every_register_bit_is_retained() {
    let context = context(4);
    let mut permuted = context.clone();
    permuted.global_labels = vec![3, 0, 2, 1];
    let entering = singleton_start(&context);
    let first = table(&context, &entering, Limits::default());
    assert_eq!(table(&permuted, &entering, Limits::default()), first);
    let mut other_register = entering;
    other_register.register = vec![false, true, false];
    let second = table(&context, &other_register, Limits::default());
    for (a, b) in first.transitions.iter().zip(second.transitions) {
        assert_eq!(a.weight, b.weight);
        assert_eq!(a.view.genealogy, b.view.genealogy);
        assert_eq!(b.view.register, other_register.register);
        assert_eq!(b.witness.register, other_register.register);
    }
}
