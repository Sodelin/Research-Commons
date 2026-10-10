use parity_solver::{forest::Tree, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial, q,
    source_boundary, source_epoch, source_population::{Context, Location, Snapshot},
    source_word::{self as word, Decision, Error, Initial, LimitKind, Limits, ProviderLimits,
        Request, Stage, Symbol, Terminal, Variable}};

fn two_tip() -> Source { Source { vertices: 3, root: 0,
    edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
    leaves: vec![1, 2], hybrids: vec![] } }
fn parallel() -> Source { Source { vertices: 5, root: 0,
    edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
        Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
    leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] } }
fn start(context: &Context, places: &[Location], register: Vec<bool>) -> Snapshot {
    let snapshot = Snapshot { live: (0..places.len()).collect(), ancestor: (0..places.len()).collect(),
        genealogy: (0..places.len()).map(|copy| Some(Tree::Leaf(copy))).collect(),
        population: places.iter().copied().map(Some).collect(), register };
    context.validate_snapshot(&snapshot).unwrap(); snapshot
}
fn request(context: Context, initial: Initial, slots: usize, symbols: Vec<Symbol>, common: Vec<bool>) -> Request {
    Request { context, initial, common, slots, word: symbols, terminal: Terminal::FullView,
        limits: Limits::default(), provider_limits: ProviderLimits::default() }
}
fn table(request: &Request) -> word::Table {
    match word::word_row(request).unwrap() { Decision::Table(result) => result,
        other => panic!("unexpected {other:?}") }
}
fn ancestral_two(symbols: Vec<Symbol>, slots: usize) -> Request {
    let context = Context { source: two_tip(), sample: vec![0, 1], global_labels: vec![3, 0] };
    let snapshot = start(&context, &[Location::Ancestral(0); 2], vec![true, false, true]);
    request(context, Initial::Conditional(snapshot), slots, symbols, vec![])
}

#[test]
fn conditional_empty_word_is_full_register_identity_without_a_query() {
    let mut input = ancestral_two(vec![], 2);
    input.limits.queries = 0;
    input.limits.branches = 0;
    input.limits.term_products = 0;
    let result = table(&input);
    assert_eq!(result.variables.len(), 6);
    assert_eq!(result.transitions.len(), 1);
    let Initial::Conditional(snapshot) = &input.initial else { unreachable!() };
    assert_eq!(&result.transitions[0].witness, snapshot);
    assert_eq!(result.transitions[0].polynomial, Polynomial::one(6));
    assert_eq!(result.work, word::Work { initial_assignments: 1, initial_term_contributions: 1,
        queries: 0, branches: 0, term_products: 0, largest_row: 1, largest_terms: 1 });
}

#[test]
fn empty_natural_carrier_retains_once_drawn_hybrid_bits_even_on_repeated_common_entries() {
    let context = Context { source: parallel(), sample: vec![], global_labels: vec![] };
    let input = request(context, Initial::Natural, 0, vec![Symbol::Enter(3), Symbol::Enter(3)], vec![true]);
    let result = table(&input);
    assert_eq!(result.variables, vec![Variable::OriginalGamma(0)]);
    assert_eq!(result.transitions.len(), 2);
    assert_eq!(result.work, word::Work { initial_assignments: 2, initial_term_contributions: 3,
        queries: 4, branches: 4, term_products: 6, largest_row: 2, largest_terms: 3 });
    for transition in result.transitions {
        assert!(transition.view.genealogy.is_empty());
        assert!(transition.view.population.is_empty());
        assert!(transition.view.register.iter().enumerate().all(|(v, bit)| v == 3 || !bit));
        let expected = if transition.view.register[3] { q(1, 3) } else { q(2, 3) };
        assert_eq!(transition.polynomial.evaluate(&[q(1, 3)]).unwrap(), expected);
    }
}

#[test]
fn two_original_hybrid_initial_bits_use_distinct_coordinates_and_nine_raw_terms() {
    let source = Source { vertices: 7, root: 0,
        edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
            Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 },
            Edge { source: 4, target: 5 }, Edge { source: 4, target: 5 }, Edge { source: 5, target: 6 }],
        leaves: vec![1, 6], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }, Hybrid { vertex: 5, incoming: [5, 6] }] };
    let input = request(Context { source, sample: vec![], global_labels: vec![] }, Initial::Natural, 0, vec![], vec![true, false]);
    let result = table(&input);
    assert_eq!(result.variables, vec![Variable::OriginalGamma(0), Variable::OriginalGamma(1)]);
    assert_eq!(result.transitions.len(), 4);
    assert_eq!(result.work.initial_assignments, 4);
    assert_eq!(result.work.initial_term_contributions, 9);
    for transition in result.transitions {
        let first = if transition.view.register[3] { q(1, 3) } else { q(2, 3) };
        let second = if transition.view.register[5] { q(1, 5) } else { q(4, 5) };
        assert_eq!(transition.polynomial.evaluate(&[q(1, 3), q(1, 5)]).unwrap(), first * second);
    }
    let mut low = input;
    low.limits.initial_terms = 8;
    assert_eq!(word::word_row(&low).unwrap(), Decision::Unknown(word::Limit {
        stage: Stage::Initialization, kind: LimitKind::InitialTerms, population: None, required: 9, cap: 8 }));
}

#[test]
fn two_distinct_interval_slots_multiply_the_same_original_ancestral_survival() {
    let input = ancestral_two(vec![Symbol::Interval(0), Symbol::Interval(1)], 2);
    let result = table(&input);
    assert_eq!(result.variables[2], Variable::Survival { slot: 0, population: Location::Ancestral(0) });
    assert_eq!(result.variables[5], Variable::Survival { slot: 1, population: Location::Ancestral(0) });
    let survival = Polynomial::variable(6, 2).unwrap().multiply(&Polynomial::variable(6, 5).unwrap()).unwrap();
    assert_eq!(result.transitions.len(), 3);
    for transition in result.transitions {
        let expected = if transition.witness.live.len() == 2 { survival.clone() }
            else { Polynomial::one(6).subtract(&survival).unwrap().scale(&q(1, 2)) };
        assert_eq!(transition.polynomial, expected);
        assert_eq!(transition.witness.register, vec![true, false, true]);
        assert_eq!(transition.view, source_epoch::selected_view(&input.context, &transition.witness).unwrap());
    }
}

#[test]
fn repeated_slot_uses_one_coordinate_and_the_exact_pair_semigroup() {
    let input = ancestral_two(vec![Symbol::Interval(0), Symbol::Interval(0)], 1);
    let result = table(&input);
    let survival = Polynomial::variable(3, 2).unwrap().power(2).unwrap();
    for transition in result.transitions {
        let expected = if transition.witness.live.len() == 2 { survival.clone() }
            else { Polynomial::one(3).subtract(&survival).unwrap().scale(&q(1, 2)) };
        assert_eq!(transition.polynomial, expected);
    }
    assert_eq!(result.work, word::Work { initial_assignments: 1, initial_term_contributions: 1,
        queries: 4, branches: 8, term_products: 14, largest_row: 3, largest_terms: 5 });
}

#[test]
fn ordinary_calendar_finite_endpoint_has_the_exact_internal_pair_row() {
    let source = Source { vertices: 5, root: 0,
        edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
            Edge { source: 2, target: 3 }, Edge { source: 2, target: 4 }], leaves: vec![1, 3, 4], hybrids: vec![] };
    let input = request(Context { source, sample: vec![0, 1, 2], global_labels: vec![3, 0, 2] }, Initial::Natural, 2,
        vec![Symbol::Enter(1), Symbol::Enter(3), Symbol::Enter(4), Symbol::Interval(0),
            Symbol::Exit(2), Symbol::Exit(3), Symbol::Enter(2), Symbol::Interval(1),
            Symbol::Exit(0), Symbol::Exit(1), Symbol::Enter(0)], vec![]);
    let result = table(&input);
    assert_eq!(result.transitions.len(), 3);
    let survival = Polynomial::variable(10, 6).unwrap(); // slot1, original edge1.
    for transition in result.transitions {
        let expected = if transition.witness.live.len() == 3 { survival.clone() }
            else { Polynomial::one(10).subtract(&survival).unwrap().scale(&q(1, 2)) };
        assert_eq!(transition.polynomial, expected);
        assert_eq!(transition.view.population, vec![Some(Location::Ancestral(0)); 3]);
        assert_eq!(transition.view.register, vec![false; 5]);
        assert_eq!(transition.view.genealogy[0], Some(Tree::Leaf(0)));
    }
}

#[test]
fn natural_common_routes_both_owners_by_the_once_drawn_bit_without_a_second_gamma() {
    let input = request(Context { source: parallel(), sample: vec![1, 1], global_labels: vec![0, 1] },
        Initial::Natural, 0, vec![Symbol::Enter(4), Symbol::Exit(4), Symbol::Enter(3), Symbol::Enter(3)], vec![true]);
    let result = table(&input);
    assert_eq!(result.transitions.len(), 2);
    for transition in result.transitions {
        let bit = transition.view.register[3];
        assert_eq!(transition.view.population, vec![Some(Location::Edge(if bit { 3 } else { 2 })); 2]);
        let gamma = Polynomial::variable(1, 0).unwrap();
        let expected = if bit { gamma } else { Polynomial::one(1).subtract(&gamma).unwrap() };
        assert_eq!(transition.polynomial, expected);
        assert_eq!(transition.witness.ancestor, vec![0, 1]);
    }
}

#[test]
fn natural_independent_draw_preserves_the_independent_initial_register_in_the_joint_row() {
    let input = request(Context { source: parallel(), sample: vec![1, 1], global_labels: vec![0, 1] },
        Initial::Natural, 0, vec![Symbol::Enter(4), Symbol::Exit(4), Symbol::Enter(3)], vec![false]);
    let result = table(&input);
    assert_eq!(result.transitions.len(), 8);
    for transition in result.transitions {
        let routes = transition.view.population.iter().filter(|p| **p == Some(Location::Edge(3))).count();
        let route_probability = [q(4, 9), q(2, 9), q(1, 9)][routes].clone();
        let register_probability = if transition.view.register[3] { q(1, 3) } else { q(2, 3) };
        assert_eq!(transition.polynomial.evaluate(&[q(1, 3)]).unwrap(), route_probability * register_probability);
    }
}

#[test]
fn every_wrapper_limit_has_an_exact_boundary_and_returns_no_partial_word_row() {
    let mut input = ancestral_two(vec![Symbol::Interval(0), Symbol::Interval(0)], 1);
    input.limits = Limits { initial_assignments: 1, initial_terms: 1, queries: 4, branches: 8,
        term_products: 14, destinations: 3, terms: 5 };
    assert_eq!(table(&input).transitions.len(), 3);
    for (kind, stage, required) in [(LimitKind::InitialAssignments, Stage::Initialization, 1),
        (LimitKind::InitialTerms, Stage::Initialization, 1), (LimitKind::Queries, Stage::Letter(1), 4),
        (LimitKind::Branches, Stage::Letter(1), 8), (LimitKind::TermProducts, Stage::Letter(1), 14),
        (LimitKind::Destinations, Stage::Letter(0), 3), (LimitKind::Terms, Stage::Letter(0), 5)] {
        let mut low = input.clone();
        match kind {
            LimitKind::InitialAssignments => low.limits.initial_assignments = required - 1,
            LimitKind::InitialTerms => low.limits.initial_terms = required - 1,
            LimitKind::Queries => low.limits.queries = required - 1,
            LimitKind::Branches => low.limits.branches = required - 1,
            LimitKind::TermProducts => low.limits.term_products = required - 1,
            LimitKind::Destinations => low.limits.destinations = required - 1,
            LimitKind::Terms => low.limits.terms = required - 1,
            _ => unreachable!(),
        }
        assert_eq!(word::word_row(&low).unwrap(), Decision::Unknown(word::Limit {
            stage, kind, population: None, required, cap: required - 1 }));
    }
}

#[test]
fn per_query_epoch_and_boundary_refusals_keep_the_original_provider_limits() {
    let mut input = ancestral_two(vec![Symbol::Interval(0)], 1);
    input.provider_limits.epoch.calls = 0;
    assert_eq!(word::word_row(&input).unwrap(), Decision::Unknown(word::Limit { stage: Stage::Letter(0),
        kind: LimitKind::Epoch(source_epoch::LimitKind::Calls), population: Some(Location::Edge(0)), required: 1, cap: 0 }));
    let context = Context { source: parallel(), sample: vec![1, 1], global_labels: vec![0, 1] };
    let snapshot = start(&context, &[Location::Node(3); 2], vec![true, false, true, true, true]);
    let mut input = request(context, Initial::Conditional(snapshot), 0, vec![Symbol::Enter(3)], vec![false]);
    input.provider_limits.boundary.assignments = 0;
    assert_eq!(word::word_row(&input).unwrap(), Decision::Unknown(word::Limit { stage: Stage::Letter(0),
        kind: LimitKind::Boundary(source_boundary::LimitKind::Assignments), population: None, required: 4, cap: 0 }));
}

#[test]
fn all_input_checks_precede_work_limits_and_completion_is_explicitly_unsupported() {
    let mut input = ancestral_two(vec![Symbol::Interval(0), Symbol::Exit(999)], 1);
    input.limits.queries = 0;
    assert_eq!(word::word_row(&input), Err(Error::InvalidInput("SOURCE_WORD_EDGE")));
    input.word = vec![Symbol::Interval(1)];
    assert_eq!(word::word_row(&input), Err(Error::InvalidInput("SOURCE_WORD_SLOT")));
    input.word = vec![];
    input.common = vec![true];
    assert_eq!(word::word_row(&input), Err(Error::InvalidInput("SOURCE_WORD_MODE_REGISTRY")));
    input.common.clear();
    input.slots = 17;
    assert_eq!(word::word_row(&input), Err(Error::InvalidInput("SOURCE_WORD_INPUT_CAP")));
    input.slots = 1;
    input.word = vec![Symbol::Enter(0); 33];
    assert_eq!(word::word_row(&input), Err(Error::InvalidInput("SOURCE_WORD_INPUT_CAP")));
    input.word.clear();
    input.terminal = Terminal::AncestralComplete;
    assert_eq!(word::word_row(&input), Err(Error::Unsupported("SOURCE_WORD_ANCESTRAL_COMPLETION_NOT_EXTRACTED")));
    if let Initial::Conditional(snapshot) = &mut input.initial { snapshot.ancestor[0] = 999; }
    assert!(matches!(word::word_row(&input), Err(Error::InvalidInput(_))));
}
