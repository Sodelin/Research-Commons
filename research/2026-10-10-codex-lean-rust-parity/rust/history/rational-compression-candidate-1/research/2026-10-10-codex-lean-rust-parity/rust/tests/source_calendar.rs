use parity_solver::{q, Rational, natural_cell::{Edge, Source}, source_calendar as calendar,
    source_epoch, source_population::{Context, Location}, source_word as word};
use num_bigint::BigInt;

fn request() -> calendar::Request {
    calendar::Request { context: Context { source: Source { vertices: 3, root: 0,
        edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 }],
        leaves: vec![1, 2], hybrids: vec![] }, sample: vec![0, 1], global_labels: vec![3, 0] },
        ages: vec![q(2, 1), q(0, 1), q(0, 1)], inverse_rates: vec![q(1, 1), q(2, 1), q(3, 2)],
        original_gamma: vec![], common: vec![], terminal: word::Terminal::FullView,
        compiler_limits: calendar::CompilerLimits::default(), word_limits: word::Limits::default(),
        provider_limits: word::ProviderLimits::default() }
}
fn generated(input: &calendar::Request) -> calendar::Generated {
    match calendar::compile_calendar(input).unwrap() { calendar::CompileDecision::Generated(g) => g,
        other => panic!("unexpected {other:?}") }
}

#[test]
fn exact_two_tip_agenda_uses_all_ids_and_one_shared_inverse_bank() {
    let input = request();
    let result = generated(&input);
    assert_eq!(result.requirements, calendar::Requirements { word_length: 6, slots: 1, variables: 3 });
    assert_eq!(result.agenda.word, vec![word::Symbol::Enter(1), word::Symbol::Enter(2),
        word::Symbol::Interval(0), word::Symbol::Exit(0), word::Symbol::Exit(1), word::Symbol::Enter(0)]);
    assert_eq!(result.agenda.dates, vec![q(0, 1), q(2, 1)]);
    assert_eq!(result.agenda.slots[0], calendar::Slot { slot: 0, word_position: 2,
        younger_date: q(0, 1), older_date: q(2, 1), duration: q(2, 1) });
    assert_eq!(result.agenda.physical_coordinates.iter().map(|c| c.argument.clone()).collect::<Vec<_>>(),
        vec![q(2, 1), q(1, 1), q(4, 3)]);
    assert!(result.agenda.leaf_age_zero);
    assert_eq!(result.child.initial, word::Initial::Natural);
    assert_eq!(result.child.context, input.context);
    assert_eq!(result.child.provider_limits, input.provider_limits);
    assert_eq!(result.child.limits, input.word_limits);
}

#[test]
fn simultaneous_internal_cohort_preserves_exit_before_enter() {
    let mut input = request();
    input.context = Context { source: Source { vertices: 7, root: 0,
        edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
            Edge { source: 1, target: 3 }, Edge { source: 1, target: 4 },
            Edge { source: 2, target: 5 }, Edge { source: 2, target: 6 }],
        leaves: vec![3, 4, 5, 6], hybrids: vec![] }, sample: vec![0, 3], global_labels: vec![0, 1] };
    input.ages = vec![q(2, 1), q(1, 1), q(1, 1), q(0, 1), q(0, 1), q(0, 1), q(0, 1)];
    input.inverse_rates = vec![q(1, 1); 7];
    let result = generated(&input);
    assert_eq!(result.agenda.cohorts[1], calendar::Cohort { date_index: 1, representative: 1,
        vertices: vec![1, 2], exits: vec![2, 3, 4, 5] });
    assert_eq!(&result.agenda.word[4..11], &[word::Symbol::Interval(0), word::Symbol::Exit(2),
        word::Symbol::Exit(3), word::Symbol::Exit(4), word::Symbol::Exit(5),
        word::Symbol::Enter(1), word::Symbol::Enter(2)]);
    assert_eq!(result.agenda.slots.len(), 2);
    assert_eq!(result.agenda.origins[4], calendar::Origin { date_index: 1,
        phase: calendar::Phase::Interval, index: 0 });
}

#[test]
fn serial_negative_tip_ages_remain_absolute_and_need_no_leading_interval() {
    let mut input = request();
    input.ages = vec![q(3, 1), q(-2, 1), q(-1, 2)];
    let result = generated(&input);
    assert_eq!(result.agenda.dates, vec![q(-2, 1), q(-1, 2), q(3, 1)]);
    assert_eq!(result.agenda.word, vec![word::Symbol::Enter(1), word::Symbol::Interval(0),
        word::Symbol::Enter(2), word::Symbol::Interval(1), word::Symbol::Exit(0),
        word::Symbol::Exit(1), word::Symbol::Enter(0)]);
    assert_eq!(result.agenda.slots.iter().map(|s| s.duration.clone()).collect::<Vec<_>>(),
        vec![q(3, 2), q(7, 2)]);
    assert!(!result.agenda.leaf_age_zero);
    assert_eq!(result.agenda.physical_coordinates[3].argument, q(7, 2));
    assert_eq!(result.agenda.physical_coordinates[4].argument, q(7, 4));
}

#[test]
fn exact_exposure_arithmetic_has_no_hidden_input_bit_limit() {
    let mut input = request();
    let two300 = BigInt::from(1u8) << 300usize;
    let two500 = BigInt::from(1u8) << 500usize;
    input.ages[0] = Rational::from_integer(two300.clone());
    input.inverse_rates[0] = Rational::new(BigInt::from(1u8), two500.clone());
    let result = generated(&input);
    assert_eq!(result.agenda.physical_coordinates[0].argument, Rational::from_integer(two300 * two500));
    assert_eq!(result.agenda.physical_coordinates[0].argument.numer().bits(), 801);
}

#[test]
fn malformed_bank_and_edge_inequalities_precede_all_compiler_caps() {
    let mut input = request();
    input.compiler_limits = calendar::CompilerLimits { word_length: 0, slots: 0, variables: 0 };
    input.inverse_rates[0] = q(0, 1);
    assert_eq!(calendar::compile_calendar(&input), Err(calendar::Error::InvalidInput("SOURCE_CALENDAR_INVERSE_RATE")));
    input.inverse_rates[0] = q(1, 1);
    input.ages[1] = input.ages[0].clone();
    assert_eq!(calendar::compile_calendar(&input), Err(calendar::Error::InvalidInput("SOURCE_CALENDAR_STRICT_EDGE")));
}

#[test]
fn dimensions_and_noncanonical_unchecked_ratios_are_rejected() {
    let mut input = request();
    input.common.push(false);
    assert_eq!(calendar::compile_calendar(&input), Err(calendar::Error::InvalidInput("SOURCE_CALENDAR_DIMENSIONS")));
    input.common.clear();
    input.inverse_rates[0] = Rational::new_raw(2.into(), 4.into());
    assert_eq!(calendar::compile_calendar(&input), Err(calendar::Error::InvalidInput("SOURCE_CALENDAR_INPUT")));
    input.inverse_rates[0] = Rational::new_raw(1.into(), 0.into());
    assert_eq!(calendar::compile_calendar(&input), Err(calendar::Error::InvalidInput("SOURCE_CALENDAR_INPUT")));
}

#[test]
fn compiler_limits_use_exact_counts_and_agreed_priority() {
    let mut input = request();
    input.compiler_limits = calendar::CompilerLimits { word_length: 0, slots: 0, variables: 0 };
    let unknown = match calendar::compile_calendar(&input).unwrap() {
        calendar::CompileDecision::Unknown(limit) => limit, other => panic!("unexpected {other:?}") };
    assert_eq!(unknown.limit, calendar::CompilerLimit { kind: calendar::CompilerLimitKind::WordLength,
        required: 6, cap: 0 });
    input.compiler_limits.word_length = 6;
    let calendar::CompileDecision::Unknown(unknown) = calendar::compile_calendar(&input).unwrap() else { panic!() };
    assert_eq!(unknown.limit.kind, calendar::CompilerLimitKind::Slots);
    input.compiler_limits.slots = 1;
    let calendar::CompileDecision::Unknown(unknown) = calendar::compile_calendar(&input).unwrap() else { panic!() };
    assert_eq!(unknown.limit.kind, calendar::CompilerLimitKind::Variables);
    input.compiler_limits.variables = 3;
    assert_eq!(generated(&input).requirements, calendar::Requirements { word_length: 6, slots: 1, variables: 3 });
    input.compiler_limits.word_length = 33;
    assert_eq!(calendar::compile_calendar(&input), Err(calendar::Error::InvalidInput("SOURCE_CALENDAR_LIMITS")));
}

#[test]
fn valid_fifteen_vertex_calendar_is_operationally_unknown_at_forty_three_letters() {
    let mut input = request();
    input.context = Context { source: Source { vertices: 15, root: 0,
        edges: (1..15).map(|target| Edge { source: (target - 1) / 2, target }).collect(),
        leaves: (7..15).collect(), hybrids: vec![] }, sample: vec![0], global_labels: vec![0] };
    input.ages = (0..15).map(|vertex| q(14 - vertex, 1)).collect();
    input.inverse_rates = vec![q(1, 1); 15];
    input.context.validate().unwrap();
    let calendar::Decision::CompilerUnknown(unknown) = calendar::calendar_row(&input).unwrap() else { panic!() };
    assert_eq!(unknown.requirements, calendar::Requirements { word_length: 43, slots: 14, variables: 210 });
    assert_eq!(unknown.limit, calendar::CompilerLimit { kind: calendar::CompilerLimitKind::WordLength,
        required: 43, cap: 32 });
}

#[test]
fn unchanged_word_unknown_retains_stage_and_original_population() {
    let mut input = request();
    input.provider_limits.epoch.calls = 0;
    let calendar::Decision::WordUnknown { generated, limit } = calendar::calendar_row(&input).unwrap() else { panic!() };
    assert_eq!(generated.agenda.slots.len(), 1);
    assert_eq!(limit.stage, word::Stage::Letter(2));
    assert_eq!(limit.population, Some(Location::Edge(0)));
    assert_eq!(limit.required, 1);
    assert_eq!(limit.cap, 0);
    input.word_limits.queries = 0;
    let calendar::Decision::WordUnknown { limit, .. } = calendar::calendar_row(&input).unwrap() else { panic!() };
    assert_eq!(limit.kind, word::LimitKind::Queries);
    assert_eq!(limit.population, None);
}

#[test]
fn natural_calendar_completes_both_original_copies_with_range_witnesses() {
    let mut input = request();
    input.terminal = word::Terminal::AncestralComplete;
    let calendar::Decision::Table { generated, table } = calendar::calendar_row(&input).unwrap() else { panic!() };
    assert_eq!(table.transitions.len(), 2);
    assert_eq!(table.variables.len(), generated.requirements.variables);
    for row in table.transitions {
        assert_eq!(row.view.population, vec![Some(Location::Ancestral(0)); 2]);
        assert_eq!(row.view.register, vec![false; 3]);
        assert_eq!(source_epoch::selected_view(&input.context, &row.witness).unwrap(), row.view);
        assert_eq!(row.polynomial.terms.values().collect::<Vec<_>>(), vec![&q(1, 2)]);
    }
}

#[test]
fn empty_completion_is_refused_before_zero_compiler_caps() {
    let mut input = request();
    input.context.sample.clear(); input.context.global_labels.clear();
    input.terminal = word::Terminal::AncestralComplete;
    input.compiler_limits = calendar::CompilerLimits { word_length: 0, slots: 0, variables: 0 };
    assert_eq!(calendar::calendar_row(&input), Err(calendar::Error::InvalidInput("SOURCE_WORD_COMPLETION_EMPTY_COPY")));
    input.terminal = word::Terminal::FullView;
    assert!(matches!(calendar::calendar_row(&input), Ok(calendar::Decision::CompilerUnknown(_))));
}
