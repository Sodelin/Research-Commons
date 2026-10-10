use parity_solver::{affine::{self, Decision}, natural_cell::{self as c, AgeAtom, AgeConstraint, Chart, Comparison, Edge, Exposure, Hybrid, Interval, Population, Source}, protocol, q};

const ORDINARY: &str = "RC1 CHART 3 2 2 0 0 2 4096\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nLEAF 0 1\nLEAF 1 2\nEXPOSURE 0 E:0 V:1 V:0 LE:1/1 LE:4/1\nEXPOSURE 1 E:1 V:2 V:0 LE:1/1 LE:4/1\n";
const PARALLEL: &str = "RC1 CHART 5 5 2 1 0 0 4096\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nEDGE 2 2 3\nEDGE 3 2 3\nEDGE 4 3 4\nLEAF 0 1\nLEAF 1 4\nHYBRID 0 3 2 3\nCOIN 0 NONE NONE\n";

#[test]
fn canonical_two_tip_compiler_and_literal_bank() {
    let protocol::Request::Chart(chart) = protocol::parse(ORDINARY.as_bytes()).unwrap() else { panic!() };
    let compiled = c::compile(&chart).unwrap();
    assert_eq!(compiled.dimension, 6);
    assert_eq!(compiled.rows.len(), 13);
    assert_eq!(compiled.bank_names, ["AGE:0", "AGE:1", "AGE:2", "RATE:0", "RATE:1", "RATE:A"]);
    // First shared edge lower exposure is u0 <= root-tip0, not a row-local u.
    assert_eq!(compiled.rows[9].coefficients, vec![q(-1, 1), q(1, 1), q(0, 1), q(1, 1), q(0, 1), q(0, 1)]);
    assert_eq!(compiled.rows[10].coefficients, vec![q(1, 1), q(-1, 1), q(0, 1), q(-4, 1), q(0, 1), q(0, 1)]);
    let Decision::Witness(bank) = affine::solve(6, &compiled.rows, chart.cap).unwrap() else { panic!() };
    assert!(c::check_bank(&chart, &bank));
    let result = protocol::execute(ORDINARY.as_bytes());
    assert_eq!(result.exit_code, 0);
    assert!(result.bytes.contains("GATE SOURCE_ADMISSION_NOT_ESTABLISHED\nSTATUS SAT\n"));
    assert_eq!(protocol::check(ORDINARY.as_bytes(), result.bytes.as_bytes()), Ok(()));
}

#[test]
fn parallel_edge_occurrences_and_coins_remain_distinct() {
    let protocol::Request::Chart(chart) = protocol::parse(PARALLEL.as_bytes()).unwrap() else { panic!() };
    assert_eq!(chart.source.edges[2], chart.source.edges[3]);
    assert_ne!(chart.source.population_index(Population::Edge(2)), chart.source.population_index(Population::Edge(3)));
    let result = protocol::execute(PARALLEL.as_bytes());
    assert_eq!(result.exit_code, 0);
    assert!(result.bytes.contains("BANK 12 AGE:0 AGE:1 AGE:2 AGE:3 AGE:4 RATE:0 RATE:1 RATE:2 RATE:3 RATE:4 RATE:A COIN:0\n"));
    assert_eq!(protocol::check(PARALLEL.as_bytes(), result.bytes.as_bytes()), Ok(()));
    let protocol::Request::Chart(chart) = protocol::parse(PARALLEL.as_bytes()).unwrap() else { panic!() };
    let compiled = c::compile(&chart).unwrap();
    let Decision::Witness(bank) = affine::solve(12, &compiled.rows, 4096).unwrap() else { panic!() };
    assert!(c::check_bank(&chart, &bank));
    assert_eq!(bank[11], q(1, 2));
}

#[test]
fn graph_admission_rejects_bad_parent_ids_degree_and_lsa() {
    for bad in [PARALLEL.replace("HYBRID 0 3 2 3", "HYBRID 0 3 2 2"),
        PARALLEL.replace("HYBRID 0 3 2 3", "HYBRID 0 3 1 3"),
        PARALLEL.replace("LEAF 1 4", "LEAF 1 1"),
        PARALLEL.replace("EDGE 3 2 3", "EDGE 3 3 2"),
        ORDINARY.replace("EDGE 1 0 2", "EDGE 1 1 2")] {
        assert_eq!(protocol::execute(bad.as_bytes()).bytes, protocol::INVALID);
    }
    // Binary rooted DAG where a nonroot hybrid dominates *all* leaves: the
    // source LSA predicate is essential even though the degrees are correct.
    // A clearer legal-degree failing LSA source is root parallel->hybrid->tree
    // with two tips; every tip path contains the same nonroot hybrid.
    let graph = Source { vertices: 5, root: 0,
        edges: vec![Edge{source:0,target:1},Edge{source:0,target:1},Edge{source:1,target:2},
                    Edge{source:2,target:3},Edge{source:2,target:4}],
        leaves:vec![3,4],hybrids:vec![Hybrid{vertex:1,incoming:[0,1]}] };
    assert_eq!(graph.validate(), Err("SOURCE_LEAST_STABLE"));
}

#[test]
fn all_source_exposures_share_one_inverse_rate() {
    let protocol::Request::Chart(mut chart) = protocol::parse(ORDINARY.as_bytes()).unwrap() else { panic!() };
    chart.exposures = vec![Exposure { population: Population::Edge(0), younger: AgeAtom::Node(1), older: AgeAtom::Node(0),
        interval: Interval {lower:Some(c::Bound{value:q(1,1),strict:false}),upper:Some(c::Bound{value:q(1,1),strict:false})}},
        Exposure { population: Population::Edge(0), younger: AgeAtom::Node(1), older: AgeAtom::Node(0),
        interval: Interval {lower:Some(c::Bound{value:q(2,1),strict:false}),upper:Some(c::Bound{value:q(2,1),strict:false})}}];
    let compiled = c::compile(&chart).unwrap();
    let Decision::Exclusion(weights) = affine::solve(compiled.dimension, &compiled.rows, 4096).unwrap() else { panic!() };
    assert!(affine::check_exclusion(6, &compiled.rows, &weights));
    // Independent fits are possible for each row, proving why duplicating the
    // edge population register would invalidate this joint exclusion.
    for exposure in chart.exposures.clone() {
        let one = Chart { exposures:vec![exposure], ..chart.clone() };
        let compiled = c::compile(&one).unwrap();
        assert!(matches!(affine::solve(6, &compiled.rows,4096),Ok(Decision::Witness(_))));
    }
}

#[test]
fn chart_chronology_strict_boundary_and_canonical_controls() {
    let protocol::Request::Chart(mut chart) = protocol::parse(ORDINARY.as_bytes()).unwrap() else { panic!() };
    chart.chronology.push(AgeConstraint { kind:Comparison::Equal, left:AgeAtom::Node(0), right:AgeAtom::Fixed(q(0,1)) });
    let compiled = c::compile(&chart).unwrap();
    assert!(matches!(affine::solve(6, &compiled.rows,4096),Ok(Decision::Exclusion(_))));
    for bad in [ORDINARY.replace("EDGE 0", "EDGE 1"), ORDINARY.replace("LEAF 0", "LEAF 01"),
        ORDINARY.replace("E:0", "E:2"), ORDINARY.replace("V:1", "V:3"),
        ORDINARY.replace("LE:1/1", "LE:2/2"), ORDINARY.replace("LE:1/1", "LT:+1/1"),
        ORDINARY.replace("ROOT 0", "ROOT 1"), ORDINARY.replace("3 2 2 0 0 2", "3 2 2 0 33 2")] {
        assert_eq!(protocol::execute(bad.as_bytes()).bytes, protocol::INVALID);
    }
    let result = protocol::execute(ORDINARY.replace("4096", "0").as_bytes());
    assert_eq!(result.exit_code,2);
    assert!(result.bytes.contains("STATUS UNKNOWN\n"));
}

#[test]
fn compiled_matrix_and_gate_are_certificate_identity() {
    let result = protocol::execute(ORDINARY.as_bytes());
    let altered = result.bytes.replacen("MATRIX 6 13 4096", "MATRIX 6 12 4096", 1);
    assert_eq!(protocol::check(ORDINARY.as_bytes(), altered.as_bytes()), Err("REQUEST_OR_MATRIX_IDENTITY"));
    let altered = result.bytes.replace("GATE SOURCE_ADMISSION_NOT_ESTABLISHED", "GATE SOURCE_ADMITTED");
    assert_eq!(protocol::check(ORDINARY.as_bytes(), altered.as_bytes()), Err("REQUEST_OR_MATRIX_IDENTITY"));
}
