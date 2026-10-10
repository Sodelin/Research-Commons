use parity_solver::{affine::{self, Decision, Row}, canonical, count, forest::{self, Tree}, protocol, q};

fn row(a: &[i64], bound: i64, strict: bool) -> Row {
    Row { coefficients: a.iter().map(|a| q(*a, 1)).collect(), bound: q(bound, 1), strict }
}

#[test]
fn empty_and_zero_dimensional_cases() {
    assert_eq!(affine::solve(0, &[], 0).unwrap(), Decision::Witness(vec![]));
    assert_eq!(affine::solve(3, &[], 0).unwrap(), Decision::Witness(vec![q(0, 1); 3]));
    assert_eq!(affine::solve(0, &[row(&[], 0, false)], 0).unwrap(), Decision::Witness(vec![]));
    let rows = [row(&[], 0, true)];
    assert_eq!(affine::solve(0, &rows, 0).unwrap(), Decision::Exclusion(vec![q(1, 1)]));
    assert!(affine::check_exclusion(0, &rows, &[q(1, 1)]));
}

#[test]
fn open_endpoint_and_singleton_boundary() {
    let weak = [row(&[-1], 0, false), row(&[1], 0, false)];
    assert_eq!(affine::solve(1, &weak, 1).unwrap(), Decision::Witness(vec![q(0, 1)]));
    let strict = [row(&[-1], 0, true), row(&[1], 0, false)];
    assert_eq!(affine::solve(1, &strict, 1).unwrap(), Decision::Exclusion(vec![q(1, 1); 2]));
    assert!(!affine::check_witness(1, &strict, &[q(0, 1)]));
    assert!(!affine::check_exclusion(1, &weak, &vec![q(1, 1); 2]));
}

#[test]
fn deterministic_endpoint_reconstruction() {
    let interval = [row(&[-1], -2, true), row(&[1], 3, true)];
    assert_eq!(affine::solve(1, &interval, 1).unwrap(), Decision::Witness(vec![q(5, 2)]));
    assert_eq!(affine::solve(1, &[row(&[-1], -2, false)], 0).unwrap(), Decision::Witness(vec![q(3, 1)]));
    assert_eq!(affine::solve(1, &[row(&[1], 3, false)], 0).unwrap(), Decision::Witness(vec![q(2, 1)]));
}

#[test]
fn all_rows_share_the_same_parameters() {
    // Each constraint separately has a solution; their shared x=y=1 and x+y<2
    // system has none. Independent row fitting would incorrectly admit it.
    let rows = [row(&[1, 0], 1, false), row(&[-1, 0], -1, false),
        row(&[0, 1], 1, false), row(&[0, -1], -1, false), row(&[1, 1], 2, true)];
    let Decision::Exclusion(weights) = affine::solve(2, &rows, 64).unwrap() else { panic!() };
    assert!(affine::check_exclusion(2, &rows, &weights));
    assert!(!affine::check_witness(2, &rows, &[q(1, 1), q(1, 1)]));
    assert!(rows.iter().all(|r| matches!(affine::solve(2, &[r.clone()], 64), Ok(Decision::Witness(_)))));
}

#[test]
fn coupled_witness_and_nonnegative_derivation() {
    // 0<x<1, x<y<2x gives x=1/2 and y=3/4 under final-variable projection.
    let rows = [row(&[-1, 0], 0, true), row(&[1, 0], 1, true),
        row(&[1, -1], 0, true), row(&[-2, 1], 0, true)];
    let Decision::Witness(x) = affine::solve(2, &rows, 16).unwrap() else { panic!() };
    assert_eq!(x, vec![q(1, 2), q(3, 4)]);
    assert!(affine::check_witness(2, &rows, &x));
    let bad = [row(&[2], -2, false), row(&[-3], 0, false)];
    assert_eq!(affine::solve(1, &bad, 1).unwrap(), Decision::Exclusion(vec![q(3, 1), q(2, 1)]));
}

#[test]
fn projection_cap_is_not_exclusion() {
    let rows = [row(&[-1], 0, false), row(&[1], 1, false)];
    assert_eq!(affine::solve(1, &rows, 0).unwrap(),
        Decision::Unknown { dimension: 1, required_rows: 1, cap: 0 });
    assert!(matches!(affine::solve(1, &rows, 1), Ok(Decision::Witness(_))));
    assert!(!affine::check_exclusion(1, &rows, &vec![q(0, 1); 2]));
}

#[test]
fn zero_weight_strict_row_cannot_supply_a_strict_contradiction() {
    let rows = [row(&[1], 0, false), row(&[-1], 0, false), row(&[0], 1, true)];
    assert!(!affine::check_exclusion(1, &rows, &[q(1, 1), q(1, 1), q(0, 1)]));
    assert!(!affine::check_exclusion(1, &rows, &[q(-1, 1), q(-1, 1), q(0, 1)]));
}

#[test]
fn exact_protocol_certificate_and_request_binding() {
    let request = b"RC1 AFFINE 1 2 1\nLT 0/1 -1/1\nLT 1/1 1/1\n";
    let result = protocol::execute(request);
    assert_eq!(result.bytes, "RC1 RESULT AFFINE\nBEGIN_REQUEST\nRC1 AFFINE 1 2 1\nLT 0/1 -1/1\nLT 1/1 1/1\nEND_REQUEST\nSTATUS SAT\nWITNESS 1 1/2\nEVAL 2 -1/2 1/2\nEND\n");
    assert_eq!(protocol::check(request, result.bytes.as_bytes()), Ok(()));
    let other = b"RC1 AFFINE 1 2 1\nLT -1/1 -1/1\nLT 2/1 1/1\n";
    assert_eq!(protocol::check(other, result.bytes.as_bytes()), Err("REQUEST_IDENTITY"));
    let altered = result.bytes.replace("WITNESS 1 1/2", "WITNESS 1 0/1");
    assert_eq!(protocol::check(request, altered.as_bytes()), Err("INVALID_WITNESS"));
    let altered = result.bytes.replace("EVAL 2 -1/2 1/2", "EVAL 2 0/1 1/2");
    assert_eq!(protocol::check(request, altered.as_bytes()), Err("INVALID_EVALUATION"));
}

#[test]
fn exact_unsat_certificate_and_tampered_multipliers() {
    let request = b"RC1 AFFINE 1 2 1\nLT 0/1 -1/1\nLE 0/1 1/1\n";
    let result = protocol::execute(request);
    assert_eq!(protocol::check(request, result.bytes.as_bytes()), Ok(()));
    let altered = result.bytes.replace("MULTIPLIERS 2 1/1 1/1", "MULTIPLIERS 2 0/1 0/1");
    assert_eq!(protocol::check(request, altered.as_bytes()), Err("INVALID_EXCLUSION"));
    let altered = result.bytes.replace("STRICT 1", "STRICT 0");
    assert_eq!(protocol::check(request, altered.as_bytes()), Err("INVALID_DERIVATION"));
}

#[test]
fn strict_transport_and_input_caps() {
    for request in ["RC1 AFFINE 01 0 0\n", "RC1 AFFINE 9 0 0\n", "RC1 AFFINE 0 65 0\n",
        "RC1 AFFINE 0 0 4097\n", "RC1 AFFINE 0 1 0\nLE 0\n", "RC1 AFFINE 0 1 0\nLE -0/1\n",
        "RC1 AFFINE 0 1 0\nLE 2/2\n", "RC1 AFFINE 0 1 0\nLE 0/2\n",
        "RC1 AFFINE 0 1 0\nLE +1/1\n", "RC1 AFFINE 0 1 0\nLE 1/-1\n",
        "RC1 AFFINE 0 0 0\r\n", "RC1 AFFINE 0 0 0", "RC1 AFFINE 0 0 0\n\n",
        "RC1\tAFFINE 0 0 0\n", "RC1  AFFINE 0 0 0\n"] {
        assert_eq!(protocol::execute(request.as_bytes()).bytes, protocol::INVALID, "{request:?}");
    }
    let largest = ((num_bigint::BigInt::from(1) << 256usize) - 1u8).to_string();
    assert!(protocol::rational(&format!("{largest}/1"), true).is_ok());
    let too_large = (num_bigint::BigInt::from(1) << 256usize).to_string();
    assert!(protocol::rational(&format!("{too_large}/1"), true).is_err());
}

#[test]
fn conditional_count_is_not_a_source_certificate() {
    let result = count::conditional_count(&q(3, 4), &q(1, 3), &q(1, 4), &q(2, 1)).unwrap();
    assert_eq!(result.delta, q(1, 24));
    assert_eq!(result.bound, q(200, 3));
    assert_eq!(result.ceiling.to_string(), "67");
    let request = b"RC1 COUNT 3/4 1/3 1/4 2/1\n";
    let response = protocol::execute(request);
    assert_eq!(response.exit_code, 2);
    assert_eq!(protocol::check(request, response.bytes.as_bytes()), Err("CONDITIONAL_NOT_SOURCE_CERTIFICATE"));
    for request in ["RC1 COUNT 0/1 1/1 1/1 0/1\n", "RC1 COUNT 1/1 0/1 1/1 0/1\n",
        "RC1 COUNT 1/1 1/1 0/1 0/1\n", "RC1 COUNT 1/1 1/1 1/1 -1/1\n"] {
        assert_eq!(protocol::execute(request.as_bytes()).exit_code, 1);
    }
}

#[test]
fn inherited_exact_forest_coordinate() {
    let f = vec![Tree::Node(Box::new(Tree::Leaf(1)), Box::new(Tree::Leaf(2))), Tree::Leaf(3), Tree::Leaf(4)];
    let coordinate = forest::coordinate(4, &f, &q(1, 2)).unwrap();
    assert_eq!(coordinate.probability, q(7, 192));
    assert_eq!(coordinate.histories.to_string(), "1");
    assert_eq!(forest::coordinate(4, &f, &q(1, 1)), Err("FOREST_SURVIVAL"));
}

#[test]
fn inherited_native_components_remain_available() {
    use parity_solver::{inherited_intervals as i, inherited_poisson as p, inherited_signed_nine as s};
    assert_eq!(i::exp_neg(&q(0, 1), 96).unwrap().lo(), &q(1, 1));
    assert!(matches!(p::certify(&q(1, 1), &q(1, 2), Some(&2u8.into())), Ok(p::Outcome::Certified(_))));
    assert_eq!(s::FEATURES[0], "AC1");
    assert_eq!(canonical(&q(2, 2)), "1/1");
}
