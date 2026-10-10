use parity_solver::{forest::{ordinary_path_coefficients, Tree}, law::{self, Budgets, Decision,
    LimitKind, Mechanism, Request}, natural_cell::{Edge, Hybrid, Source}, polynomial::Polynomial,
    protocol, q};

fn budgets() -> Budgets { Budgets { states: 4096, terms: 65536, histories: 4096 } }
fn three_tip() -> Source { Source { vertices: 5, root: 0,
    edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
        Edge { source: 2, target: 3 }, Edge { source: 2, target: 4 }],
    leaves: vec![3, 4, 1], hybrids: vec![] } }
fn parallel() -> Source { Source { vertices: 5, root: 0,
    edges: vec![Edge { source: 0, target: 1 }, Edge { source: 0, target: 2 },
        Edge { source: 2, target: 3 }, Edge { source: 2, target: 3 }, Edge { source: 3, target: 4 }],
    leaves: vec![1, 4], hybrids: vec![Hybrid { vertex: 3, incoming: [2, 3] }] } }
fn table(request: &Request) -> law::Table { match law::compile(request).unwrap() {
    Decision::Table(t) => t, other => panic!("unexpected {other:?}"),
} }
fn sum_table(table: &law::Table) -> Polynomial {
    table.rooted.values().fold(Polynomial::zero(table.dimension), |sum, (_, p)| sum.add(p).unwrap())
}

#[test]
fn actual_three_taxon_species_tree_closed_form() {
    let request = Request { source: three_tip(), samples: vec![0, 1, 2],
        mechanism: Mechanism::Independent, budgets: budgets() };
    let result = table(&request);
    assert_eq!(result.rooted.len(), 3);
    let x = Polynomial::variable(4, 1).unwrap();
    assert_eq!(result.rooted["((0,1),2)"].1, Polynomial::one(4).subtract(&x.scale(&q(2, 3))).unwrap());
    assert_eq!(result.rooted["((0,2),1)"].1, x.scale(&q(1, 3)));
    assert_eq!(result.rooted["(0,(1,2))"].1, x.scale(&q(1, 3)));
    assert_eq!(result.unrooted["[]"], Polynomial::one(4));
    assert_eq!(sum_table(&result), Polynomial::one(4));
}

#[test]
fn ordinary_kernel_initial_value_and_differential_equation() {
    let path = |k, j| ordinary_path_coefficients(k, j).unwrap().iter().fold(Polynomial::zero(1),
        |sum, (power, coefficient)| sum.add(&Polynomial::monomial(1, 0, *power, coefficient.clone()).unwrap()).unwrap());
    for k in 1..=4 { for j in 1..=k {
        let h = path(k, j);
        assert_eq!(h.evaluate(&[q(1, 1)]).unwrap(), q(i64::from(k == j), 1));
        let derivative = h.terms.iter().fold(Polynomial::zero(1), |sum, (powers, coefficient)|
            sum.add(&Polynomial::monomial(1, 0, powers[0], coefficient * q(-(powers[0] as i64), 1)).unwrap()).unwrap());
        let next = if j < k { path(k, j + 1) } else { Polynomial::zero(1) };
        let rhs = h.scale(&q(-((j * (j - 1) / 2) as i64), 1)).add(&next).unwrap();
        assert_eq!(derivative, rhs);
    } }
}

#[test]
fn copied_current_lineages_and_parallel_occurrences_preserve_joint_routing() {
    let mut request = Request { source: parallel(), samples: vec![1, 1, 0, 0],
        mechanism: Mechanism::Common, budgets: budgets() };
    let common = table(&request);
    request.mechanism = Mechanism::Independent;
    let independent = table(&request);
    assert_eq!(common.rooted.len(), 15);
    assert_eq!(common.unrooted.len(), 3);
    assert_ne!(common, independent);
    assert_eq!(sum_table(&common), Polynomial::one(6));
    assert_eq!(sum_table(&independent), Polynomial::one(6));
    assert!(independent.rooted.values().any(|(_, p)| p.terms.keys().any(|powers| powers[5] == 2)));
    for edge in [2, 3] {
        assert!(independent.rooted.values().any(|(_, p)| p.terms.keys().any(|powers| powers[edge] > 0)));
    }
    let mut values = vec![q(1, 2); 6];
    values[5] = q(1, 3);
    values[4] = q(0, 1); // Already merged before routing: one current lineage.
    for (name, (_, p)) in &common.rooted {
        assert_eq!(p.evaluate(&values).unwrap(), independent.rooted[name].1.evaluate(&values).unwrap());
    }
    values[4] = q(1, 1); // Both copied lineages enter the hybrid separately.
    assert!(common.rooted.iter().any(|(name, (_, p))|
        p.evaluate(&values).unwrap() != independent.rooted[name].1.evaluate(&values).unwrap()));
}

#[test]
fn unsampled_taxa_empty_common_routes_and_conservative_caps() {
    let mut request = Request { source: parallel(), samples: vec![0],
        mechanism: Mechanism::Common, budgets: budgets() };
    let result = table(&request);
    assert_eq!(result.rooted["0"], (Tree::Leaf(0), Polynomial::one(6)));
    assert_eq!(result.unrooted["[]"], Polynomial::one(6));
    request.budgets.states = 1;
    match law::compile(&request).unwrap() {
        Decision::Unknown(limit) => { assert_eq!(limit.kind, LimitKind::State); assert_eq!(limit.vertex, 3); assert_eq!(limit.required.to_string(), "2"); }
        other => panic!("expected state cap, got {other:?}"),
    }
    request.budgets.states = 2;
    request.budgets.terms = 2;
    match law::compile(&request).unwrap() {
        Decision::Unknown(limit) => { assert_eq!(limit.kind, LimitKind::Term); assert_eq!(limit.vertex, 3); assert_eq!(limit.required.to_string(), "3"); }
        other => panic!("expected pre-cancellation term cap, got {other:?}"),
    }
    request.mechanism = Mechanism::Independent;
    assert_eq!(table(&request).rooted["0"].1, Polynomial::one(6));
}

#[test]
fn budgets_prioritize_history_then_state_then_terms() {
    let mut request = Request { source: three_tip(), samples: vec![0, 1, 2],
        mechanism: Mechanism::Independent, budgets: budgets() };
    for (kind, changed) in [(LimitKind::State, Budgets { states: 0, ..budgets() }),
        (LimitKind::Term, Budgets { terms: 0, ..budgets() }),
        (LimitKind::History, Budgets { histories: 0, ..budgets() })] {
        request.budgets = changed;
        match law::compile(&request).unwrap() { Decision::Unknown(l) => assert_eq!(l.kind, kind),
            other => panic!("expected {kind:?}, got {other:?}") }
    }
    request.samples = vec![1, 1, 1, 1];
    request.budgets = Budgets { states: 0, terms: 0, histories: 0 };
    match law::compile(&request).unwrap() { Decision::Unknown(l) => {
        assert_eq!(l.kind, LimitKind::History); assert_eq!(l.vertex, 4); assert_eq!(l.required.to_string(), "6");
    }, other => panic!("expected history before other caps, got {other:?}") }
}

#[test]
fn law_wire_canonical_echo_gate_and_native_replay() {
    let raw = b"RC1 LAW 5 4 3 0 3 4096 65536 4096\nMECHANISM INDEPENDENT\nROOT 0\nEDGE 0 0 1\nEDGE 1 0 2\nEDGE 2 2 3\nEDGE 3 2 4\nLEAF 0 3\nLEAF 1 4\nLEAF 2 1\nSAMPLE 0 0\nSAMPLE 1 1\nSAMPLE 2 2\n";
    let response = protocol::execute(raw);
    assert_eq!(response.exit_code, 0);
    assert!(response.bytes.contains("GATE SOURCE_ADMISSION_NOT_ESTABLISHED\nSTATUS TABLE\nROOTED 3\n"));
    protocol::check(raw, response.bytes.as_bytes()).unwrap();
    let forged = response.bytes.replace("TERM -2/3", "TERM -1/3");
    assert_ne!(forged, response.bytes);
    assert!(protocol::check(raw, forged.as_bytes()).is_err());
    let other = String::from_utf8(raw.to_vec()).unwrap().replace("MECHANISM INDEPENDENT", "MECHANISM COMMON");
    assert!(protocol::check(other.as_bytes(), response.bytes.as_bytes()).is_err());
    for malformed in [other.replace("SAMPLE 1 1", "SAMPLE 0 1"),
        other.replace("MECHANISM COMMON", "MECHANISM JOINT"),
        other.replace("SAMPLE 2 2", "SAMPLE 2 3"),
        other.replace(" 3 4096 65536 4096", " 3 4096 65537 4096")] {
        let refusal = protocol::execute(malformed.as_bytes());
        assert_eq!(refusal.bytes, protocol::INVALID); assert_eq!(refusal.exit_code, 1);
    }
    let limited = String::from_utf8(raw.to_vec()).unwrap().replace(" 3 4096 65536 4096", " 3 0 65536 4096");
    let unknown = protocol::execute(limited.as_bytes());
    assert_eq!(unknown.exit_code, 2);
    assert!(unknown.bytes.contains("STATUS UNKNOWN\nLIMIT STATE 4 1 0\nEND\n"));
    assert!(!unknown.bytes.contains("ROOTED"));
    assert!(protocol::check(limited.as_bytes(), unknown.bytes.as_bytes()).is_err());
}
