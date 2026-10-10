use rational_compression::{check, encode, solve, Frame};
use serde_json::{json, Value};

fn request(m: usize, atoms: &[(&str, &str)]) -> Value {
    json!({"schema":"g6_rational_compression_request_v1","M":m,
        "atoms":atoms.iter().map(|(z,alpha)| json!({"z":z,"alpha":alpha})).collect::<Vec<_>>(),
        "limits":{"atoms":64,"matrix_cells":8192,"rational_bits":4096}})
}
fn wire(v: &Value) -> Vec<u8> { encode(v).unwrap() }
fn produce(v: &Value) -> (Vec<u8>, Frame, Value) {
    let raw = wire(v);
    let result = solve(&raw);
    let frame: Value = serde_json::from_slice(&encode(&result).unwrap()).unwrap();
    (raw, result, frame)
}
fn accepted(v: &Value) -> Value {
    let (raw, result, frame) = produce(v);
    assert_eq!(result.exit_code(), 0, "{frame}");
    let checked = check(&raw, &encode(&result).unwrap());
    assert_eq!(checked.status, "ACCEPT");
    assert!(checked.certificate_valid);
    assert!(!checked.producer_work_verified && !checked.resource_exhaustion_verified);
    frame
}
fn rejected(raw: &[u8], frame: Value) {
    let result = check(raw, &wire(&frame));
    assert_eq!(result.status, "REJECT");
    assert!(!result.certificate_valid);
}

#[test]
fn zero_weights_and_duplicate_values_keep_original_indices() {
    for atoms in [vec![], vec![("1/3","0/1"),("2/3","0/1")]] {
        let mut v = request(4, &atoms);
        // No geometry is generated for an all-zero family, even under 2 bits.
        v["limits"]["rational_bits"] = json!(2);
        let frame = accepted(&v);
        assert_eq!(frame["output_atoms"], json!([]));
        assert_eq!(frame["mass"], "0/1");
        assert_eq!(frame["tail_moments"], json!([{"level":3,"moment":"0/1"},{"level":4,"moment":"0/1"}]));
        assert_eq!(frame["work"], json!({"elimination_steps":0,"matrix_cells":0}));
    }
    let v = request(2, &[("1/3","0/1"),("1/2","2/1"),("1/2","3/1"),("2/3","0/1")]);
    let frame = accepted(&v);
    assert_eq!(frame["output_atoms"], json!([{"input_index":1,"beta":"5/1"}]));
    assert_eq!(frame["mass"], "5/1");
}

#[test]
fn inherited_exact_m3_certificate() {
    let v = request(3, &[("1/8","2/3"),("1/4","3/4"),("3/8","4/5"),("1/2","5/6"),
        ("5/8","6/7"),("3/4","7/8"),("7/8","8/9")]);
    let frame = accepted(&v);
    assert_eq!(frame["output_atoms"], json!([{"input_index":2,"beta":"21121/11520"},
        {"input_index":4,"beta":"6877/1792"}]));
    assert_eq!(frame["mass"], "14291/2520");
    assert_eq!(frame["work"], json!({"elimination_steps":5,"matrix_cells":50}));
}

#[test]
fn domain_is_checked_before_count_and_bit_budgets() {
    let mut v = request(4, &[("1/2","1/1"),("1/1","0/1")]);
    v["limits"] = json!({"atoms":0,"matrix_cells":0,"rational_bits":0});
    assert_eq!(solve(&wire(&v)).error.as_deref(), Some("INVALID_REQUEST"));
    v["atoms"][1]["z"] = json!("2/4");
    assert_eq!(solve(&wire(&v)).error.as_deref(), Some("INVALID_REQUEST"));
}

#[test]
fn duplicate_unknown_float_and_bool_fields_are_refused() {
    let v = request(2, &[("1/2","1/1")]);
    let raw = String::from_utf8(wire(&v)).unwrap();
    let variants = [raw.replacen("\"M\":2", "\"M\":2,\"M\":2", 1),
        raw.replacen("\"M\":2", "\"M\":2.0", 1),
        raw.replacen("\"M\":2", "\"M\":true", 1),
        raw.replacen("\"M\":2", "\"M\":2,\"extra\":0", 1),
        raw.replacen("\"z\":\"1/2\"", "\"z\":\"1/2\",\"z\":\"1/2\"", 1)];
    for bytes in variants { assert_eq!(solve(bytes.as_bytes()).error.as_deref(), Some("INVALID_REQUEST")); }
    let mut empty = request(2, &[]);
    empty["limits"]["atoms"] = json!(0);
    let minus_zero = String::from_utf8(wire(&empty)).unwrap().replacen("\"atoms\":0", "\"atoms\":-0", 1);
    assert_eq!(solve(minus_zero.as_bytes()).status, "COMPRESSED");
}

#[test]
fn exact_and_one_below_matrix_and_atom_limits() {
    let mut v = request(2, &[("1/3","1/1"),("2/3","1/1")]);
    v["limits"]["atoms"] = json!(2);
    v["limits"]["matrix_cells"] = json!(2);
    accepted(&v);
    v["limits"]["matrix_cells"] = json!(1);
    let (raw, result, frame) = produce(&v);
    assert_eq!(frame["limit"], json!({"stage":"MOMENTS","kind":"matrix_cells","required":2,"cap":1}));
    assert_eq!(frame["work"]["matrix_cells"], 0);
    assert_eq!(result.exit_code(), 2);
    let checked = check(&raw, &encode(&result).unwrap());
    assert_eq!(checked.status, "ACCEPT");
    assert!(!checked.certificate_valid && !checked.resource_exhaustion_verified);
    v["limits"]["atoms"] = json!(1);
    let (_, _, frame) = produce(&v);
    assert_eq!(frame["limit"]["kind"], "atoms");
    assert_eq!(frame["work"], json!({"elimination_steps":0,"matrix_cells":0}));
}

#[test]
fn bit_limits_cover_input_geometry_rref_update_and_certificate() {
    let cases = [
        (2, vec![("1/2","1/1")], 1, "INPUT"),
        (4, vec![("1/2","1/1");4], 2, "MOMENTS"),
        (3, vec![("1/3","1/1"),("1/2","1/1"),("2/3","1/1")], 5, "RREF"),
        (2, vec![("1/2","1/1");4], 2, "UPDATE"),
        (4, vec![("1/2","1/1")], 2, "CERTIFICATE"),
    ];
    for (m, atoms, cap, stage) in cases {
        let mut v = request(m, &atoms);
        v["limits"]["rational_bits"] = json!(cap);
        let (raw, result, frame) = produce(&v);
        assert_eq!(frame["status"], "UNKNOWN", "{frame}");
        assert_eq!(frame["limit"]["stage"], stage, "{frame}");
        assert_eq!(frame["limit"]["kind"], "rational_bits");
        assert!(frame["limit"]["required"].as_u64().unwrap() > cap);
        assert!(frame.get("output_atoms").is_none());
        assert_eq!(check(&raw, &encode(&result).unwrap()).status, "ACCEPT");
    }
    // With an insufficient matrix budget no moment geometry is attempted.
    let mut v = request(4, &[("1/2","1/1");4]);
    v["limits"]["rational_bits"] = json!(2);
    v["limits"]["matrix_cells"] = json!(0);
    let (_, _, frame) = produce(&v);
    assert_eq!(frame["limit"]["kind"], "matrix_cells");
    assert_eq!(frame["work"]["matrix_cells"], 0);
}

#[test]
fn checker_rejects_balanced_wrong_moment_and_bad_indices() {
    let v = request(3, &[("1/3","1/1"),("2/3","1/1")]);
    let (raw, _, frame) = produce(&v);
    let mut forged = frame.clone();
    forged["output_atoms"][0]["beta"] = json!("3/2");
    forged["output_atoms"][1]["beta"] = json!("1/2");
    rejected(&raw, forged); // Same mass, different geometric tail moment.
    for index in [0, 2] {
        let mut forged = frame.clone();
        forged["output_atoms"][1]["input_index"] = json!(index);
        rejected(&raw, forged);
    }
    for beta in ["0/1", "-1/1"] {
        let mut forged = frame.clone();
        forged["output_atoms"][0]["beta"] = json!(beta);
        rejected(&raw, forged);
    }
    let mut foreign = raw.clone(); foreign.push(b' ');
    rejected(&foreign, frame);
}

#[test]
fn exact_variant_fields_and_all_input_bit_requirements() {
    let v = request(2, &[("1/3","1/1")]);
    let (raw, _, frame) = produce(&v);
    for field in ["limit", "error"] {
        let mut extra = frame.clone(); extra[field] = Value::Null;
        rejected(&raw, extra);
    }
    let mut huge_beta = frame.clone();
    huge_beta["output_atoms"][0]["beta"] = json!(format!("{}/1", "1".repeat(5000)));
    rejected(&raw, huge_beta); // Explicit bit cap is enforced before gcd normalization.
    let mut low = v.clone(); low["limits"]["rational_bits"] = json!(1);
    let raw_low = wire(&low);
    let mut forged = frame;
    forged["request"] = low;
    forged["request_raw"] = json!(String::from_utf8(raw_low.clone()).unwrap());
    rejected(&raw_low, forged); // M2 mass alone does not touch z: check z explicitly.
    let (_, result, frame) = produce(&request(2, &[("1/2","1/1")]));
    let mut unknown_v = request(2, &[("1/2","1/1")]);
    unknown_v["limits"]["atoms"] = json!(0);
    let (raw_unknown, _, mut unknown) = produce(&unknown_v);
    unknown["output_atoms"] = Value::Null;
    rejected(&raw_unknown, unknown);
    assert_eq!(result.exit_code(), 0);
    assert_eq!(frame["source_admission_verified"], false);
}

#[test]
fn checker_accepts_alternative_certificate_without_work_claim() {
    let v = request(2, &[("1/3","1/1"),("2/3","1/1")]);
    let (raw, _, mut frame) = produce(&v);
    frame["output_atoms"] = json!([{"input_index":1,"beta":"2/1"}]);
    frame["work"] = json!({"elimination_steps":0,"matrix_cells":0});
    let result = check(&raw, &wire(&frame));
    assert_eq!(result.status, "ACCEPT");
    assert!(result.certificate_valid);
    assert!(!result.producer_work_verified && !result.resource_exhaustion_verified);
}
