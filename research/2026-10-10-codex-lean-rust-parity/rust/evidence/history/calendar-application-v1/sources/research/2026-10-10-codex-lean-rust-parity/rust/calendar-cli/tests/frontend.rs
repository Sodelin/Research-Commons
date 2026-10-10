//! New general-input parsing/framing controls; the exact source kernels are reused.
use calendar_cli::{request::{parse_request, MAX_REQUEST_BYTES}, response::{canonical_json, ErrorKind, Frame, MAX_RESULT_BYTES}, solve};
use serde_json::{json, Value};
use std::{fs, io::Write, process::{Command, Stdio}};

const REQUEST: &[u8] = include_bytes!("../../../design/evidence/calendar-fixture-freeze-1/twoTipCalendar.request.json");
fn input() -> Value { serde_json::from_slice(REQUEST).unwrap() }
fn frame(value: Value) -> Frame { solve(&serde_json::to_vec(&value).unwrap()) }
fn check(value: &Frame, status: &str, code: u8) {
    assert_eq!(value.exit_code,code);
    assert_eq!(value.value["status"],status);
    assert_eq!(canonical_json(&serde_json::from_slice::<Value>(&value.bytes()).unwrap()),value.bytes());
    assert!(value.bytes().is_ascii());
}

#[test]
fn negative_zero_is_exact_integer_zero() {
    let raw = serde_json::to_string(&input()).unwrap().replace("\"root\":0","\"root\":-0");
    let parsed = parse_request(raw.as_bytes()).unwrap();
    assert_eq!(parsed.context.root.0,0);
    let result = solve(raw.as_bytes());
    check(&result,"TABLE",0);
    assert_eq!(result.value["request"]["context"]["root"],0);
}
#[test]
fn count_booleans_floats_exponents_and_overflow_refuse() {
    let original = serde_json::to_string(&input()).unwrap();
    for token in ["true","false","0.0","0e0","-1","18446744073709551616","\"0\""] {
        let raw = original.replace("\"root\":0",&format!("\"root\":{token}"));
        let result = solve(raw.as_bytes());
        check(&result,"ERROR",1);
        assert_eq!(result.value["error"],"INVALID_REQUEST", "{token}");
    }
}
#[test]
fn maximal_natural_graph_counts_refuse_before_allocation_and_labels_are_metadata() {
    for key in ["vertices", "root"] {
        let mut value = input(); value["context"][key] = json!(u64::MAX);
        let result = frame(value); check(&result,"ERROR",1);
        assert_eq!(result.value["error"],"INVALID_REQUEST");
    }
    let mut value = input(); value["context"]["global_labels"][0] = json!(u64::MAX);
    let result = frame(value); check(&result,"TABLE",0);
    assert_eq!(result.value["request"]["context"]["global_labels"][0],u64::MAX);
}
#[test]
fn duplicate_and_unknown_keys_refuse_at_every_struct_level() {
    let original = serde_json::to_string(&input()).unwrap();
    let duplicate = format!("{{\"ages\":[],{}",&original[1..]);
    assert!(parse_request(duplicate.as_bytes()).is_err());
    let duplicate = original.replace("\"root\":0","\"root\":0,\"root\":0");
    assert!(parse_request(duplicate.as_bytes()).is_err());
    for path in ["outer","context","compiler","word","epoch","boundary","completion"] {
        let mut value = input();
        let target = match path {
            "outer"=>&mut value,"context"=>&mut value["context"],
            "compiler"=>&mut value["compiler_limits"],"word"=>&mut value["word_limits"],
            key=>&mut value["provider_limits"][key],
        };
        target["extra"] = json!(0);
        check(&frame(value),"ERROR",1);
    }
}
#[test]
fn graph_tuple_arity_and_mechanism_types_refuse() {
    for replacement in [json!([0]),json!([0,1,2]),json!([true,1]),json!([0.0,1])] {
        let mut value = input(); value["context"]["edges"][0] = replacement;
        check(&frame(value),"ERROR",1);
    }
    let mut value = input(); value["common"] = json!([1]);
    check(&frame(value),"ERROR",1);
}
#[test]
fn exact_rationals_have_no_additional_bit_cap_and_zero_denominator_never_panics() {
    for token in ["1/0","0/2","-0/1","01/1","+1/1","1/-2","1//1","1/01"] {
        let mut value = input();value["ages"][0]=json!(token);
        let result=frame(value);check(&result,"ERROR",1);
        assert_eq!(result.value["error"],"INVALID_REQUEST");
    }
    let mut value=input();value["ages"][0]=json!(format!("1{}/1","0".repeat(100)));
    check(&frame(value),"TABLE",0);
}
#[test]
fn malformed_utf8_and_oversized_requests_are_invalid_inputs() {
    check(&solve(b"\xff"),"ERROR",1);
    let value=solve(&vec![b' ';MAX_REQUEST_BYTES+1]);
    check(&value,"ERROR",1);assert_eq!(value.value["error"],"INVALID_REQUEST");
}
#[test]
fn validation_precedes_compiler_and_word_caps() {
    let mut value=input();value["inverse_rates"][0]=json!("0/1");
    value["compiler_limits"]=json!({"word_length":0,"slots":0,"variables":0});
    let result=frame(value);check(&result,"ERROR",1);
    assert_eq!(result.value["error"],"INVALID_REQUEST");
}
#[test]
fn compiler_and_provider_unknowns_have_no_partial_rows() {
    let mut value=input();value["compiler_limits"]["word_length"]=json!(0);
    let result=frame(value);check(&result,"UNKNOWN",2);
    assert_eq!(result.value["unknown_scope"],"COMPILER");
    assert!(result.value.get("agenda").is_none());
    assert!(result.value.get("word_result").is_none());
    let mut value=input();value["provider_limits"]["completion"]["calls"]=json!(0);
    let result=frame(value);check(&result,"UNKNOWN",2);
    assert_eq!(result.value["consumer_population"],json!(["A",0]));
    assert!(result.value["word_result"].get("rows").is_none());
    assert!(result.value["word_result"].get("work").is_none());
}
#[test]
fn result_output_cap_reports_execution_failure_without_partial_table() {
    let oversized=Frame {value:json!({"rows":"x".repeat(MAX_RESULT_BYTES)}),exit_code:0,diagnostic:None}.bounded();
    check(&oversized,"ERROR",1);
    assert_eq!(oversized.value,Frame::error(ErrorKind::ExecutionFailure,"ignored").value);
}
#[test]
fn file_stdin_and_bounded_replay_entrypoints_agree() {
    let binary=env!("CARGO_BIN_EXE_calendar-solver");
    let temp=std::env::temp_dir().join(format!("calendar-cli-control-{}",std::process::id()));
    fs::create_dir(&temp).unwrap();
    let request=temp.join("REQUEST.json");fs::write(&request,REQUEST).unwrap();
    let certificate=temp.join("TABLE.json");
    let file=Command::new(binary).args(["solve","--request"]).arg(&request).output().unwrap();
    assert_eq!(file.status.code(),Some(0));
    fs::write(&certificate,&file.stdout).unwrap();
    let mut child=Command::new(binary).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    child.stdin.take().unwrap().write_all(REQUEST).unwrap();
    let stdin=child.wait_with_output().unwrap();assert_eq!(file.stdout,stdin.stdout);
    let checked=Command::new(binary).arg("check").arg("--request").arg(&request)
        .arg("--certificate").arg(&certificate).output().unwrap();
    assert_eq!(checked.status.code(),Some(0));
    assert_eq!(checked.stdout,b"{\"schema\":\"source_calendar_check_v1\",\"status\":\"ACCEPT\"}\n");
    let mut altered:Value=serde_json::from_slice(&file.stdout).unwrap();
    altered["word_result"]["work"]["queries"]=json!(0);
    fs::write(&certificate,canonical_json(&altered)).unwrap();
    let checked=Command::new(binary).arg("check").arg("--request").arg(&request)
        .arg("--certificate").arg(&certificate).output().unwrap();
    assert_eq!(checked.status.code(),Some(1));
    assert_eq!(checked.stdout,b"{\"schema\":\"source_calendar_check_v1\",\"status\":\"REJECT\"}\n");
    fs::remove_dir_all(temp).unwrap();
}
